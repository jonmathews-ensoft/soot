/* Soot - a J*va Optimization Framework
 * Copyright (C) 1997-2014 Raja Vallee-Rai and others
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */
package soot;

import soot.jimple.*;
import soot.coffi.Util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public final class LambdaMetaFactory {
    public static SootMethodRef makeLambdaHelper(
                        List<? extends Value> bootstrapArgs,
                        int tag,
                        String name,
                        Type[] types) {
        if(bootstrapArgs.size() != 3 || 
           !(bootstrapArgs.get(0) instanceof ClassConstant) ||
           !(bootstrapArgs.get(1) instanceof MethodHandle) ||
           !(bootstrapArgs.get(2) instanceof ClassConstant)) {
            G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactor.metaFactory");
            return null;
        }
        String samMethodType = ((ClassConstant) bootstrapArgs.get(0)).getValue();
        SootMethodRef implMethod = ((MethodHandle) bootstrapArgs.get(1)).getMethodRef();
        String instantiatedMethodType = ((ClassConstant) bootstrapArgs.get(2)).getValue();
        if(!samMethodType.equals(instantiatedMethodType)) {
            G.v().out.println("warning: LambdaMetaFactory: " + 
                              samMethodType + " != " + instantiatedMethodType);
            return null;
        }
        
        Type[] samTypes = Util.v().jimpleTypesOfFieldOrMethodDescriptor(samMethodType);
        List<Type> paramTypes = Arrays.asList(samTypes).subList(0, samTypes.length - 1);
        Type retType = samTypes[samTypes.length - 1];
        
        List<Type> capTypes = Arrays.asList(types).subList(0, types.length - 1);
        if(!(types[types.length-1] instanceof RefType)) {
            G.v().out.println("unexpected interface type: " + types[types.length-1]);
            return null;
        }
        SootClass iface = ((RefType) types[types.length-1]).getSootClass();
        
        // Our thunk class implements the functional interface
        String className = "soot.dummy." + implMethod.name() + "$" + uniqSupply();
        SootClass tclass = new SootClass(className);
        tclass.addInterface(iface);
        
        // It contains fields for all the captures in the lambda
        List<SootField> capFields = new ArrayList<SootField>(capTypes.size());
        for(int i=0;i<capTypes.size();i++) {
            SootField f = new SootField(
                "cap" + i,
                capTypes.get(i),
                0);
            capFields.add(f);
            tclass.addField(f);
        }
        
        MethodSource ms = new ThunkMethodSource(capFields, paramTypes, retType, implMethod);
        
        // Bootstrap method creates a new instance of this class
        SootMethod tboot = new SootMethod(
            "bootstrap$",
            capTypes,
            iface.getType(),
            Modifier.STATIC
        );
        tclass.addMethod(tboot);
        tboot.setSource(ms);
        
        // Constructor just copies the captures
        SootMethod tctor = new SootMethod(
            "<init>",
            capTypes,
            VoidType.v());
        tclass.addMethod(tctor);
        tctor.setSource(ms);
        
        // Dispatch runs the 'real' method implementing the body of the lambda
        SootMethod tdispatch = new SootMethod(
            name,
            paramTypes,
            retType);
        tclass.addMethod(tdispatch);
        tdispatch.setSource(ms);
        
        Scene.v().addClass(tclass);
        tclass.setApplicationClass(); // FIXME: should be inferred from Soot settings; failing to set correctly prevents serialization to Jimple text format
            
        // System.out.println(tboot);
        
        /*java.io.PrintWriter pw = new java.io.PrintWriter(System.out);
        Printer.v().printTo(tclass, pw);
        pw.close();*/
        
        return tboot.makeRef();
    }
    
    private static class ThunkMethodSource implements MethodSource {
        private List<SootField> capFields;
        private List<Type> paramTypes;
        private Type retType;
        private SootMethodRef implMethod;
        
        public ThunkMethodSource(List<SootField> capFields, List<Type> paramTypes, Type retType, SootMethodRef implMethod) {
            this.capFields = capFields;
            this.paramTypes = paramTypes;
            this.retType = retType;
            this.implMethod = implMethod;
        }

        public Body getBody(SootMethod m, String phaseName) {
            if(!phaseName.equals("jb"))
                throw new Error("unsupported body type: " + phaseName); // FIXME?

            SootClass tclass = m.getDeclaringClass();
            JimpleBody jb = Jimple.v().newBody(m);
            PatchingChain<Unit> us = jb.getUnits();

            if(m.getName().equals("<init>")) {
                Local l = Jimple.v().newLocal("r", tclass.getType());
                jb.getLocals().add(l);
                us.add(Jimple.v().newIdentityStmt(
                    l,
                    Jimple.v().newThisRef(tclass.getType())
                ));
                us.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(
                        l,
                        Scene.v().makeConstructorRef(
                            Scene.v().getObjectType().getSootClass(), Collections.<Type>emptyList()
                        ),
                        Collections.<Value>emptyList())
                ));
                for(SootField f : capFields) {
                    int i = us.size() - 2;
                    Local l2 = Jimple.v().newLocal("c" + i, f.getType()); // FIXME: non-standard prefix, should be based on type; fix cases below as well
                    jb.getLocals().add(l2);
                    us.add(Jimple.v().newIdentityStmt(
                        l2,
                        Jimple.v().newParameterRef(f.getType(), i)
                    ));
                    us.add(Jimple.v().newAssignStmt(
                        Jimple.v().newInstanceFieldRef(l, f.makeRef()),
                        l2
                    ));
                }
                us.add(Jimple.v().newReturnVoidStmt());
            } else if(m.getName().equals("bootstrap$")) {
                Local l = Jimple.v().newLocal("r", tclass.getType());
                jb.getLocals().add(l);
                Value val = Jimple.v().newNewExpr(tclass.getType());
                List<Value> capVals = new ArrayList<Value>();
                us.add(Jimple.v().newAssignStmt(l, val));
                us.add(Jimple.v().newInvokeStmt(
                    Jimple.v().newSpecialInvokeExpr(
                        l,
                        Scene.v().makeConstructorRef(tclass, Collections.<Type>emptyList()),
                        Collections.<Value>emptyList())
                ));
                us.add(Jimple.v().newReturnStmt(l));
            } else {
                Local this_ = Jimple.v().newLocal("r", tclass.getType());
                jb.getLocals().add(this_);
                us.add(Jimple.v().newIdentityStmt(
                    this_,
                    Jimple.v().newThisRef(tclass.getType())
                ));

                List<Local> args = new ArrayList<Local>();
                
                for(SootField f : capFields) {
                    int i = args.size();
                    Local l = Jimple.v().newLocal("c" + i, f.getType());
                    jb.getLocals().add(l);
                    us.add(Jimple.v().newAssignStmt(
                        l, 
                        Jimple.v().newInstanceFieldRef(this_, f.makeRef())
                    ));
                    args.add(l);
                }

                for(Type ty : paramTypes) {
                    int i = args.size();
                    Local l = Jimple.v().newLocal("a" + i, ty);
                    jb.getLocals().add(l);
                    us.add(Jimple.v().newIdentityStmt(
                        l,
                        Jimple.v().newParameterRef(ty, i)
                    ));
                    args.add(l);
                }
                
                Local ret = Jimple.v().newLocal("r", retType);
                jb.getLocals().add(ret);
                us.add(Jimple.v().newAssignStmt(
                    ret,
                    Jimple.v().newStaticInvokeExpr(implMethod, args)
                ));
                us.add(Jimple.v().newReturnStmt(ret));
            }
            return jb;
        }
    }
    
    // FIXME: Move to 'G'?
    private static int uniq;
    private static synchronized long uniqSupply() {
        return ++uniq;
    }
}
