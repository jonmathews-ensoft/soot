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
import soot.jimple.toolkits.scalar.LocalNameStandardizer;
import soot.util.Chain;
import soot.util.HashChain;
import soot.coffi.Util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

public final class LambdaMetaFactory {
    public static SootMethodRef makeLambdaHelper(
                        List<? extends Value> bootstrapArgs,
                        int tag,
                        String name,
                        Type[] types, String enclosingClassname) {
        if(bootstrapArgs.size() < 3 || 
           !(bootstrapArgs.get(0) instanceof ClassConstant) ||
           !(bootstrapArgs.get(1) instanceof MethodHandle) ||
           !(bootstrapArgs.get(2) instanceof ClassConstant) ||
           (bootstrapArgs.size() > 3 && !(bootstrapArgs.get(3) instanceof IntConstant))) {
            G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.metaFactory");
            return null;
        }
        String samMethodType = ((ClassConstant) bootstrapArgs.get(0)).getValue();
        SootMethodRef implMethod = ((MethodHandle) bootstrapArgs.get(1)).getMethodRef();
        String instantiatedMethodType = ((ClassConstant) bootstrapArgs.get(2)).getValue();
        if(!samMethodType.equals(instantiatedMethodType)) {
            G.v().out.println("warning: LambdaMetaFactory: " + 
                              samMethodType + " != " + instantiatedMethodType);
            // FIXME: this happens for method references to constructors, must be handled
//            return null;
        }
        int flags = 0;
        if(bootstrapArgs.size() > 3)
            flags = ((IntConstant) bootstrapArgs.get(3)).value;
        boolean serializable = (flags & 1 /* FLAGS_SERIALIZABLE */) != 0;
        List<ClassConstant> markerInterfaces = new ArrayList<ClassConstant>();
        List<ClassConstant> bridges = new ArrayList<ClassConstant>();
        int va = 4;
        if((flags & 2 /* FLAG_MARKERS */) != 0) {
            if(va == bootstrapArgs.size() || !(bootstrapArgs.get(va) instanceof IntConstant)) {
                G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                return null;
            }
            int count = ((IntConstant) bootstrapArgs.get(va++)).value;
            for(int i=0;i<count;i++) {
                if(va >= bootstrapArgs.size()) {
                    G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                    return null;
                }
                Value v = bootstrapArgs.get(va++);
                if(!(v instanceof ClassConstant)) {
                    G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                    return null;
                }
                markerInterfaces.add((ClassConstant)v);
            }
        }
        if((flags & 4 /* FLAG_BRIDGES */) != 0) {
            if(va == bootstrapArgs.size() || !(bootstrapArgs.get(va) instanceof IntConstant)) {
                G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                return null;
            }
            int count = ((IntConstant) bootstrapArgs.get(va++)).value;
            for(int i=0;i<count;i++) {
                if(va >= bootstrapArgs.size()) {
                    G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                    return null;
                }
                Value v = bootstrapArgs.get(va++);
                if(!(v instanceof ClassConstant)) {
                    G.v().out.println("warning: LambdaMetaFactory: unexpected arguments for LambdaMetaFactory.altMetaFactory");
                    return null;
                }
                bridges.add((ClassConstant)v);
            }
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
        if (enclosingClassname == null || enclosingClassname.equals("")) //$NON-NLS-1$
        		enclosingClassname = "soot.dummy."; //$NON-NLS-1$
        else
        		enclosingClassname = enclosingClassname + "$"; //$NON-NLS-1$
        
        // class names cannot contain <>  
        String dummyName = "<init>".equals(implMethod.name()) ? "init" : implMethod.name(); //$NON-NLS-1$//$NON-NLS-2$
        // FIXME: $ causes confusion in inner class inference; remove for now
        dummyName = dummyName.replaceAll("\\$", "_");  //$NON-NLS-1$//$NON-NLS-2$
        String className = enclosingClassname + dummyName + "__" + uniqSupply();  //$NON-NLS-1$//$NON-NLS-2$
        SootClass tclass = new SootClass(className);
        tclass.addInterface(iface);
        tclass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));

		// additions from altMetafactory
        if(serializable)
            tclass.addInterface(RefType.v("java.io.Serializable").getSootClass());
        for(int i=0;i<markerInterfaces.size();i++)
            tclass.addInterface(RefType.v(markerInterfaces.get(i).getValue()).getSootClass());

        
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

            if(m.getName().equals("<init>")) {
                getInitBody(tclass, jb);
            } else if(m.getName().equals("bootstrap$")) {
                getBootstrapBody(tclass, jb);
            } else {
                getInvokeBody(tclass, jb);
            }
            
            // rename locals consistent with JimpleBodyPack
            LocalNameStandardizer.v().transform(jb);
            return jb;
        }

        /**
         * Thunk class init (constructor)
         * @param tclass thunk class
         * @param jb
         */
		private void getInitBody(SootClass tclass, JimpleBody jb) {
            PatchingChain<Unit> us = jb.getUnits();

			// @this
			Local l = Jimple.v().newLocal("r", tclass.getType());
			jb.getLocals().add(l);
			us.add(Jimple.v().newIdentityStmt(
			    l,
			    Jimple.v().newThisRef(tclass.getType())
			));
			
			// @parameters
			Chain<Local> capLocals = new HashChain<>();
			int i=0;
			for(SootField f : capFields) {
				Local l2 = Jimple.v().newLocal("c" + i, f.getType());
				jb.getLocals().add(l2);
				us.add(Jimple.v().newIdentityStmt(
						l2,
						Jimple.v().newParameterRef(f.getType(), i)
						));
				capLocals.add(l2);
				i++;
			}
			
			// super   java.lang.Object.<init>
			us.add(Jimple.v().newInvokeStmt(
			    Jimple.v().newSpecialInvokeExpr(
			        l,
			        Scene.v().makeConstructorRef(
			            Scene.v().getObjectType().getSootClass(), Collections.<Type>emptyList()
			        ),
			        Collections.<Value>emptyList())
			));
			
			// assign parameters to fields 
			Iterator<Local> localItr = capLocals.iterator();
			for(SootField f : capFields) {
				Local l2 = localItr.next();
				us.add(Jimple.v().newAssignStmt(
						Jimple.v().newInstanceFieldRef(l, f.makeRef()),
						l2
						));
			}
			
			us.add(Jimple.v().newReturnVoidStmt());
		}

		private void getBootstrapBody(SootClass tclass, JimpleBody jb) {
            PatchingChain<Unit> us = jb.getUnits();
			List<Value> capValues = new ArrayList<Value>();
			List<Type> capTypes = new ArrayList<Type>();
			int i=0;
			for (SootField capField : capFields) {
					Type type = capField.getType();
					capTypes.add(type);
					Local p = Jimple.v().newLocal("p", type);
					jb.getLocals().add(p);
					ParameterRef pref = Jimple.v().newParameterRef(type,i);
					us.add(Jimple.v().newIdentityStmt(p, pref));
				capValues.add(p);
				i++;
			}
			Local l = Jimple.v().newLocal("r", tclass.getType());
			jb.getLocals().add(l);
			Value val = Jimple.v().newNewExpr(tclass.getType());
			us.add(Jimple.v().newAssignStmt(l, val));
			us.add(Jimple.v().newInvokeStmt(
			    Jimple.v().newSpecialInvokeExpr(
			        l,
			        Scene.v().makeConstructorRef(tclass, capTypes),
			        capValues)
			));
			us.add(Jimple.v().newReturnStmt(l));
		}

		private void getInvokeBody(SootClass tclass, JimpleBody jb) {
            PatchingChain<Unit> us = jb.getUnits();

			// @this
			Local this_ = Jimple.v().newLocal("r", tclass.getType());
			jb.getLocals().add(this_);
			us.add(Jimple.v().newIdentityStmt(
			    this_,
			    Jimple.v().newThisRef(tclass.getType())
			));
			
			// @parameter for direct arguments
			Chain<Local> paramLocals = new HashChain<>();
			int j = 0;
			for(Type ty : paramTypes) {
			    Local l = Jimple.v().newLocal("a" + j, ty);
			    jb.getLocals().add(l);
			    us.add(Jimple.v().newIdentityStmt(
			        l,
			        Jimple.v().newParameterRef(ty, j)
			    ));
			    paramLocals.add(l);
			    j++;
			}

			List<Local> args = new ArrayList<Local>();
			
			// captured arguments
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

			// direct arguments
			for (Local l : paramLocals)
				args.add(l);
			
			invokeImplMethod(jb, us, args);
		}

		private void invokeImplMethod(JimpleBody jb, PatchingChain<Unit> us, List<Local> args) {
			Value value = _invokeImplMethod(jb, us, args);
			
			if (value instanceof InvokeExpr && soot.VoidType.v().equals(implMethod.returnType())) {
				// implementation method is void
				us.add(Jimple.v().newInvokeStmt(value));
				us.add(Jimple.v().newReturnVoidStmt());
			} else if (soot.VoidType.v().equals(retType)) {
				// dispatch method is void
				us.add(Jimple.v().newInvokeStmt(value));
				us.add(Jimple.v().newReturnVoidStmt());
			} else {
				// neither is void, must pass through return value
				Local ret = Jimple.v().newLocal("r", retType);
				jb.getLocals().add(ret);
				us.add(Jimple.v().newAssignStmt(
						ret,
						value
						));
				us.add(Jimple.v().newReturnStmt(ret));
			}
		}

		private Value _invokeImplMethod(JimpleBody jb, PatchingChain<Unit> us, List<Local> args) {
			// A lambda capturing 'this' may be implemented by a private instance method.
	        // A method reference to an instance method may be implemented by the instance method itself.
	        // To use the correct invocation style, resolve the method and determine how the compiler
	        // implemented the lambda or method reference.
	        // NOTE: the SootMethodRef is set to static, and has to be ignored for this purpose.
			
	        SootClass implClass = implMethod.declaringClass();
			SootMethod method = implClass.getMethodUnsafe(implMethod.name(), implMethod.parameterTypes(), implMethod.returnType());
			if (method == null) {
				// resolve failed, fall back to static invocation
	            G.v().out.println("warning: LambdaMetaFactory: unable to resolve target method, invocation may be incorrect; method: " + implMethod.getSignature());
				return Jimple.v().newStaticInvokeExpr(implMethod, args);
			}
			if (method.isStatic()) {
				return Jimple.v().newStaticInvokeExpr(implMethod, args);
			} else {
				// instance methods
				
				if (method.isConstructor()) {
					// TODO: new array?
					// invoke special
	                RefType type = method.getDeclaringClass().getType();
	                NewExpr newRef = Jimple.v().newNewExpr(type);
	                Local newLocal = Jimple.v().newLocal("rnew", type);
	                jb.getLocals().add(newLocal);
	    				us.add(Jimple.v().newAssignStmt(
	    				    newLocal,
	    				    newRef
	    				));
					SpecialInvokeExpr specialInvokeExpr = Jimple.v().newSpecialInvokeExpr(newLocal, method.makeRef(), args); // args does not include the base
					InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(specialInvokeExpr);
					us.add(invokeStmt); 
					return newLocal;
					
				} else {
					// FIXME: how to log assertions?
					if (args.size() < 1)
						G.v().out.println("warning: LambdaMetaFactory: missing base reference for instance invocation, method: " + implMethod.getSignature());
					
					if (method.isPrivate()) {
						// invoke special
						return Jimple.v().newSpecialInvokeExpr(args.get(0), method.makeRef(), rest(args));
					} else {
						if (implClass.isInterface())
							return Jimple.v().newInterfaceInvokeExpr(args.get(0), method.makeRef(), rest(args));
						else
							// invoke virtual
							return Jimple.v().newVirtualInvokeExpr(args.get(0), method.makeRef(), rest(args));
					}
				}
			}
		}

		private List<Local> rest(List<Local> args) {
			int first = 1;
			int last = args.size();
			if (last < first)
				return Collections.<Local>emptyList();
			return args.subList(first, last);
		}
    }
    
    // FIXME: Move to 'G'?
    private static int uniq;
    private static synchronized long uniqSupply() {
        return ++uniq;
    }
}
