EMFTVM Invoke implementation
- 

EMFTVM BYTECODE implementation
- org.eclipse.m2m.atl.emftvm.impl.CodeBlockImpl



==== High ====		
		=== Model Handlling ===
				case SET:
					frame.setPc(pc);
					set(stack.pop(), stack.pop(), ((Set) instr).getFieldname(), frame);
					break;
				case GET:
					frame.setPc(pc);
					stack.push(get(((Get) instr).getFieldname(), frame, stack.pop()));
					break;	
				case ADD:
					add(-1, stack.pop(), stack.pop(), ((Add) instr).getFieldname(), frame);
					break;
				case REMOVE:
					remove(stack.pop(), stack.pop(), ((Remove) instr).getFieldname(), frame);
					break;
				case INSERT:
					add((Integer) stack.pop(), stack.pop(), stack.pop(), ((Insert) instr).getFieldname(), frame);
					break;
				case DELETE:
					frame.setPc(pc);
					delete(frame, (EObject) stack.pop());
					break;
		=== Code Block ===
				case AND:
					cb = ((And) instr).getCodeBlock();
					frame.setPc(pc);
					stack.push((Boolean) stack.pop() && (Boolean) cb.execute(new StackFrame(frame, cb)));
					break;
				case OR:
					cb = ((Or) instr).getCodeBlock();
					frame.setPc(pc);
					stack.push((Boolean) stack.pop() || (Boolean) cb.execute(new StackFrame(frame, cb)));
					break;
				case IMPLIES:
					cb = ((Implies) instr).getCodeBlock();
					frame.setPc(pc);
					stack.push(!(Boolean) stack.pop() || (Boolean) cb.execute(new StackFrame(frame, cb)));
					break;					
				case GETCB:
					stack.push(((Getcb) instr).getCodeBlock());
					break;
				case INVOKE_CB:
					cb = ((InvokeCb) instr).getCodeBlock();
					frame.setPc(pc);
					// Use Java's left-to-right evaluation semantics:
					// stack = [..., arg1, arg2]
					argcount = ((InvokeCb) instr).getArgcount();
					if (cb.getStackLevel() > 0) {
						stack.push(cb.execute(frame.getSubFrame(cb, argcount > 0 ? stack.pop(argcount) : EMPTY)));
					} else {
						cb.execute(frame.getSubFrame(cb, argcount > 0 ? stack.pop(argcount) : EMPTY));
					}
					break;

		=== Control ===		
				case ISNULL:
					stack.push(stack.pop() == null);
					break;

				case NOT:
					stack.push(!(Boolean) stack.pop());
					break;
				case XOR:
					stack.push((Boolean) stack.pop() ^ (Boolean) stack.pop());
					break;
				case IFN:
					if (!(Boolean) stack.pop()) {
						pc = ((Ifn) instr).getOffset();
					}
					break;
				case IFTE:
					frame.setPc(pc);
					if ((Boolean) stack.pop()) {
						cb = ((Ifte) instr).getThenCb();
					} else {
						cb = ((Ifte) instr).getElseCb();
					}
					stack.push(cb.execute(new StackFrame(frame, cb)));
					break;
					
					
					
					
					
					
					
					
					
==== Not supported	====				
				case GET_SUPER:
					frame.setPc(pc);
					stack.push(getSuper(getField(), ((GetSuper) instr).getFieldname(), frame, stack.pop()));
					break;
				case MATCH_S:
					frame.setPc(pc);
					// stack = [..., arg1, arg2, rule]
					argcount = ((MatchS) instr).getArgcount();
					stack.push(argcount > 0 ? matchOne(frame, (Rule) stack.pop(), stack.pop(argcount, new EObject[argcount])) : matchOne(
							frame, (Rule) stack.pop()));
					break;
				case INVOKE_CB_S:
					cb = (CodeBlock) stack.pop();
					frame.setPc(pc);
					// Use Java's left-to-right evaluation semantics:
					// stack = [..., arg1, arg2]
					argcount = ((InvokeCbS) instr).getArgcount();
					// unknown code block => always produce one stack element
					stack.push(cb.execute(frame.getSubFrame(cb, argcount > 0 ? stack.pop(argcount) : EMPTY)));
					break;
				case INVOKE_ALL_CBS:
					frame.setPc(pc);
					// Use Java's left-to-right evaluation semantics:
					// stack = [..., arg1, arg2]
					argcount = ((InvokeAllCbs) instr).getArgcount();
					Object[] args = argcount > 0 ? stack.pop(argcount) : EMPTY;
					for (CodeBlock ncb : getNested()) {
						if (ncb.getStackLevel() > 0) {
							stack.push(ncb.execute(frame.getSubFrame(ncb, args)));
						} else {
							ncb.execute(frame.getSubFrame(ncb, args));
						}
					}
					break;
				case GETENVTYPE:
					stack.push(EXEC_ENV);
					break;
				case GET_TRANS:
					frame.setPc(pc);
					stack.push(getTrans(((GetTrans) instr).getFieldname(), frame, stack.pop()));
					break;
				case SET_STATIC:
					setStatic(stack.pop(), stack.pop(), ((SetStatic) instr).getFieldname(), env);
					break;
				case GET_STATIC:
					frame.setPc(pc);
					stack.push(getStatic(((GetStatic) instr).getFieldname(), frame, stack.pop()));
					break;
				case INVOKE_SUPER:
					frame.setPc(pc);
					stack.push(invokeSuper(getOperation(), ((InvokeSuper) instr).getOpname(), ((InvokeSuper) instr).getArgcount(), frame,
							stack));
					break;
				case MATCH:
					frame.setPc(pc);
					// Use Java's left-to-right evaluation semantics:
					// stack = [..., arg1, arg2]
					argcount = ((Match) instr).getArgcount();
					stack.push(argcount > 0 ? matchOne(frame, findRule(frame.getEnv(), ((Match) instr).getRulename()),
							stack.pop(argcount, new EObject[argcount])) : matchOne(frame,
							findRule(frame.getEnv(), ((Match) instr).getRulename())));
					break;	