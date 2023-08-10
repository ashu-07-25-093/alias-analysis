package submit_a1;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import com.google.common.collect.Sets;

import dont_submit.AliasQuery;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import soot.ArrayType;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

public class AliasAnalysis extends BodyTransformer{
	
	static int cnt = 1;
	
	// This function is calculating all the fields of a class, and it's superclass recursively,
	// and then returns all those soot fields.
	synchronized Chain<SootField> getAllFields(Value val)
	{	
		// convert into refType
		
		Chain<SootField> fields = null;
		
		if(val.getType() instanceof RefLikeType && !(val.getType() instanceof ArrayType))
		{
			RefType rf = (RefType) val.getType();
			
			// find the sootclass and then it's fields
			fields = rf.getSootClass().getFields();
			
			SootClass c = rf.getSootClass();
			
			// adding all the fields of superclass
			while(c.hasSuperclass())
			{
				// getting superclass of current sootClass
				c = c.getSuperclass();
				
				Chain<SootField> fs = c.getFields();
				
				if(!fs.isEmpty())
					fields.addAll(fs);
			}
			
		}
		
		return fields;
		
	}
	
	// This function is used to calculate the concept of reachable heap....
	// When we're making the field of any var to bottom, we have to first calculate all the other
	// reachable reference from this var and make their fields also bottom
	synchronized Set<String> getReachableRefs(Set<String> st, Map<String, Set<String>> in_old_ro, Map<String, Map<String, Set<String>>> in_old_sigma)
	{
		// taking temporary ro and sigma map
		Map<String, Set<String>> in_new_ro = new HashMap<>();
		Map<String, Map<String, Set<String>>> in_new_sigma = new HashMap<>();
		
		Set<String> set = new HashSet<>();
		set = st;
		
		in_new_ro.putAll(in_old_ro);
		in_new_sigma.putAll(in_old_sigma);
		
		ArrayList<String> reachable_fields = new ArrayList<>();
		Set<String> final_fields = new HashSet<>();
		
		// adding all the refs of current variable
		
		if(st!=null)
		{
			reachable_fields.addAll(set);
			
			// to store the final fields for which we will make them to bottom
			
			
			// visited map, to store for which refs, we've already calculated, otherwise loop will go into infinite
			Map<String, Boolean> visited = new HashMap<>();
			
			while(!reachable_fields.isEmpty())
			{
				// removing first element from the arrayList
				String str = reachable_fields.remove(0);
				
				// if not visited already then only calculate
				if(!visited.containsKey(str))
				{
					// adding ref to final field
					final_fields.add(str);
					
					Map<String, Set<String>> mp = new HashMap<>();
					
					if(in_new_sigma.containsKey(str))
						mp = in_new_sigma.get(str);
					
					// for all the fields of curr ref, iterate through map and add the refs, this field point to...
					for(Map.Entry<String, Set<String>> entry:mp.entrySet())
					{
						Set<String> sett = new HashSet<>();
						sett = entry.getValue();
						
						reachable_fields.addAll(sett);
					}
					
					visited.put(str, true);
				}
			}
		}
		
		return final_fields;
		
	}
	
	// implementation of flowFunction, which will take unit, it's ro and sigma map, bottom and visited map as an arguments
	synchronized ArrayList<Map<String, Map<String, Set<String>>>> flowFunction(Unit u, Map<String, Set<String>> in_old_ro, Map<String, Map<String, Set<String>>> in_old_sigma, 
			Set<String> bot, Map<Stmt, String> vis)
	{
		// new ro and sigma map, on which we will do calculations and return
		Map<String, Set<String>> in_new_ro = new HashMap<>();
		
		Map<String, Map<String, Set<String>>> in_new_sigma = new HashMap<>();
		
		Set<String> bottom = new HashSet<>();
		
		Map<Stmt, String> visited = new HashMap<>();
		
		visited = vis;
		
		bottom = bot;
		
		// doing deep copy of ro and sigma map to new ro and sigma map
		for(Map.Entry<String, Set<String>> entry:in_old_ro.entrySet())
		{
			String key = entry.getKey();
			
			in_new_ro.put(key, new HashSet<String>(in_old_ro.get(key)));
		}
		
		for(Map.Entry<String, Map<String, Set<String>>> entry:in_old_sigma.entrySet())
		{
			String key = entry.getKey();
			
			in_new_sigma.put(key, new HashMap<String, Set<String>>());
			
			Map<String, Set<String>> mp1 = in_old_sigma.get(key);
			
			for(Map.Entry<String, Set<String>> ent:mp1.entrySet())
			{
				String k = ent.getKey();
				
				in_new_sigma.get(key).put(k, new HashSet<String>(mp1.get(k)));
				
			}
		}
		
		ArrayList<Map<String, Map<String, Set<String>>>> in_new_ro_sigma = new ArrayList<>();
		
		// converting unit to statement
		Stmt stmt = (Stmt) u;
		
		// checking if the stmt is of type definition
		if(stmt instanceof DefinitionStmt)
		{
			DefinitionStmt ds = (DefinitionStmt) stmt;
			
			// getting the left and right operands of DefinitionStmt
			Value lhs = ds.getLeftOp();
			Value rhs = ds.getRightOp();
			
			// to calculate the arguments
			if(stmt instanceof IdentityStmt)
			{
				IdentityStmt is = (IdentityStmt) stmt;
				
				Value lhs_ = is.getLeftOp();
				Value rhs_ = is.getRightOp();
				
				Set<String> st = new HashSet<>();
				String s = "R" + cnt;
				st.add(s);
				cnt++;
				bottom.add(s);
				
				in_new_ro.put(lhs_.toString(), bottom);
				
				in_new_sigma.put(lhs_.toString(), new HashMap<>());
				
				Map<String, Set<String>> field = new HashMap<>();
				
				// getting all the fields
				Chain<SootField> fields = getAllFields(lhs_);
				
				if(fields!=null)
				{
					// for each sootField, check if it's RefLikeType, then only add it to the map and initialize
					for(SootField f:fields)
					{
						if(f.getType() instanceof RefLikeType)
						{
							field.put(f.getName().toString(), bottom);
						}
					}
					
					in_new_sigma.put(s, field);
				}
				
			}
			// if the stmt is of type allocation
			else if(rhs instanceof NewExpr)
			{
				// getting the lhs variable
				String local = lhs.toString();
				Set<String> st = new HashSet<>();
				
				String s = "";
				
				// if this stmt is not visited then only assign new ref to this stmt
				// in case of loop, we have perform new allocation only one time, that's why we use visited map
				if(!visited.containsKey(stmt))
				{
					s = "R"+cnt;      // creating new ref
					st.add(s);
					bottom.add(s);    // as and when we create new ref, we have to add it to the bottom
					cnt++;
					
					visited.put(stmt, s);   // make curr stmt as visited
				}
				else
				{	
					// getting the stmt for which we've already done calculations
					s = visited.get(stmt); 
					st.add(s);
					// re-assigning the same ref to curr stmt
					in_new_ro.put(local, st);
				}
				
				in_new_ro.put(local, st);
				
				// calculations of sigma field, when allocation is being done,
				// fields for that ref will also get initialized to empty
				in_new_sigma.put(local, new HashMap<>());
				
				Map<String, Set<String>> field = new HashMap<>();
				
				// getting all the fields
				Chain<SootField> fields = getAllFields(lhs);
				
				// for each sootField, check if it's RefLikeType, then only add it to the map and initialize
				for(SootField f:fields)
				{
					if(f.getType() instanceof RefLikeType)
					{
						field.put(f.getName().toString(), new HashSet<>());
					}
				}
				
				in_new_sigma.put(s, field);
			}
			// calculation of NewArrayExpr
			else if(rhs instanceof NewArrayExpr)
			{
				String local = lhs.toString();
				Set<String> st = new HashSet<>();
				
				String s = "";
				
				if(!visited.containsKey(stmt))
				{
					s = "R"+cnt;
					st.add(s);   // adding the new ref to set
					bottom.add(s);  // adding to bottom
					cnt++;
					
					visited.put(stmt, s);     // mark is as visited
				}
				else
				{	
					s = visited.get(stmt); 
					st.add(s);
				}
				in_new_ro.put(local, st);     // make refs for lhs
			}
			// if rhs is any invokeExpr
			else if(rhs instanceof InvokeExpr)
			{
				// getting lhs field
				String local = lhs.toString();
				
				in_new_ro.put(local, bottom);    // lhs assigned to bottom
				
				// calculation for arguments, we've to make the fields of arguments to bottom
				
				// getting the list containing the arguments passing to the function
				List<Value> val = ((InvokeExpr) rhs).getArgs();
				
				// check if function call contains any arguments, then only do calculations
				if(!val.isEmpty())
				{
					// for each of the argument, first get all the refs it's pointing to
					// then calculate all the reachable fields from these refs.
					// now get all the soot fields of current argument, and for each of the reachable field -> for each 
					// sootFields, assign bottom
					for(Value v:val)
					{
						Set<String> set = new HashSet<>();
						if(in_new_ro.containsKey(v.toString()))
							set = new HashSet<>(in_new_ro.get(v.toString()));
						
						// getting all the reachable fields of current argument
						Set<String> reachable_fields = getReachableRefs(set, in_new_ro, in_new_sigma);
						
						// getting all the sootfields of current argument
						
						Chain<SootField> arg_sootfields = getAllFields(v);
						
						// iterate through all the reachable fields
						for(String str:reachable_fields)
						{
							// iterate through all the sootFields
							for(SootField f:arg_sootfields)
							{
								// check it the current sootField it of RefLike Type, then only make it as bottom
								if(f.getType() instanceof RefLikeType)
								{
									if(in_new_sigma.containsKey(str))
										in_new_sigma.get(str).put(f.getName().toString(), bottom);
								}
							}
						}
					}
				}
				// 1.) z = foo(y), 2.) z = x.foo(y)
				// if rhs is of 2nd type then we have to get the base of the rhs and make all the fields bottom
				if(rhs instanceof InstanceInvokeExpr)
				{
					// getting the base
					Value v = ((InstanceInvokeExpr) rhs).getBase();
				
					// base fields manipulation
					Set<String> set = new HashSet<>();
					
					if(in_new_ro.containsKey(v.toString()))
						set = in_new_ro.get(v.toString());
					
					// getting all the reachable fields from the base
					Set<String> reachable_fields = getReachableRefs(set, in_new_ro, in_new_sigma);
					
					// getting all the sootFields of base
					Chain<SootField> arg_sootfields = getAllFields(v);
					
					// for each reachable field, iterate through all sootFields of base and assign bottom
					for(String str:reachable_fields)
					{
						for(SootField f:arg_sootfields)
						{
							// check if field is of RefLikeType
							if(f.getType() instanceof RefLikeType)
							{
								if(in_new_sigma.containsKey(str))
									in_new_sigma.get(str).put(f.getName().toString(), bottom);
							}
						}
					}
				}
				
			}
			
			// store statement x.f = y
			else if(lhs instanceof InstanceFieldRef && (rhs.getType() instanceof RefLikeType && !(rhs instanceof InstanceFieldRef)))
			{
				// getting the base and field from the lhs
				String local = ((InstanceFieldRef) lhs).getBase().toString();
				String field = ((InstanceFieldRef) lhs).getField().getName().toString();
				
				//strong update.....if base is pointing to only one ref then do strong update
				if(!in_new_ro.isEmpty())
				{
					if(in_new_ro.containsKey(local))
					{
						if(in_new_ro.get(local).size()==1)
						{
							// getting the ref, base pointing to...
							String ref = in_new_ro.get(local).iterator().next();
							
							Set<String> st = new HashSet<>();
							
							// getting all the refs, rhs pointing to...
							if(in_new_ro.containsKey(rhs.toString()))
								st = in_new_ro.get(rhs.toString());
							
							// assigning refs to field of base
							if(in_new_sigma.containsKey(ref))
								in_new_sigma.get(ref).put(field, st);
						}
						
						// weak update.....if base is pointing to more than one ref
						else
						{
							// getting all the refs, base is pointing to...
							Set<String> st = new HashSet<>();
							st = in_new_ro.get(local);
							
							// getting all the refs, rhs is pointing to...
							Set<String> set_rhs = new HashSet<>();
							if(in_new_ro.containsKey(rhs.toString()))
								set_rhs = new HashSet<>(in_new_ro.get(rhs.toString()));
							
							// for each of the ref pointed by base, first get all the old refs of the given field,
							// then do union of old refs with new refs(refs pointed by rhs), and put it back in the map...
							for(String s:st)
							{
								Set<String> s1 = new HashSet<>();
								boolean flag = false;
								
								if(in_new_sigma.containsKey(s) && in_new_sigma.get(s).containsKey(field))
								{
									s1 = new HashSet<>(in_new_sigma.get(s).get(field));
									flag = true;
								}
								
								s1 = Sets.union(s1, set_rhs);
								
								// doing union of old and new refs
								
								if(flag)
									in_new_sigma.get(s).put(field, s1);
							}
						}

					}
				}	
					
			}
			// load statement x = y.f
			else if(!(lhs instanceof InstanceFieldRef) && rhs instanceof InstanceFieldRef)
			{
				
				// getting the base and field of rhs
				String local = ((InstanceFieldRef) rhs).getBase().toString();
				String field = ((InstanceFieldRef) rhs).getField().getName().toString();
				
				// to store teh refs pointed by base
				Set<String> st = new HashSet<>();
				
				// getting the refs pointed by base
				if(in_new_ro.containsKey(local))
					st = in_new_ro.get(local);
				
				// to store the union of the refs pointed by field, for all refs poitned by base
				Set<String> set_ = new HashSet<>();
				
				// for eachh refs pointed by base
				for(String s:st)
				{
					// get all the refs pointed by field of current ref
					Set<String> set = new HashSet<>();
					
					if(in_new_sigma.containsKey(s) && in_new_sigma.get(s).containsKey(field))
						set = in_new_sigma.get(s).get(field);
					
					// performing the union
					set_ = Sets.union(set_, set);
				}
				
				// assigning union set to the ro of lhs
				in_new_ro.put(lhs.toString(), set_);
			}
			// copy statement x = y
			else if(!(lhs instanceof InstanceFieldRef) && !(rhs instanceof InstanceFieldRef))
			{
				// to store the refs pointed by rhs
				Set<String> st = new HashSet<>();
				
				if(in_new_ro.containsKey(rhs.toString()))
					st = in_new_ro.get(rhs.toString()); 
				
				in_new_ro.put(lhs.toString(), st);
				
			}
		}
				
		// creating dummy map to make similar structure as sigma map, to add it to the list...so that we can return
		// ro and sigma map
		Map<String, Map<String, Set<String>>> dummy = new HashMap<>();
		dummy.put("dummy", in_new_ro);
		
		in_new_ro_sigma.add(dummy);
		in_new_ro_sigma.add(in_new_sigma);
		
		return in_new_ro_sigma;
	}
	
	@Override
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		// Initialization
		
		// getting the class and method name being analyzed
		//System.out.println(arg0);
		String currClass = arg0.getMethod().getDeclaringClass().toString();
		String currMethod = arg0.getMethod().getName().toString();
		
		// ro and sigma map, to store for each unit
		Map<Unit, Map<String, Set<String>>> In_ro = new HashMap<>();    // {unit -> {var -> refs}}
		Map<Unit, Map<String, Map<String, Set<String>>>> In_sigma = new HashMap<>();  // {unit -> {ref_var -> {field -> {refs}}}}
		
		// bottom(Og)
		Set<String> bottom = new HashSet<>();
		
		// visited map, to keep track of statement inside loop visited only once during loop...
		Map<Stmt, String> visited = new HashMap<>();
		
		// worklist of units...
		Set<Unit> worklist = new HashSet<>();
		
		// creating empty ro and sigma map to do initialization
		Map<String, Set<String>> ro = new HashMap<>();
		
		Map<String, Map<String, Set<String>>> sigma = new HashMap<>();		
		
		for(Unit u:arg0.getUnits())
		{
			Stmt stmt = (Stmt) u;
			worklist.add(u);
				
			In_ro.put(u, ro);
			
			In_sigma.put(u, sigma);			
		}
		
		// getting control flow graph
		UnitGraph cfg = new BriefUnitGraph(arg0);
		
		// last unit, on which we will run our queries
		Unit lastUnit = cfg.getHeads().get(0);
		
		// loop, while worklist is not empty
		while(!worklist.isEmpty())
		{
			// getting the first element from worklist
			Unit u = worklist.iterator().next();      // current unit
			
			worklist.remove(u);
			
			Stmt stmt = (Stmt) u;     // type casting unit to stmt
					
			List<Unit> preds = cfg.getPredsOf(u);     // getting the predecessor of current unit
			
			// getting the in_ro and in_sigma of current unit
			Map<String, Set<String>> dfin_ro = new HashMap<>();
			dfin_ro = In_ro.get(u);
			
			Map<String, Map<String, Set<String>>> dfin_sigma = new HashMap<>();
			dfin_sigma = In_sigma.get(u);
			
			// to store the updated in_ro and in_sigma for current unit
			Map<String, Set<String>> toteff_ro = new HashMap<>();
			Map<String, Map<String, Set<String>>> toteff_sigma = new HashMap<>();
			
			for(Unit pred:preds)
			{
				Stmt stm = (Stmt) pred;
				
				// to store the in_ro of current predecessor
				Map<String, Set<String>> pred_in_ro = new HashMap<>(In_ro.get(pred));
				
				// to store the in_sigma of current predecessor
				Map<String, Map<String, Set<String>>> pred_in_sigma = new HashMap<>(In_sigma.get(pred));
				
				// to store the ro and sigma return by flowFunction
				ArrayList<Map<String, Map<String, Set<String>>>> out_ro_sigma = new ArrayList<>();
				
				// calling the flowFuction
				out_ro_sigma = flowFunction(pred, pred_in_ro, pred_in_sigma, bottom, visited);
				
				// store the out_ro of current predecessor
				Map<String, Set<String>> pred_out_ro = new HashMap<>(out_ro_sigma.get(0).get("dummy"));
				// store the out_sigma of current predecessor
				Map<String, Map<String, Set<String>>> pred_out_sigma = new HashMap<>(out_ro_sigma.get(1));
				
				// to calculate the union of out_ro of all predecessors 
				for(Map.Entry<String, Set<String>> entry:pred_out_ro.entrySet())
				{
					String key = entry.getKey();
					
					// if current key is already contained, then do union
					if(toteff_ro.containsKey(key))
					{
						Set<String> s1 = new HashSet<>(toteff_ro.get(key));
						
						Set<String> s2 = new HashSet<>(pred_out_ro.get(key));
						
						Set<String> s3 = new HashSet<>();
						s3 = Sets.union(s1, s2);
						
						toteff_ro.put(key, s3);
					}
					// if new key, then simply put it to the map...
					else
					{
						Set<String> s1 = new HashSet<>(pred_out_ro.get(key));
						
						toteff_ro.put(key, s1);
					}
						
				}
				
				// to calculate the union of out_sigma of all predecessors 
				for(Map.Entry<String, Map<String, Set<String>>> entry:pred_out_sigma.entrySet())
				{
					String key = entry.getKey();    // reference
					
					// if already contains the ref
					if(toteff_sigma.containsKey(key))
					{
						// get the map for current ref from both the sigma maps
						Map<String, Set<String>> mp = new HashMap<>(pred_out_sigma.get(key));
						
						Map<String, Set<String>> mp2 = new HashMap<>(toteff_sigma.get(key));
						
						// both sigma maps contains the same fields, to iterate through map and do union of the refs, pointed by
						// field
						for(Map.Entry<String, Set<String>> ent:mp.entrySet())
						{
							String k = ent.getKey();   // field
							
							Set<String> s1 = new HashSet<>();  // set of refs pointed by field
							if(mp.containsKey(k))
								s1 = mp.get(k);
							
							Set<String> s2 = new HashSet<>();
							if(mp2.containsKey(k))
								s2 = mp2.get(k);
							
							Set<String> s3 = new HashSet<>();
							s3 = Sets.union(s1, s2);     // union of both the sets
							
							mp2.put(k, s3);
						}
						toteff_sigma.put(key, mp2);
					}
					// if not present, then simply put it to map
					else
					{
						Map<String, Set<String>> mp = new HashMap<>(pred_out_sigma.get(key));
						
						toteff_sigma.put(key, mp);
					}	
				}
			}
			
			// if(old in_ro != new in_ro || old in_sigma != new in_sigma) for current unit of worklist
			// then update and add all it's successors to worklist...
			if(!dfin_ro.equals(toteff_ro) || !dfin_sigma.equals(toteff_sigma))
			{
				In_ro.put(u, toteff_ro);
				In_sigma.put(u, toteff_sigma);
				
				List<Unit> successors = cfg.getSuccsOf(u);      // getting the successors of current unit
				
				worklist.addAll(successors);      // adding successors to the worklist
			}
			
			lastUnit = u;

	}
		// outputting the query result
		Map<String, Set<String>> ans = new HashMap<>();

		ArrayList<AliasQuery> queries = A1.queryList;
		
		for(Unit u:arg0.getUnits())
		{
			List<Unit> succ = cfg.getSuccsOf(u);
			if(succ.isEmpty())
			{
				lastUnit = u;
				ans = In_ro.get(lastUnit);
				break;
			}
			
		}
		
		for(AliasQuery query:queries)
		{
			// getting left and right vars of query
			String leftVar = query.getLeftVar();
			String rightVar = query.getRightVar();
			
			// getting class and method names for which query is given
			String className = query.getClassName();
			String methodName = query.getMethodName();
			
			// checking the current class and method with query's class and method
			if(currClass.equals(className) && currMethod.equals(methodName))
			{	
				Set<String> intersect = new HashSet<>();
				
				// getting refs of left and right vars
				
				Set<String> st1 = new HashSet<>();
				if(ans.containsKey(leftVar))
					st1 = new HashSet<>(ans.get(leftVar));
				
				Set<String> st2 = new HashSet<>();
				if(ans.containsKey(rightVar))
					st2 = new HashSet<>(ans.get(rightVar));
		
				// finding intersection of both the sets
				intersect = Sets.intersection(st1, st2);
				
				// if intersection is not empty || both the sets are same then both the variables are alias...else Not alias
				if(!intersect.isEmpty() || st1.equals(st2))
				{
					int ind = queries.indexOf(query);
					A1.answers[ind] = "Yes";
				}
					
				else
				{
					int ind = queries.indexOf(query);
					A1.answers[ind] = "No";
				}
					
			}
		}
				
   }
		 
}
