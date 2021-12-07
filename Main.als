module library/main


open library/rules[AutomatonState] // Policy is stateful and states will be given as AutomatonState instances

open library/statemachine[Subject, Object, Actions] as sm // States will keep track of Subject, Object, Actions
											// These are included from library/rules which imports library/graph


// Concrete allowance rules. The abstract signature Allowance is important from library/rules.

// A base allowance rule that willl allow actions if no prohibition rule exists.
one sig Allowance_BaseAllowance extends Allowance {} {
		(subject_attribute = Drone) and
		(object_attribute =  CityA) and
		(action_set = Actions) and
		(state_set =   AutomatonState) and
		(priority = P1)}


// Start With High Importance Buildings
one sig Prohibition_ImportanceOrder  extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = LowImportance) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[HighImportance, aState] }) and // Valid for all states where there is a HighImportance
																			 // room that is on fire.
		(priority = P8)
}

// Check if all children of an attribute ext(inguished).
pred AttributeEXT(att: AttributeNodeObject,  aState: AutomatonState){ 
all obj: Object|  (not ObjectDAGPath[obj, att])  or aState.state_map[obj] = NoFire
}

//  DO NOT LEAVE UNTIL THE BUILDING IS DONE RULES
// There are 2 rules for each building because we have 3 buildings in total. Ex:
// Prohibition_FinishBuildingB1_1: Do not go to B2 before you finish B1.
// Prohibition_FinishBuildingB1_2: Do not go to B3 before you finish B1.
one sig Prohibition_FinishBuildingB1_1 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B2) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B1, aState]  and ObjectDAGPath[aState.curr, B1]}) and
		(priority = P7)
}

one sig Prohibition_FinishBuildingB1_2 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B3) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B1, aState]  and ObjectDAGPath[aState.curr, B1]}) and
		(priority = P7)
}

one sig Prohibition_FinishBuildingB2_1 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B1) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B2, aState]  and ObjectDAGPath[aState.curr, B2]}) and
		(priority = P7)
}

one sig Prohibition_FinishBuildingB2_2 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B3) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B2, aState]  and ObjectDAGPath[aState.curr, B2]}) and
		(priority = P7)
}


one sig Prohibition_FinishBuildingB3_1 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B1) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B3, aState]  and ObjectDAGPath[aState.curr, B3]}) and
		(priority = P7)
}


one sig Prohibition_FinishBuildingB3_2 extends Prohibition {} {
		(subject_attribute = Drone) and
		(object_attribute = B2) and 
		(action_set = Actions)  and
		(state_set =  {aState: AutomatonState| not AttributeEXT[B3, aState]  and ObjectDAGPath[aState.curr, B3]}) and
		(priority = P7)
}

// Bind policy to state machine. Force the input word to be valid.
pred validRun{
	all t:Time | let i = StateMachine.input.t | access_check_prioritized[i.sub, i.act, i.obj, StateMachine.state.t]
}

pred initially_acceptable{
 subject2objectAccess[D1, DropPayload,  StateMachine. state.(sm/time/first)]
}

//fact{validRun and startRoom[R1]}

//assert access_control{
//let s0 = StateMachine.state.(sm/time/first) | 
//	access_check_prioritized[D1, Actions,  R1, s0] and 
//	access_check_prioritized[D1, Actions,  R2, s0] and 
//	access_check_prioritized[D1, Actions,  R3, s0] and
// 	not access_check_prioritized[D1, Actions,  R4, s0] and
//	not access_check_prioritized[D1, Actions,  R5, s0] 
//} 


//check access_control for 16

// Find a trace that is valid under this policy where the drone starts in R1 and in 5 steps  R5 is not on fire. 
// Also mark Rooms that are allowed in the initial state as ReachableObject.
run {validRun and startRoom[R1] and roomExt[R5] and initially_acceptable } for 6 but 5 Time

//run {store_best_allow_path[D1, DropPayload, R4,  StateMachine. state.(sm/time/first)]} for 6 but 1 AllowancePath, 1 ProhibitionPath

