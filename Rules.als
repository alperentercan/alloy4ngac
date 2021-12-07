module library/rules[State] // This module gives the abstraction for policy.

open library/graph
open util/ordering[Priority] as ord // Create the ordering of priorities.
enum Priority {P1,P2,P3,P4,P5,P6,P7,P8}

// Abstract Allowance Rule. Note that the actual rules will be given in the main function by extending this.
abstract sig Allowance {
		subject_attribute: AttributeNodeSubject,
    		action_set:  set Actions, //Actions is not being treated as a set by Alloy
		object_attribute: AttributeNodeObject,
		state_set:  set State,
		priority: one Priority}

// Abstract Prohibition Rule. Note that the actual rules will be given in the main function by extending this.
abstract sig Prohibition {
		subject_attribute: AttributeNodeSubject,
     		action_set:  set Actions, //Actions is not being treated as a set by Alloy
		object_attribute: AttributeNodeObject,
		state_set: set State,
		priority: one Priority
}

//action access check for only allowances
pred access_allowance_prioritized(sub: Subject, actset: Actions, obj: Object, stateset: set State, p: Priority){
	all act: actset, state: stateset |
	some snode: AttributeNodeSubject, onode: AttributeNodeObject, 
	allow_rule: Allowance |
		SubjectDAGPath[sub, snode] and  ObjectDAGPath[obj, onode] and
		(snode=allow_rule.subject_attribute) and (onode = allow_rule.object_attribute) and
		(act in allow_rule.action_set) and
		(state in allow_rule.state_set) and
		(act in sub.SubjectActions) and //check if Subject is allowed these action(s)
		(act in obj.ObjectActions) and //check if Object allows these action(s)
		(ord/lte[p, allow_rule.priority])
		
}

////action access check for only prohibitions
pred access_prohibition_prioritized(sub: Subject, actset: Actions, obj: Object, stateset: set State, p: Priority){
	all act: actset, state: stateset |
	some snode: AttributeNodeSubject, onode: AttributeNodeObject, 
	prohibit_rule: Prohibition |
		SubjectDAGPath[sub, snode] and  ObjectDAGPath[obj, onode] and
		(snode=prohibit_rule.subject_attribute) and (onode = prohibit_rule.object_attribute) and
		(act in prohibit_rule.action_set) and
		(state in prohibit_rule.state_set) and
		(act in sub.SubjectActions) and //check if Subject is allowed these action(s)
		(act in obj.ObjectActions)  and //check if Object allows these action(s)
		(ord/lte[p, prohibit_rule.priority])
}

//action access check over both allowances and prohibitions
pred access_check_prioritized(sub: Subject, acts: Actions, obj: Object, states: set State){
	some p:  Priority|
	access_allowance_prioritized[sub, acts, obj, states, p] and
	not 	access_prohibition_prioritized[sub, acts, obj, states, p]
}

// Show  ReachableObjects for a subject in the given state.
sig ReachableObject in Object{
}

pred subject2objectAccess(sub: Subject,  actset: Actions, stateset: set State){
	(all ro:ReachableObject | access_check_prioritized[sub, actset,  ro, 
	 stateset]) and
	(all ro: Object-ReachableObject | not access_check_prioritized[sub, actset,  ro, 
	 stateset])
} 		



