module library/statemachine[subs, objs, acts] // States do refer to Subject, Object, Action but they do not 
								      // address anything specific to these signatures. (for example no property of those is used.)
								 // So, we can use placeholders for them and put the actual signatures in when importing this module..

open library/time 
enum RoomStatus{Fire, NoFire} 

// States
sig AutomatonState{
	state_map :  objs -> one RoomStatus, // A RoomStatus for each room. Like a lookup table.
	curr: objs // Where is the drone currently? 
} 

// This machine just keeps track of states and inputs. This is done by mapping a state and input to each Time step.
one sig StateMachine{
	state: AutomatonState one -> Time, 
	input: Operation one -> Time
}

// The Alphabet. Each input signal will be a tuple <Subject, Action, Object>. 
sig Operation{
	sub: subs,
	act: acts,
	obj: objs
}

// Describe the transitions of StateMachine.
fact StateMachineFacts{
	(all t: Time | t = time/last or
		let s = StateMachine.state.t | // just introducing a shorthand
			let s' = StateMachine.state.(time/next[t]) | // again another shorthand
				let i =   StateMachine.input.t | 
					(s'.state_map = s.state_map++(i.obj -> NoFire)) and // One simple transition rule. If a payload is dropped, there won't be a fire
															// in that room.
					s'.curr = i.obj  // update the current room. 
					)
			and
	(StateMachine.state.(time/first).state_map = objs -> Fire)  // Initial State - all rooms on fire
	
}

// Use this predicate to determine the room drone starts in.
pred startRoom(r: objs){
StateMachine.state.(time/first).curr=r
}

// Check whether there is a time where there isn't a fire in the room. 
pred roomExt(r: objs){
 some  t: Time |  StateMachine.state.t.state_map[r] = NoFire 
}



