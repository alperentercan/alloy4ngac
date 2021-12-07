module library/graph // This module draws the attribute graph. 

enum Actions {DropPayload}

 //Subjects and Subject graph
abstract sig Subject {
		NodeID: one AttributeNodeSubject,
		SubjectActions: set Actions //actions allowed for subject
}

one sig D1 extends Subject {} {
	(NodeID = D1Node) and 
	(SubjectActions = Actions)
}


// Attributes
abstract sig AttributeNodeSubject{
		children: set AttributeNodeSubject
} 

one sig D1Node extends AttributeNodeSubject {} {
	children = Drone
}

one sig Drone extends AttributeNodeSubject {} {
	children = none
}




// Objects

//Objects and Object graph
abstract sig Object {
		NodeID: one AttributeNodeObject,
		ObjectActions: set Actions  //Legal action set for each object
}

// Rooms
one sig R1 extends Object {} {
        (NodeID =  R1Node) and
	  (ObjectActions = Actions)
}

one sig R2  extends Object {} {
        (NodeID =  R2Node) and
	  (ObjectActions = Actions)
}

one sig R3 extends Object {} {
        (NodeID =  R3Node) and
	  (ObjectActions = Actions)
}

one sig R4  extends Object {} {
        (NodeID =  R4Node) and
	  (ObjectActions =Actions)
}

one sig R5  extends Object {} {
        (NodeID =  R5Node) and
	  (ObjectActions =Actions)
}

abstract sig AttributeNodeObject{
            children: set AttributeNodeObject
} 

// Room Nodes
one sig R1Node  extends AttributeNodeObject {} {
                children = F1B1
}

one sig R2Node extends AttributeNodeObject {} {
                children = F1B1
}

one sig R3Node extends AttributeNodeObject {} {
                children = F2B1
}

one sig R4Node extends AttributeNodeObject {} {
                children = F1B2
}

one sig R5Node extends AttributeNodeObject {} {
                children = F1B3
}

// Floors: Ex, F2B1 is the 2nd Floor of B1.
one sig F1B1 extends AttributeNodeObject {} {
                children = B1
}

one sig F2B1 extends AttributeNodeObject {} {
                children = B1
}

one sig F1B2 extends AttributeNodeObject {} {
                children = B2
}

one sig F1B3 extends AttributeNodeObject {} {
                children = B3
}

// Buildings
one sig B1 extends AttributeNodeObject {} {
                children = HighImportance
}

one sig B2 extends AttributeNodeObject {} {
                children = LowImportance
}

one sig B3 extends AttributeNodeObject {} {
                children = LowImportance
}

// Importance Levels
one sig HighImportance extends AttributeNodeObject {} {
                children = CityA
}

one sig LowImportance extends AttributeNodeObject {} {
                children = CityA
}

// City. There is just one for the case study.
one sig CityA extends AttributeNodeObject {} {
	children = none
}

//Subject graph path predicate
//Is there a path from sub to sub_attribute?
pred SubjectDAGPath(sub: Subject, sub_attribute: AttributeNodeSubject)
{
	(sub_attribute in sub.NodeID.*children) 
}

//
//Object graph path predicate
//Is there a path from obj to obj_attribute?
pred ObjectDAGPath(obj: Object, obj_attribute: AttributeNodeObject)
{
	(obj_attribute in obj.NodeID.*children) 
}


assert graphAssert{
SubjectDAGPath[D1, Drone] and
ObjectDAGPath[R1 + R2, B1] and 
not ObjectDAGPath[R1, B2] and
not ObjectDAGPath[R1 + R5, B2] and 
not ObjectDAGPath[R1, B1 + B3] and 
not ObjectDAGPath[R1, B1 + B3] 
}
check graphAssert

