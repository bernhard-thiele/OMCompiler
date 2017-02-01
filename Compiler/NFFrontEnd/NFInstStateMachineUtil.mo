/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2017, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
 * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from OSMC, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package NFInstStateMachineUtil

import DAE;
import NFPrefix.Prefix;
import HashTableCG;

protected import Flags;
protected import List;
protected import ComponentReference;
protected import HashTable;
protected import HashTableCrToSMNode;
// protected import HashTable3;
protected import HashSet;
// protected import Util;
// protected import Array;
// protected import DAEUtil;
// protected import InnerOuter;
// protected import Expression;
// protected import Debug;
// protected import PrefixUtil;
protected import DAEDump;

public uniontype SMNode
  record SMNODE "Collecting information about a state/mode"
    //DAE.Ident ident;
    DAE.ComponentRef componentRef;
    Boolean isInitial;
    HashSet.HashSet edges "relations to other modes due to in- and out-going transitions";
  end SMNODE;
end SMNode;

public uniontype FlatSMGroup
  record FLAT_SM_GROUP "Collecting information about a group of state components forming a flat state machine"
    DAE.ComponentRef initState;
    array<DAE.ComponentRef> states;
  end FLAT_SM_GROUP;
end FlatSMGroup;

public uniontype IncidenceTable
  record INCIDENCE_TABLE
    HashTable.HashTable cref2index "Map cref to corresponding index in incidence matrix";
    Boolean incidence[:,:] "Incidence matrix showing which modes are connected by transitions";
  end INCIDENCE_TABLE;
end IncidenceTable;

// Table having crefs as keys and corresponding SMNODE as value
type SMNodeTable = HashTableCrToSMNode.HashTable;

// Table mapping crefs of SMNodes to corresponding crefs of FlatSMGroup
type SMNodeToFlatSMGroupTable = HashTableCG.HashTable;

constant String SMS_PRE = "smOf" "prefix for flat State Machine names";

protected constant Boolean DEBUG_SMDUMP = true "enable verbose stdout debug information during elaboration";


public function createSMNodeToFlatSMGroupTable "
Author: BTH
Create table that associates a state instance with its governing flat state machine.
"
  input list<DAE.Element> elements;
  output SMNodeToFlatSMGroupTable smNodeToFlatSMGroup;
protected
  SMNodeTable smNodeTable;
  Integer nStates;
  IncidenceTable iTable, transClosure;
  list<DAE.ComponentRef> initialStates;
  list<FlatSMGroup> flatSMGroup;
algorithm
  if intLt(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33) then
    smNodeToFlatSMGroup := HashTableCG.emptyHashTableSized(1);
    return;
  end if;

  smNodeTable := getSMNodeTable(elements);
  nStates := BaseHashTable.hashTableCurrentSize(smNodeTable);

  if nStates > 0 then
    smNodeToFlatSMGroup := HashTableCG.emptyHashTable();

    if DEBUG_SMDUMP then print("***** InstStateMachineUtil.createSMNodeToFlatSMGroupTable: START ***** \n"); end if;
    if DEBUG_SMDUMP then print("***** State machine node table: ***** \n"); end if;
    if DEBUG_SMDUMP then BaseHashTable.dumpHashTable(smNodeTable); end if;

    if DEBUG_SMDUMP then print("***** Incidence Matrix: ***** \n"); end if;
    iTable := createIncidenceTable(smNodeTable, nStates);
    if DEBUG_SMDUMP then printIncidenceTable(iTable, nStates); end if;

    if DEBUG_SMDUMP then print("***** Transitive Closure: ***** \n"); end if;
    transClosure := transitiveClosure(iTable, nStates);
    if DEBUG_SMDUMP then printIncidenceTable(transClosure, nStates); end if;

    if DEBUG_SMDUMP then print("***** Initial States: ***** \n"); end if;
    initialStates := extractInitialStates(smNodeTable);
    if DEBUG_SMDUMP then print( stringDelimitList(List.map(initialStates, ComponentReference.printComponentRefStr), ", ") + "\n"); end if;

    if DEBUG_SMDUMP then print("***** Flat State Machine Groups: ***** \n"); end if;
    flatSMGroup := extractFlatSMGroup(initialStates, transClosure, nStates);
    if DEBUG_SMDUMP then print(stringDelimitList(List.map(flatSMGroup,dumpFlatSMGroupStr), "\n") + "\n"); end if;

    if DEBUG_SMDUMP then print("***** SM Node cref to SM Group cref mapping: ***** \n"); end if;
    smNodeToFlatSMGroup := List.fold(flatSMGroup, relateNodesToGroup, smNodeToFlatSMGroup);
    if DEBUG_SMDUMP then BaseHashTable.dumpHashTable(smNodeToFlatSMGroup); end if;

    if DEBUG_SMDUMP then print("***** InstStateMachineUtil.createSMNodeToFlatSMGroupTable: END ***** \n"); end if;
  else
    smNodeToFlatSMGroup := HashTableCG.emptyHashTableSized(1);
  end if;

end createSMNodeToFlatSMGroupTable;


public function getSMNodeTable "
Author: BTH
Traverse the equations, search for 'transition' and 'initialState' operators,
extract the state arguments from them and collect them in the table."
  input list<DAE.Element> elements;
  output SMNodeTable smNodeTable;
protected
  list<DAE.Element> elements2;
algorithm
  elements2 := list(e for e guard isSMStatement2(e) in elements);
  if not listEmpty(elements2) then
    smNodeTable := List.fold(elements2,  extractSMStates2, HashTableCrToSMNode.emptyHashTable());
  else
    smNodeTable := HashTableCrToSMNode.emptyHashTableSized(1);
  end if;
end getSMNodeTable;

protected function isSMStatement2 "
Author: BTH
Return true if element is a state machine statement, otherwise false"
  input DAE.Element inElement;
  output Boolean outIsSMStatement;
algorithm
  outIsSMStatement := match inElement
    local
      String name;

    case DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT(name)))
      then (name == "transition" or name == "initialState") and
           intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33);

    else false;
  end match;
end isSMStatement2;

protected function extractSMStates2 "
Author: BTH
Helper function to getSMNodeTable"
  input DAE.Element inElement;
  input SMNodeTable inTable;
  output SMNodeTable outTable = inTable;
algorithm

  outTable := match (inElement)
    local
      SMNode smnode1, smnode2;
      DAE.ComponentRef cref1, cref2;
      Boolean isInitial1, isInitial2;
      HashSet.HashSet edges1, edges2;
    case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("transition"),
      expLst=DAE.CREF(componentRef=cref1)::DAE.CREF(componentRef=cref2)::_))
      equation
        //print("InstStateMachineUtil.extractSMStates: transition("+ComponentReference.crefStr(cref1)+", "+ComponentReference.crefStr(cref2)+")\n");
        smnode1 = if BaseHashTable.hasKey(cref1, outTable)
          then BaseHashTable.get(cref1, outTable)
            else SMNODE(cref1, false, HashSet.emptyHashSet());
        SMNODE(_,isInitial1,edges1) = smnode1;
        edges1 = BaseHashSet.add(cref1, edges1);
        edges1 = BaseHashSet.add(cref2, edges1);
        smnode1 = SMNODE(cref1, isInitial1, edges1);
        outTable = BaseHashTable.add((cref1, smnode1), outTable);

        smnode2 = if BaseHashTable.hasKey(cref2, outTable)
          then BaseHashTable.get(cref2, outTable)
            else SMNODE(cref2, false, HashSet.emptyHashSet());
        SMNODE(_,isInitial2,edges2) = smnode2;
        edges2 = BaseHashSet.add(cref1, edges2);
        edges2 = BaseHashSet.add(cref2, edges2);
        smnode2 = SMNODE(cref2, isInitial2, edges2);
        outTable = BaseHashTable.add((cref2, smnode2), outTable);
      then outTable;
    case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("initialState"),
      expLst={DAE.CREF(componentRef=cref1)}))
      equation
        //print("InstStateMachineUtil.extractSMStates: initialState("+ComponentReference.crefStr(cref1)+")\n");
        smnode1 = if BaseHashTable.hasKey(cref1, outTable)
          then BaseHashTable.get(cref1, outTable)
            else SMNODE(cref1, true, HashSet.emptyHashSet());
        SMNODE(_,_,edges1) = smnode1;
        edges1 = BaseHashSet.add(cref1, edges1);
        smnode1 = SMNODE(cref1,true,edges1);
        outTable = BaseHashTable.add((cref1, smnode1), outTable);
      then outTable;
  end match;

end extractSMStates2;


protected function createIncidenceTable "
Author: BTH
Create incidence table showing which modes are connected by transitions."
  input SMNodeTable smNodes;
  input Integer nStates "Number of states";
  output IncidenceTable iTable;
protected
  HashTable.HashTable cref2index "Map cref to corresponding index in incidence matrix";
  Boolean incidence[nStates,nStates] "Incidence matrix showing which states are connected by transitions";
  array<Boolean> iRow;
  Integer n,m,i,j,k;
  DAE.ComponentRef cref;
  HashSet.HashSet edges;
  array<DAE.ComponentRef> crefs1,crefs2;
algorithm
  crefs1 := listArray(BaseHashTable.hashTableKeyList(smNodes));
  n := arrayLength(crefs1);
  cref2index := HashTable.emptyHashTableSized(n);
  assert(n == nStates, "Value of nStates needs to be equal to number of modes within mode table argument.");
  incidence := fill(false,n,n);

  for i in 1:n loop
    cref2index := BaseHashTable.addNoUpdCheck((crefs1[i], i), cref2index);
  end for;

  for i in 1:n loop
    SMNODE(edges=edges) := BaseHashTable.get(crefs1[i], smNodes);
    crefs2 := listArray(BaseHashSet.hashSetList(edges));
    m := arrayLength(crefs2);
    for j in 1:m loop
      cref := crefs2[j];
      k := BaseHashTable.get(cref, cref2index);
      incidence[i,k] := true;
    end for;
  end for;

  iTable := INCIDENCE_TABLE(cref2index, incidence);
end createIncidenceTable;

protected function printIncidenceTable "
Author: BTH
Print incidence table."
  input IncidenceTable iTable;
  input Integer nStates "Number of states";
protected
  HashTable.HashTable cref2index;
  Boolean incidence[nStates,nStates];
  list<tuple<DAE.ComponentRef, Integer>> entries;
  tuple<DAE.ComponentRef, Integer> entry;
  DAE.ComponentRef cref;
  Integer n,i,j,padn;
  array<Boolean> row;
  String str,pads;
  Boolean b;
algorithm
  INCIDENCE_TABLE(cref2index, incidence) := iTable;
  entries := BaseHashTable.hashTableList(cref2index);

  // sanity check:
  n := listLength(entries);
  assert(n == nStates, "Value of nStates needs to be equal to number of modes within state table argument.");

  entries := List.sort(entries, crefIndexCmp);
  for entry in entries loop
    (cref, i) := entry;
    print( ComponentReference.printComponentRefStr(cref) + ": " + intString(i) + "\n" );
  end for;

  pads := " ";
  padn := 8;
  // Print table header
  str := Util.stringPadRight("i", padn, pads);
  for i in 1:n loop
    str := str + Util.stringPadLeft(intString(i)+",", padn, pads);
  end for;
  print(str + "\n");
  // print incidence matrix rows
  for i in 1:n loop
    str := Util.stringPadRight(intString(i), padn, pads);
    for j in 1:n loop
      b := incidence[i,j];
      str := str + Util.stringPadLeft(boolString(b)+",", padn, pads);
    end for;
    print(str + "\n");
  end for;
end printIncidenceTable;

protected function crefIndexCmp "
Author: BTH
Compare the indices assigned to two crefs (helper function for sorting)"
  input tuple<DAE.ComponentRef, Integer> inElement1;
  input tuple<DAE.ComponentRef, Integer> inElement2;
  output Boolean inRes;
protected
  Integer i1, i2;
algorithm
  (_, i1) := inElement1;
  (_, i2) := inElement2;
  inRes := i1 > i2;
end crefIndexCmp;

protected function transitiveClosure "
Author: BTH
Compute the transitive closure over the transition relation between states.
This allows to group states that are part of the same (flat) state machine.
The function uses the Warshall's algorithm for that task, c.f.
http://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
or the more succinct (and potentially more readable) description
http://de.wikipedia.org/wiki/Warshall-Algorithmus
"
  input IncidenceTable iTable;
  input Integer nStates "Number of states";
  output IncidenceTable  transClosure;
protected
  HashTable.HashTable cref2index;
  Boolean incidence[nStates,nStates];
  Integer n,k,i,j;
  Boolean c;
algorithm
  INCIDENCE_TABLE(cref2index, incidence) := iTable;
  n := BaseHashTable.hashTableCurrentSize(cref2index);
  // sanity check:
  assert(n == nStates, "Value of nStates needs to be equal to number of states within state table argument.");

  // Warshall's algorithm for computing the transitive closure
  for k in 1:n loop
    for i in 1:n loop
      if incidence[i,k] then
        for j in 1:n loop
          if incidence[k,j] then
            incidence[i,j] := true;
          end if;
        end for;
      end if;
    end for;
  end for;

  transClosure := INCIDENCE_TABLE(cref2index, incidence);
end transitiveClosure;

protected function extractInitialStates "
Author: BTH
Return crefs of states declared as 'initialState'. "
  input SMNodeTable smNodeTable;
  output list<DAE.ComponentRef> initialStates;
protected
  list<tuple<DAE.ComponentRef, SMNode>> entries;
  tuple<DAE.ComponentRef, SMNode> e;
  DAE.ComponentRef cref;
  SMNode smNode;
  Boolean isInitial;
algorithm
  entries := BaseHashTable.hashTableList(smNodeTable);
  initialStates := {};
  for e in entries loop
    (cref, smNode) := e;
    SMNODE(isInitial=isInitial) := smNode;
    if isInitial then
      initialStates := cref::initialStates;
    end if;
  end for;
end extractInitialStates;


protected function extractFlatSMGroup "
Author: BTH
For each initial state extract the (flat) state machine group that is defined by the
transitive closure associated with that initial state."
  input list<DAE.ComponentRef> initialStates;
  input IncidenceTable iTable;
  input Integer nStates "Number of states";
  output list<FlatSMGroup> flatSMGroup;
protected
  HashTable.HashTable cref2index;
  Boolean incidence[nStates,nStates];
  list<tuple<DAE.ComponentRef, Integer>> entries;
  array<DAE.ComponentRef> i2cref;
  DAE.ComponentRef cref;
  list<DAE.ComponentRef> members;
  array<DAE.ComponentRef> membersArr;
  HashSet.HashSet memberSet;
  Integer n,i,j;
algorithm
  INCIDENCE_TABLE(cref2index, incidence) := iTable;
  n := BaseHashTable.hashTableCurrentSize(cref2index);
  // sanity check:
  assert(n == nStates, "Value of nStates needs to be equal to number of modes within state table argument.");

  entries := BaseHashTable.hashTableList(cref2index);
  entries := List.sort(entries, crefIndexCmp);
  //i2cref := arrayCreate(n, ComponentReference.makeDummyCref());
  i2cref := listArray(List.map(entries, Util.tuple21));

  flatSMGroup := {};
  for cref in initialStates loop
    i := BaseHashTable.get(cref, cref2index);
    members := {};
    for j in 1:n loop
      if incidence[i,j] then
        members := i2cref[j]::members;
      end if;
    end for;

    // Ensure uniquenes of entries
    memberSet := HashSet.emptyHashSetSized(listLength(members));
    memberSet := List.fold(members, BaseHashSet.add, memberSet);

    // Ensure that initialState comes first in array
    memberSet := BaseHashSet.delete(cref, memberSet);
    membersArr := listArray(cref :: BaseHashSet.hashSetList(memberSet));

    flatSMGroup := FLAT_SM_GROUP(cref, membersArr)::flatSMGroup;
  end for;

end extractFlatSMGroup;

public function dumpFlatSMGroupStr "
Author: BTH
Dump flat state machine group to string"
  input FlatSMGroup flatA;
  output String flatStr;
protected
  list<DAE.ComponentRef> crefs;
  String initialStateStr, statesStr;
  list<String> statesStrs;
  // FLAT_SM_GROUP fields
  DAE.ComponentRef initState;
  array<DAE.ComponentRef> states;
algorithm
  FLAT_SM_GROUP(initState=initState, states=states) := flatA;
  initialStateStr := ComponentReference.printComponentRefStr(initState);
  crefs := arrayList(states);
  statesStrs := List.map(crefs, ComponentReference.printComponentRefStr);
  statesStr := stringDelimitList(statesStrs, ", ");

  flatStr := initialStateStr+"( states("+statesStr+"))";
end dumpFlatSMGroupStr;

protected function relateNodesToGroup "
Author: BTH
Relate crefs of SMNodes with cref of the FlatSMGroup that it belongs to.
"
  input FlatSMGroup flatSMGroup;
  input SMNodeToFlatSMGroupTable inNodeToGroup;
  output SMNodeToFlatSMGroupTable outNodeToGroup = inNodeToGroup;
protected
  array<tuple<DAE.ComponentRef, DAE.ComponentRef>> nodeGroup;
  // FLAT_SM_GROUP
  DAE.ComponentRef initState;
  array<DAE.ComponentRef> states;
algorithm
  FLAT_SM_GROUP(initState, states) := flatSMGroup;
  nodeGroup := Array.map(states, function Util.makeTuple(inValue2=initState));
  outNodeToGroup := Array.fold(nodeGroup, BaseHashTable.add, outNodeToGroup);
end relateNodesToGroup;




/**************************************************************************************
 * wrapSMCompsInFlatSMs
 *************************************************************************************/

public function wrapSMCompsInFlatSMs "
Author: BTH
Wrap state machine components into corresponding flat state machine containers.
"
  input output list<DAE.Element> elements;
  input SMNodeToFlatSMGroupTable smNodeToFlatSMGroup;
  input list<DAE.ComponentRef> smInitialCrefs "every smInitialCrefs corresponds to a flat state machine group";
protected
  list<DAE.Element> elementLst1, elementLst2, smCompsLst, otherLst1, otherLst2, smTransitionsLst, flatSmLst, flatSMsAndMergingEqns;
algorithm
  //print("InstStateMachineUtil.wrapSMCompsInFlatSMs: smInitialCrefs: " + stringDelimitList(List.map(smInitialCrefs, ComponentReference.crefStr), ",") + "\n");
  //print("InstStateMachineUtil.wrapSMCompsInFlatSMs: smNodeToFlatSMGroup:\n"); BaseHashTable.dumpHashTable(smNodeToFlatSMGroup);


  // extract SM_COMPs
  (smCompsLst, otherLst1) := List.extractOnTrue(elements, isSMComp);

  // extract transition and initialState statements
  (smTransitionsLst, otherLst2) := List.extractOnTrue(otherLst1, isSMStatement2);

  // Create list of FLAT_SM(..). Every FLAT_SM contains the components that constitute that flat state machine
  //flatSmLst := List.map2(smInitialCrefs, createFlatSM, smCompsLst, smNodeToFlatSMGroup);
  flatSmLst := List.map2(smInitialCrefs, createFlatSM, listAppend(smCompsLst, smTransitionsLst), smNodeToFlatSMGroup);
  /*
  // Merge variable definitions in flat state machine and create elements list containing FLAT_SMs and merging equations
  // flatSMsAndMergingEqns := List.fold1(flatSmLst, mergeVariableDefinitions, inIH, {});
  */

  //elements := listAppend(flatSMsAndMergingEqns, otherLst1);
  elements := listAppend(flatSmLst, otherLst1);
end wrapSMCompsInFlatSMs;


protected function isSMComp "
Author: BTH
Check if element is a SM_COMP.
"
  input DAE.Element inElement;
  output Boolean outResult;
algorithm
  outResult := match (inElement)
    case DAE.SM_COMP(_,_) then true;
    else false;
  end match;
end isSMComp;


protected function createFlatSM "
Author: BTH
Helper function to wrapSMCompsInFlatSMs.
"
  input DAE.ComponentRef smInitialCref;
  input list<DAE.Element> smElemsLst;
  input SMNodeToFlatSMGroupTable smNodeToFlatSMGroup;
  output DAE.Element flatSM;
protected
  list<DAE.Element> smElemsInFlatSM;
algorithm
  smElemsInFlatSM := List.filter2OnTrue(smElemsLst, isInFlatSM, smInitialCref, smNodeToFlatSMGroup);
  flatSM := DAE.FLAT_SM(ComponentReference.printComponentRefStr(smInitialCref), smElemsInFlatSM);
end createFlatSM;

protected function isInFlatSM "
Author: BTH
Check if SM_COMP, transition or initialState (first argument) is part of the flat state machine which corresponds to smInitialCref.
"
  input DAE.Element inElement;
  input DAE.ComponentRef smInitialCref;
  input SMNodeToFlatSMGroupTable smNodeToFlatSMGroup "Table which maps the cref of an SM_COMP to the cref of its corresponding flat state machine group";
  output Boolean outResult;
protected
  DAE.ComponentRef crefCorrespondingFlatSMGroup;
algorithm
  crefCorrespondingFlatSMGroup := match inElement
    local
      DAE.ComponentRef cref1;
    case DAE.SM_COMP(componentRef=cref1) guard BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup)
      then BaseHashTable.get(cref1, smNodeToFlatSMGroup);
    case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("transition"),
      expLst=DAE.CREF(componentRef=cref1)::_)) guard BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup)
      // Note that it suffices to check for the "from" state, since the "to" state must be in the same FlatSMGroup
      then BaseHashTable.get(cref1, smNodeToFlatSMGroup);
    case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("initialState"),
      expLst={DAE.CREF(componentRef=cref1)})) guard BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup)
      then BaseHashTable.get(cref1, smNodeToFlatSMGroup);
    else
      algorithm
      	BaseHashTable.dumpHashTableStatistics(smNodeToFlatSMGroup);
      	assert(false, "- InstStateMachineUtil.isInFlatSM failed: Hash table lookup failed for " + DAEDump.dumpElementsStr({inElement}));
      then fail();
  end match;

  outResult := if ComponentReference.crefEqual(crefCorrespondingFlatSMGroup, smInitialCref) then true else false;
end isInFlatSM;















/**************************************************************************************
 * BELOW NOT NEEDED
 *************************************************************************************/

public function getSMStatesInContext "
Author: BTH
Return list of states defined in current context (by checking 'transtion' and 'initialState' operators)"
  input list<DAE.Element> elements;
  input Prefix prefix;
  output list<DAE.ComponentRef> states "Initial and non-initial states";
  output list<DAE.ComponentRef> initialStates "Only initial states";
protected
  list<SCode.Equation> eqns1;
  list<list<Absyn.ComponentRef>> statesLL;
  list<Absyn.ComponentRef> initialStatesCR, statesCR;
algorithm

	(states, initialStates) := List.fold20(elements, foldSMStates, {}, {});

/*
  eqns1 := list(elem for elem guard isSMStatement(elem) in elements);

  // Extract initial states
  initialStatesCR := List.filterMap(eqns1, extractInitialSMStates);
  initialStates := List.map(initialStatesCR, ComponentReference.toExpCref);
  // prefix the names
  initialStates := List.map1(initialStates, prefixCrefNoContext2, inPrefix);
  // 01.06.2015 Strange. I get a compile error if using below instead of above AND removing prefixCrefNoContext2(..) function definitions
  // initialStates := List.map(initialStates, function PrefixUtil.prefixCrefNoContext(inPre=inPrefix));

  // Extract states (initial as well as non-initial)
  statesLL := List.map(eqns1, extractSMStates);
  statesCR := List.flatten(statesLL);
  states := List.map(statesCR, ComponentReference.toExpCref);
  // prefix the names
  states := List.map(states, function PrefixUtil.prefixCrefNoContext(inPre=inPrefix));
  */
end getSMStatesInContext;

protected function foldSMStates
    input DAE.Element element;
    input list<DAE.ComponentRef> inStates;
    input list<DAE.ComponentRef> inInitialStates;
    output list<DAE.ComponentRef> outStates;
    output list<DAE.ComponentRef> outInitialStates;
algorithm
	(outStates, outInitialStates) := match element
		local
			String name;
			DAE.ComponentRef cr1, cr2;
		case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("initialState"), expLst={DAE.CREF(componentRef=cr1)}))
			guard intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33)
			then (cr1::inStates, cr1::inInitialStates);
		case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT("transition"), expLst=DAE.CREF(componentRef=cr1)::DAE.CREF(componentRef=cr2)::_))
			guard intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33)
			then (cr1::inStates, inInitialStates);
		else (inStates, inInitialStates);
	end match;
end foldSMStates;


/*
protected function isSMStatement "
Author: BTH
Return true if element is a state machine statement, otherwise false"
  input DAE.Element element;
  output Boolean isSMStatement;
algorithm
  isSMStatement := match element
    local
      String name;
    case DAE.NORETCALL(exp=DAE.CALL(path=Absyn.IDENT(name)))
    	guard intGe(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33)
    		and (name == "initialState" or name == "initialState")
    	then true;
    else false;
  end match;
end isSMStatement;
*/

annotation(__OpenModelica_Interface="frontend");
end NFInstStateMachineUtil;