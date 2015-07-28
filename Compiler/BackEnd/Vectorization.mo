/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
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

encapsulated package Vectorization
" file:        Vectorization.mo
  package:     Vectorization
  description: Vectorization

  RCS: $Id: Vectorization.mo 2013-05-24 11:12:35Z vwaurich $
"
public import BackendDAE;
public import DAE;

protected import Absyn;
protected import Algorithm;
protected import Array;
protected import BackendArrayVarTransform;
protected import BackendDAEUtil;
protected import BackendDump;
protected import BackendEquation;
protected import BackendDAEEXT;
protected import BackendDAETransform;
protected import BackendVariable;
protected import BackendVarTransform;
protected import ComponentReference;
protected import Dump;
protected import ExpressionDump;
protected import ExpressionSimplify;
protected import ExpressionSolve;
protected import HpcOmEqSystems;
protected import List;
protected import Matching;
protected import SCode;
protected import SCodeDump;
protected import SimCode;
protected import SimCodeVar;
protected import Tearing;
protected import Util;



//--------------------------------
// collect for-loops
//--------------------------------

public function collectForLoops
  input list<BackendDAE.Var> varsIn;
  input list<BackendDAE.Equation> eqsIn;
  output list<BackendDAE.Var> varsOut;
  output list<BackendDAE.Equation> eqsOut;
protected
  Boolean cont, perfectMatching;
  Integer idx, numEqs, numVars;
  array<Integer> ass1,ass2;
  list<Integer> idxs;
  BackendDAE.EqSystem eqSys;
  BackendDAE.Shared shared;
  BackendVarTransform.VariableReplacements repl1;
  DAE.ComponentRef cref;
  DAE.Exp exp;
  list<DAE.ComponentRef> scalarCrefs,scalarCrefs1,scalarCrefs2, allScalarCrefs, stateCrefs;
  list<DAE.Exp> scalarCrefExps;
  list<BackendDAE.Equation> loopEqs;
  list<BackendDAE.Var> arrVars;
  list<Absyn.Exp> loopIds;
  list<BackendDAE.LoopInfo> loopInfos;
  list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> arrayCrefs; //headCref, range, tailcrefs
  list<BackendDAE.Var> varLst, arrayVars;
  list<BackendDAE.Equation> forEqs,mixEqs,nonArrEqs;

algorithm
    //BackendDump.dumpEquationList(eqsIn,"eqsIn");
    //BackendDump.dumpVarList(varsIn,"varsIn");

  //-------------------------------------------
  //dispatch vars and equals to different lists
  //-------------------------------------------

  //split vars in array vars and non array vars
  (varLst, arrayVars) := List.fold(varsIn, getArrayVars,({},{}));

  // get the arrayCrefs
  (arrayCrefs,_) := List.fold(arrayVars,getArrayVarCrefs,({},{}));

  // dispatch the equations in for-quations, mixedequations, non-array equations
  ((forEqs,mixEqs,nonArrEqs)) := List.fold1(eqsIn, dispatchLoopEquations,List.map(arrayCrefs,Util.tuple31),({},{},{}));
      //BackendDump.dumpEquationList(forEqs,"forEqs1");
      //BackendDump.dumpEquationList(mixEqs,"mixEqs1");
      //BackendDump.dumpEquationList(nonArrEqs,"nonArrEqs1");

  //build for equations for repeated equations
  forEqs := buildBackendDAEForEquations(forEqs,{});

  //find accumulated equations in mixEqs and insert SUM-Exp
  mixEqs := listReverse(List.fold(mixEqs,buildAccumExpInEquations,{}));
      //BackendDump.dumpEquationList(forEqs,"forEqs2");
      //BackendDump.dumpEquationList(mixEqs,"mixEqs2");
      //BackendDump.dumpEquationList(nonArrEqs,"nonArrEqs2");

  // build non-expanded arrays
  arrayVars := unexpandArrayVariables(arrayVars,{});

  eqsOut := listAppend(forEqs,listAppend(mixEqs, nonArrEqs));
  varsOut := listAppend(arrayVars,varLst);

end collectForLoops;

//--------------------------------
//removeSimpleEquations
//--------------------------------

public function removeSimpleEquationsInForEquations"scalarized everythin in the backenddae"
  input BackendDAE.BackendDAE daeIn;
  output BackendDAE.BackendDAE daeOut;
algorithm
  daeOut := BackendDAEUtil.mapEqSystem(daeIn,removeSimpleEquationsInForEquations1);
end removeSimpleEquationsInForEquations;

protected function removeSimpleEquationsInForEquations1
  input BackendDAE.EqSystem sysIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem sysOut;
  output BackendDAE.Shared sharedOut;
protected
  Boolean cont;
  Integer numEqs;
  BackendDAE.EquationArray eqs, reqs;
  BackendDAE.Variables vars, knownVars, aliasVars;
  BackendVarTransform.VariableReplacements repl1;
  list<DAE.ComponentRef> scalarCrefs1,scalarCrefs2,allScalarCrefs;
  list<BackendDAE.Equation> forEqs,mixEqs,nonArrEqs, eqsOut;
  list<BackendDAE.Var> varLst, arrayVars, varsOut, knVarsOut, aliasVarsOut;

  BackendDAE.IncidenceMatrix m,mT;
  list<tuple<Boolean,String>> varAtts,eqAtts;
algorithm
  BackendDAE.EQSYSTEM(orderedVars = vars, orderedEqs=eqs) := sysIn;
  BackendDAE.SHARED(knownVars=knownVars, aliasVars=aliasVars, removedEqs=reqs) := sharedIn;

  // dispatch the equations in for-quations, mixedequations, non-array equations and the vars in array and non-array vars
  ((forEqs,mixEqs,nonArrEqs)) := List.fold(BackendEquation.equationList(eqs), classifyLoopEquations,({},{},{}));
  (arrayVars, varLst) := List.separateOnTrue(BackendVariable.varList(vars), BackendVariable.isRangeVar);

  //-------------------------------------------
  //apply replacements for non-array equations and for-equations
  //-------------------------------------------
  repl1 := BackendVarTransform.emptyReplacements();
  cont := true;

  while cont loop
    numEqs := listLength(nonArrEqs)+listLength(forEqs);
    //find alias statements in non-array equations
    (nonArrEqs, repl1) := removeSimpleEquationsWithFor(nonArrEqs,BackendVariable.listVar1(varLst),SOME(repl1));
    //find alias statements in for equations
    (forEqs, repl1) := removeSimpleEquationsWithFor(forEqs,BackendVariable.listVar1(arrayVars),SOME(repl1));
    cont := intNe(listLength(nonArrEqs)+listLength(forEqs),numEqs);
  end while;

      //BackendDump.dumpEquationList(forEqs,"forEqs3");
      //BackendDump.dumpEquationList(nonArrEqs,"nonArrEqs3");
      //BackendDump.dumpEquationList(mixEqs,"mixEqs3");
      //BackendVarTransform.dumpReplacements(repl1);

  //-------------------------------------------
  //apply replacements for mixed-equations
  //-------------------------------------------

  cont := true;
  while cont loop
    numEqs := listLength(nonArrEqs)+listLength(forEqs)+listLength(mixEqs);
    // apply replacements on mixed eqs
    (mixEqs,_) := BackendVarTransform.replaceEquations(mixEqs,repl1,NONE());
     //find alias statements in mixed equations
    (mixEqs, repl1) := removeSimpleEquationsWithFor(mixEqs,BackendVariable.listVar1(arrayVars),SOME(repl1));
      //BackendDump.dumpEquationList(mixEqs,"mixEqs3.1");
      //BackendVarTransform.dumpReplacements(repl1);
    //try the replacements in the for equations and non-array equations again
    (forEqs, repl1) := removeSimpleEquationsWithFor(forEqs,BackendVariable.listVar1(arrayVars),SOME(repl1));
    (nonArrEqs, repl1) := removeSimpleEquationsWithFor(nonArrEqs,BackendVariable.listVar1(arrayVars),SOME(repl1));
    cont := intNe(listLength(nonArrEqs)+listLength(mixEqs)+listLength(forEqs),numEqs);
  end while;

      //BackendDump.dumpEquationList(forEqs,"forEqs4");
      //BackendDump.dumpEquationList(nonArrEqs,"nonArrEqs4");
      //BackendDump.dumpEquationList(mixEqs,"mixEqs4");
      //BackendVarTransform.dumpReplacements(repl1);

  //-------------------------------------------
  //slice what has to be sliced because the replacement rules demand it and the mixed eqs, too
  //-------------------------------------------

  //get scalar crefs from replacements
  scalarCrefs1 := getScalarArrayCrefsFromReplacements(repl1);
  scalarCrefs2 := List.fold(mixEqs,getScalarArrayCrefsFromEquation,{});
      //print("\nscalarCrefs from repl: \n"+stringDelimitList(List.map(scalarCrefs1,ComponentReference.printComponentRefStr),"\n")+"\n");
      //print("scalarCrefs from mixed: \n"+stringDelimitList(List.map(scalarCrefs2,ComponentReference.printComponentRefStr),"\n")+"\n");
  scalarCrefs1 := listAppend(scalarCrefs1,scalarCrefs2);

  //split equations and apply replacements
  (forEqs,scalarCrefs2) := List.fold2(forEqs,splitForEquations,scalarCrefs1,{},({},{}));
  (forEqs,_) := BackendVarTransform.replaceEquations(forEqs,repl1,NONE());
      //print("scalarCrefs from splitforeqs"+": \n"+stringDelimitList(List.map(scalarCrefs2,ComponentReference.printComponentRefStr),"\n")+"\n");
      //BackendDump.dumpEquationList(forEqs,"forEqs4_0");

  //split array-vars for the scalarcrefs
  arrayVars := List.fold(scalarCrefs1,sliceArrayVarsForCref,arrayVars);
    //BackendDump.dumpVariables(BackendVariable.listVar1(arrayVars),"arrayVars2");

  //-------------------------------------------
  //slice more stuff
  //-------------------------------------------
  /*
  allScalarCrefs := scalarCrefs2;
  for i in List.intRange(0) loop
    //split for-equations
    print("SPLIT EQUATIONS ROUND "+intString(i)+"\n");
  (forEqs,_) := BackendVarTransform.replaceEquations(forEqs,repl1,NONE());
  (forEqs,scalarCrefs2) := List.fold1(forEqs,splitForEquations,scalarCrefs2,({},{}));
  allScalarCrefs := listAppend(scalarCrefs2,allScalarCrefs);
    BackendDump.dumpEquationList(forEqs,"forEqs4_"+intString(i));
    print("scalarCrefs2_"+intString(i)+": \n"+stringDelimitList(List.map(scalarCrefs1,ComponentReference.printComponentRefStr),"\n")+"\n");
  end for;
    //print("allScalarCrefs: \n"+stringDelimitList(List.map(allScalarCrefs,ComponentReference.printComponentRefStr),"\n")+"\n");

  //apply replacements again
  (forEqs,_) := BackendVarTransform.replaceEquations(forEqs,repl1,NONE());
  (nonArrEqs,_) := BackendVarTransform.replaceEquations(nonArrEqs,repl1,NONE());
  (mixEqs,_) := BackendVarTransform.replaceEquations(mixEqs,repl1,NONE());
      BackendDump.dumpEquationList(forEqs,"forEqs5");
      BackendDump.dumpEquationList(nonArrEqs,"nonArrEqs5");
      BackendDump.dumpEquationList(mixEqs,"mixEqs5");

  //split array-vars for the scalarcrefs
  arrayVars := List.fold(allScalarCrefs,sliceArrayVarsForCref,arrayVars);
  //BackendDump.dumpVariables(BackendVariable.listVar1(arrayVars),"arrayVars2") ;
*/

  //-------------------------------------------
  //gather constant and alias vars
  //-------------------------------------------
  eqsOut := listAppend(listAppend(nonArrEqs,listAppend(forEqs,mixEqs)));
  (reqs,_) := BackendVarTransform.replaceEquationsArr(reqs,repl1,NONE());

  varLst := listAppend(arrayVars,varLst);
  (varsOut,knVarsOut, aliasVarsOut) := assignAliasVars(repl1, varLst);

  //scalarize alias and known
  (_,aliasVarsOut) := List.mapFold(aliasVarsOut,scalarizeVar,{});
  (_,knVarsOut) :=  List.mapFold(knVarsOut,scalarizeVar,{});
  aliasVarsOut :=  List.map1(aliasVarsOut,BackendVarTransform.replaceBindingExp,repl1);
  knVarsOut :=  List.map1(knVarsOut,BackendVarTransform.replaceBindingExp,repl1);

  aliasVars := BackendVariable.addVars(aliasVarsOut,aliasVars);
  knownVars := BackendVariable.addVars(knVarsOut,knownVars);

  sharedOut := BackendDAEUtil.setSharedAliasVars(sharedIn, aliasVars);
  sharedOut := BackendDAEUtil.setSharedKnVars(sharedOut, knownVars);
  sharedOut := BackendDAEUtil.setSharedRemovedEqns(sharedOut, reqs);
  sysOut := BackendDAEUtil.setEqSystVars(sysIn, BackendVariable.listVar1(varsOut));
  sysOut := BackendDAEUtil.setEqSystEqs(sysOut, BackendEquation.listEquation(eqsOut));

  //-------------------------------------------
  //build an incidence matrix
  //-------------------------------------------
  (m,mT) := BackendDAEUtil.incidenceMatrix(sysOut,BackendDAE.NORMAL(),NONE());
  varAtts := List.fill((true,"JO"),listLength(varLst));
  eqAtts := List.fill((true,"JO"),listLength(eqsOut));
  HpcOmEqSystems.dumpEquationSystemBipartiteGraph2(BackendVariable.listVar1(varsOut),BackendEquation.listEquation(eqsOut),m,varAtts,eqAtts,"BipartiteGraph_AFTER_REPL");
end removeSimpleEquationsInForEquations1;


protected function classifyLoopEquations"calssifies an equation to either forEqs, mixeqs or nonarrayEqs"
  input BackendDAE.Equation eqIn;
  input tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tplIn; //forEqs,mixEqs,nonArrEqs
  output tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tplOut;//forEqs,mixEqs,nonArrEqs
algorithm
  tplOut := matchcontinue(eqIn,tplIn)
    local
      list<BackendDAE.Equation> forEqs,mixEqs,nonArrEqs;
      list<DAE.ComponentRef> crefs;
      tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tpl;

    case(BackendDAE.FOR_EQUATION(),(forEqs,mixEqs,nonArrEqs))
      then (eqIn::forEqs,mixEqs,nonArrEqs);

    case(_,(forEqs,mixEqs,nonArrEqs))
      equation
        crefs = BackendEquation.equationCrefs(eqIn);
        if List.exist(crefs,ComponentReference.crefHaveSubs) then
          mixEqs = eqIn::mixEqs;
        else
          nonArrEqs = eqIn::nonArrEqs;
        end if;
      then (forEqs,mixEqs,nonArrEqs);
  end matchcontinue;
end classifyLoopEquations;

//--------------------------------
// causalize system
//--------------------------------


public function causalizeForEquations "Gets a matching and a BLT-matrix for the BackendDAE with for-equations"
  input BackendDAE.BackendDAE inDAE;
  output BackendDAE.BackendDAE outDAE;
protected
  BackendDAE.EqSystems eqs;
  BackendDAE.Shared shared;
algorithm
  BackendDAE.DAE(eqs=eqs, shared=shared) := inDAE;
  (eqs,shared) := List.mapFold(eqs,causalizeForEquations1,shared);
  outDAE := BackendDAE.DAE(eqs,shared);
end causalizeForEquations;

protected function causalizeForEquations1"Gets a matching and a BLT-matrix for an eqSystem with for-equations"
  input BackendDAE.EqSystem sysIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem sysOut;
  output BackendDAE.Shared sharedOut;
protected
  Boolean perfectMatching;
  Integer numEqs, numVars, i;
  array<Integer> ass1, ass2, mapIncRowEqn;
  array<list<Integer>> mapEqnIncRow;
  DAE.ComponentRef cref;
  BackendDAE.StrongComponents comps;
  BackendDAE.EquationArray eqs;
  BackendDAE.EqSystem sys, sys_for;
  BackendDAE.IncidenceMatrix m;
  BackendDAE.IncidenceMatrixT mT;
  BackendDAE.Var var;
  BackendDAE.Variables vars;
  BackendDAE.StateSets stateSets;
  BackendDAE.BaseClockPartitionKind partitionKind;
  list<DAE.ComponentRef> stateCrefs;
  list<BackendDAE.Equation> eqLst, forEqs,mixEqs,nonArrEqs, slicedEqs;
  list<BackendDAE.Var> varLst0, varLst, slicedVars;

  list<tuple<Boolean,String>> varAtts,eqAtts;
algorithm
  //print("causalize!\n");
  BackendDAE.EQSYSTEM(orderedVars = vars, orderedEqs = eqs, stateSets=stateSets, partitionKind=partitionKind) := sysIn;
  eqLst := BackendEquation.equationList(eqs);
  varLst0 := BackendVariable.varList(vars);

  //get the states
  //-------------
        //BackendDump.dumpEquationList(eqLst,"eqLst1");

  (_,stateCrefs) := BackendEquation.traverseExpsOfEquationList(eqLst,collectStatesAndTransformDerCall,{});
        //BackendDump.dumpEquationList(eqLst,"eqLst2");

    //print("stateCrefs: \n"+stringDelimitList(List.map(stateCrefs,ComponentReference.printComponentRefStr),"\n")+"\n");

  varLst := {};
  for var in varLst0 loop
   if List.exist1(stateCrefs,ComponentReference.crefEqualWithoutSubs,BackendVariable.varCref(var)) then
     //cref := ComponentReference.crefPrefixDer(BackendVariable.varCref(var));
     //var := BackendVariable.copyVarNewName(cref,var);
     var := BackendVariable.setVarKind(var, BackendDAE.STATE(1,NONE()));
   end if;
     varLst := var::varLst;
  end for;

  vars := BackendVariable.listVar1(varLst);
  eqs := BackendEquation.listEquation(eqLst);
  sys := BackendDAE.EQSYSTEM(vars, eqs,NONE(), NONE(), BackendDAE.NO_MATCHING(),  stateSets, partitionKind);
    //BackendDump.dumpEqSystem(sys,"REPLACED STATES");

  //dump graph
  //-------------
  /*
  ((forEqs,mixEqs,nonArrEqs)) := List.fold(BackendEquation.equationList(eqs), classifyLoopEquations,({},{},{}));
  sys_for := BackendDAE.EQSYSTEM(BackendVariable.listVar1(varLst),BackendEquation.listEquation(forEqs),NONE(),NONE(),BackendDAE.NO_MATCHING(), stateSets,partitionKind);
  (m,mT) := BackendDAEUtil.incidenceMatrix(sys_for,BackendDAE.NORMAL(),NONE());
  varAtts := List.fill((true,"JO"),listLength(varLst));
  eqAtts := List.fill((true,"JO"),listLength(forEqs));
  HpcOmEqSystems.dumpEquationSystemBipartiteGraph2(BackendVariable.listVar1(varLst),BackendEquation.listEquation(forEqs),m,varAtts,eqAtts,"BipartiteGraph_SYS_FOR");
*/
  (m,mT) := BackendDAEUtil.incidenceMatrix(sys,BackendDAE.ABSOLUTE(),NONE());
  varAtts := List.fill((true,"JO"),listLength(BackendVariable.varList(vars)));
  eqAtts := List.fill((true,"JO"),listLength(BackendEquation.equationList(eqs)));
  HpcOmEqSystems.dumpEquationSystemBipartiteGraph2(vars,eqs,m,varAtts,eqAtts,"BipartiteGraph_CAUSAL_VEC");

  //slice vars and equations to make everything fit together
  //-------------
  for i in List.intRange(3) loop
     //print("SLICING ROUND "+intString(i)+"\n");
    sys := BackendDAE.EQSYSTEM(vars, eqs,NONE(), NONE(), BackendDAE.NO_MATCHING(),  stateSets, partitionKind);
      //BackendDump.dumpVariables(vars,"before split vars");
      //BackendDump.dumpEquationArray(eqs,"before split equations");
    (m,mT) := BackendDAEUtil.incidenceMatrix(sys,BackendDAE.NORMAL(),NONE());
      //BackendDump.dumpIncidenceMatrix(m);
      //BackendDump.dumpIncidenceMatrixT(mT);
    (slicedEqs,slicedVars) := slicePartially(m,mT,eqs,vars,stateCrefs);
    eqs := BackendEquation.listEquation(slicedEqs);
    vars := BackendVariable.listVar(slicedVars);
  end for;

  sys_for := BackendDAE.EQSYSTEM(vars,eqs,NONE(),NONE(),BackendDAE.NO_MATCHING(), stateSets,partitionKind);
  (m,mT) := BackendDAEUtil.incidenceMatrix(sys_for,BackendDAE.NORMAL(),NONE());
  varAtts := List.fill((true,"JO"),listLength(slicedVars));
  eqAtts := List.fill((true,"JO"),listLength(slicedEqs));
  HpcOmEqSystems.dumpEquationSystemBipartiteGraph2(vars,eqs,Array.map1(m,Tearing.deleteNegativeEntries,1),varAtts,eqAtts,"BipartiteGraph_SLICED");

  //match the system, get components
  //-------------
  numEqs := BackendDAEUtil.equationArraySize(eqs);
  numVars := BackendVariable.varsSize(vars);
  sys := BackendDAE.EQSYSTEM(vars, eqs,NONE(), NONE(), BackendDAE.NO_MATCHING(),  stateSets, partitionKind);
  (m,mT) := BackendDAEUtil.incidenceMatrix(sys,BackendDAE.NORMAL(),NONE());
    //print("nEqs "+intString(numEqs)+" numVars "+intString(numVars)+"\n");
    //BackendDump.dumpEqSystem(sys,"SLICED System");

  ass1 := arrayCreate(numVars, -1);
  ass2 := arrayCreate(numEqs, -1);
  Matching.matchingExternalsetIncidenceMatrix(numVars, numEqs, m);
  BackendDAEEXT.matching(numVars, numEqs, 5, 0, 0.0, 1);
  BackendDAEEXT.getAssignment(ass2, ass1);
  perfectMatching := listEmpty(Matching.getUnassigned(numVars, ass1, {}));
  sys := BackendDAE.EQSYSTEM(vars, eqs, SOME(m), SOME(mT), BackendDAE.MATCHING(ass1,ass2,{}), stateSets, partitionKind);
    //BackendDump.dumpEqSystem(sys,"CAUSALIZE_SYSTEM");
    //print("matching is perfect "+ boolString(perfectMatching) +"\n");

  // perform BLT to order the StrongComponents
  mapIncRowEqn := listArray(List.intRange(numEqs));
  mapEqnIncRow := Array.map(mapIncRowEqn,List.create);
  (sysOut,comps) := BackendDAETransform.strongComponentsScalar(sys,sharedIn,mapEqnIncRow,mapIncRowEqn);
    //BackendDump.dumpEqSystem(sysOut,"CAUSALIZED_SYSTEM");

  sharedOut := sharedIn;
end causalizeForEquations1;

protected function slicePartially
  input BackendDAE.IncidenceMatrix m;
  input BackendDAE.IncidenceMatrix mT;
  input BackendDAE.EquationArray eqArr;
  input BackendDAE.Variables varArr;
  input list<DAE.ComponentRef> states;
  output list<BackendDAE.Equation> eqsOut;
  output list<BackendDAE.Var> varsOut;
protected
  Integer varIdx;
  list<Integer> eqIdcs;
  BackendDAE.Var var;
  DAE.ComponentRef varName;
  list<BackendDAE.Equation> eqs, forEqs;
  list<DAE.ComponentRef> crefs, scalarCrefs={};
algorithm
  for varIdx in List.intRange(arrayLength(mT)) loop
    eqIdcs := arrayGet(mT,varIdx);
    eqIdcs := List.filterOnTrue(eqIdcs, Util.intPositive);
    //print("varIdx "+intString(varIdx)+" eqidcs  "+stringDelimitList(List.map(eqIdcs,intString),",")+"\n");
    var := BackendVariable.getVarAt(varArr,varIdx);
    if BackendVariable.isRangeVar(var) then
      eqs := BackendEquation.getEqns(eqIdcs,eqArr);
      //print(" eqs:\n"+BackendDump.equationListString(eqs,"")+"\n");
      forEqs := List.filterOnTrue(eqs,BackendEquation.isForEquation);
      forEqs := List.map(forEqs,insertRangeInForEquation);
      varName := BackendVariable.varCref(var);
      //print("VAR: "+BackendDump.varString(var)+" occures in for eqs:\n"+BackendDump.equationListString(forEqs,"")+"\n");
      //get the subscripts to be split
      for eq in forEqs loop
        crefs := BackendEquation.equationCrefs(eq);
        crefs := List.filter1OnTrue(crefs,ComponentReference.crefEqualWithoutSubs,varName);
        //print("cref: "+stringDelimitList(List.map(crefs,ComponentReference.printComponentRefStr),",")+"\n");
        // get the scalar crefs to be split
        if listLength(crefs)==1 then
          (varName,scalarCrefs) := List.fold(crefs,compareRangesAndSlice,(varName,scalarCrefs));
        end if;
      end for;
        //print("new VAR "+ComponentReference.printComponentRefStr(varName)+"   scalarCrefs: "+stringDelimitList(List.map(scalarCrefs,ComponentReference.printComponentRefStr),",")+"\n\n");
    end if;
  end for;

  //split equations and apply replacements
  (eqsOut,_) := List.fold2(BackendEquation.equationList(eqArr),splitForEquations,scalarCrefs,states,({},{}));
  //split array-vars for the scalarcrefs
  varsOut := List.fold(scalarCrefs,sliceArrayVarsForCref,BackendVariable.varList(varArr));
end slicePartially;


protected function compareRangesAndSlice
  input DAE.ComponentRef crefIn;
  input tuple<DAE.ComponentRef,list<DAE.ComponentRef>> tplIn;
  output tuple<DAE.ComponentRef,list<DAE.ComponentRef>> tplOut;
algorithm
  tplOut := matchcontinue(crefIn,tplIn)
    local
      Integer start1, start2, stop1, stop2;
      DAE.ComponentRef cref1,cref2;
      DAE.Type ty;
      list<DAE.ComponentRef> scalars;
    case(_,(cref1,scalars))
      algorithm
        {DAE.INDEX(DAE.RANGE(ty=ty, start=DAE.ICONST(start1), stop=DAE.ICONST(stop1)))} := ComponentReference.crefSubs(cref1);
        {DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start2), stop=DAE.ICONST(stop2)))} := ComponentReference.crefSubs(crefIn);
        if start1==start2-1 and stop1==stop2 then //cut first
          cref1 := replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(start2), NONE(),DAE.ICONST(stop1)))});
          scalars := replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.ICONST(start1))})::scalars;
        elseif start1==start2 and stop1==stop2+1 then //cut last
          cref1 := replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(start1), NONE(),DAE.ICONST(stop2)))});
          scalars := replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.ICONST(stop1))})::scalars;
        elseif start1==start2-1 and stop1==stop2+1 then //cut last and first
          cref1 := replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(start2), NONE(),DAE.ICONST(stop2)))});
          scalars := listAppend({replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.ICONST(start1))}),replaceFirstSubsInCref(cref1,{DAE.INDEX(DAE.ICONST(stop1))})},scalars);
        else
          cref1 := cref1;
          scalars := scalars;
        end if;
      then (cref1,scalars);
    else
      then tplIn;
  end matchcontinue;
end compareRangesAndSlice;

protected function collectStatesAndTransformDerCall"traverses all equations, collects states and replaces der-calls"
  input DAE.Exp inExp;
  input list<DAE.ComponentRef> statesIn;
  output DAE.Exp outExp;
  output list<DAE.ComponentRef> statesOut;
algorithm
  (outExp,statesOut) := Expression.traverseExpBottomUp(inExp,collectStatesAndTransformDerCall1,statesIn);
end collectStatesAndTransformDerCall;

protected function collectStatesAndTransformDerCall1"traverses all equations, collects states and replaces der-calls"
  input DAE.Exp inExp;
  input list<DAE.ComponentRef> statesIn;
  output DAE.Exp outExp;
  output list<DAE.ComponentRef> statesOut;
algorithm
  (outExp,statesOut) := matchcontinue(inExp,statesIn)
    local
      DAE.ComponentRef cr;
      DAE.Exp cref_exp;
  case(DAE.CALL(path=Absyn.IDENT(name = "der"), expLst={DAE.CREF(componentRef=cr)}),_)
    equation
      cref_exp = Expression.crefExp(ComponentReference.crefPrefixDer(cr));
    then (cref_exp, cr::statesIn);
  else
    then(inExp,statesIn);
  end matchcontinue;
end collectStatesAndTransformDerCall1;

//-----------------------------------------------
// dispatch vars to const, alias and normal vars
//-----------------------------------------------

protected function assignAliasVars
  input BackendVarTransform.VariableReplacements repl;
  input list<BackendDAE.Var> varsIn;
  output list<BackendDAE.Var> varLst={};
  output list<BackendDAE.Var> constLst={};
  output list<BackendDAE.Var> aliasLst={};
protected
  BackendDAE.Var var;
  DAE.ComponentRef cref;
  DAE.Exp exp;
algorithm
  for var in varsIn loop
    BackendDAE.VAR(varName=cref) := var;
    if BackendVarTransform.hasReplacement(repl,cref) then
      exp := BackendVarTransform.getReplacement(repl,cref);
      var := BackendVariable.setBindExp(var,SOME(exp));
      if Expression.isConst(exp) then
        constLst := var::constLst;
      else
        exp := BackendVariable.varBindExp(var);
        (exp,_) := BackendVarTransform.replaceExp(exp,repl,NONE());
        var := BackendVariable.setBindExp(var,SOME(exp));
        aliasLst := var::aliasLst;
      end if;
    else
      varLst := var::varLst;
    end if;
  end for;
end assignAliasVars;

//-----------------------------------------------
// split For Equations
//-----------------------------------------------

protected function splitForEquations"splits the for-equations into for equations and single equations which contain the scalarsIn"
  input BackendDAE.Equation eqIn;
  input list<DAE.ComponentRef> scalarsIn;
  input list<DAE.ComponentRef> states;
  input tuple<list<BackendDAE.Equation>,list<DAE.ComponentRef>> tplIn;  //the sliced equations and the crefs to slice the array vars
  output tuple<list<BackendDAE.Equation>,list<DAE.ComponentRef>> tplOut;
algorithm
  tplOut := matchcontinue(eqIn,scalarsIn,states,tplIn)
    local
      DAE.ComponentRef cref, crefRange;
      DAE.Exp iter,start,stop,lhs,rhs, range;
      DAE.ElementSource source;
      BackendDAE.Equation forEq, eq;
      BackendDAE.EquationAttributes attr;
      list<BackendDAE.Equation> scalarEqs, eqsIn;
      list<DAE.ComponentRef> allCrefs, derCrefs, scalars, all, splitCrefsIn, splitCrefs0,splitCrefs1;
      list<DAE.Exp> restSubs;
  case(BackendDAE.FOR_EQUATION(iter,start,stop,lhs,rhs,source,attr),_,_,(eqsIn,splitCrefsIn))
    algorithm
        //BackendDump.dumpEquationList({eqIn},"EQ");
      allCrefs := BackendEquation.equationCrefs(eqIn);
      (_,allCrefs) := List.separate1OnTrue(allCrefs, ComponentReference.crefInLst,states);// dont take the states
      (_,derCrefs) := BackendEquation.traverseExpsOfEquation(eqIn,Expression.getAllCrefsFromDer,{});//but slice for der(states)
      allCrefs := listAppend(derCrefs,allCrefs);
      //print("allCrefs: "+stringDelimitList(List.map(allCrefs,ComponentReference.printComponentRefStr),"\n|")+"\n\n");
      range := DAE.RANGE(Expression.typeof(start),start,NONE(),stop);
      restSubs := {};
      // get the subs of the splitted crefs which occure in the equation
      while not listEmpty(allCrefs) loop
        cref::allCrefs := allCrefs;
        (_,allCrefs) := List.separate1OnTrue(allCrefs,ComponentReference.crefEqualWithoutSubs,cref);
        scalars := {};
        crefRange := BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref,iter,range);
        if isRangeCref(crefRange) then
          //print("crefRange: "+stringDelimitList(List.map({crefRange},ComponentReference.printComponentRefStr)," | ")+"\n");
          scalars := listAppend(scalars,List.filter1OnTrue(scalarsIn,crefFitsInCref,crefRange));
           //print("scalars: "+stringDelimitList(List.map(scalars,ComponentReference.printComponentRefStr)," | ")+"\n");
          ((range,restSubs)) := List.fold2(scalars,getIteratorVarForIndex,cref,iter,(range,restSubs));
        end if;
      end while;
          //print("range: "+stringDelimitList(List.map({range},ExpressionDump.printExpStr),"\n")+"\n");
          //print("restSubs: "+stringDelimitList(List.map(restSubs,ExpressionDump.printExpStr),"\n")+"\n");
        scalarEqs := List.map1(restSubs,makeScalarForEquation,eqIn);
        DAE.RANGE(start=start, stop=stop) := range;
        forEq := BackendDAE.FOR_EQUATION(iter,start,stop,lhs,rhs,source,attr);
          //BackendDump.dumpEquationList(forEq::scalarEqs,"MADE EQS");
        splitCrefs0 := {};
        // get the other array vars that have to be separated in the array vars
        for cref in allCrefs loop
          crefRange := BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref,iter,range);
          if isRangeCref(crefRange) and not List.exist1(scalarsIn,ComponentReference.crefEqualWithoutSubs,crefRange) then
            splitCrefs1 := List.map1r(List.mapMap(restSubs, Expression.makeIndexSubscript,List.create),replaceFirstSubsInCref,cref);
            splitCrefs0 := listAppend(splitCrefs1,splitCrefs0);
          end if;
        end for;
          //print("splitCrefs0: "+stringDelimitList(List.map(splitCrefs0,ComponentReference.printComponentRefStr)," | ")+"\n");
    then (listAppend(forEq::scalarEqs,eqsIn),listAppend(splitCrefs0,splitCrefsIn));
  case(_,_,_,(eqsIn,splitCrefsIn))
    algorithm
    then ((eqIn::eqsIn),splitCrefsIn);
  end matchcontinue;
end splitForEquations;

protected function makeScalarForEquation"makes a scalar equation from a for-equation for a certain index"
  input DAE.Exp sub;
  input BackendDAE.Equation eqIn;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := matchcontinue(sub,eqIn)
    local
      DAE.Exp iterExp, lhs, rhs;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
  case(_,BackendDAE.FOR_EQUATION(iter=iterExp,left=lhs,right=rhs,source=source,attr=attr))
    equation
      (lhs,_) = Expression.traverseExpBottomUp(lhs,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iterExp,sub));
      (rhs,_) = Expression.traverseExpBottomUp(rhs,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iterExp,sub));
  then BackendDAE.EQUATION(lhs,rhs,source,attr);
  else
    equation
  then eqIn;
  end matchcontinue;
end makeScalarForEquation;

protected function insertRangeInForEquation"replaces the iterator with the range"
  input BackendDAE.Equation eqIn;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := matchcontinue(eqIn)
    local
      DAE.Exp iterExp, lhs, rhs, start, stop;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
  case(BackendDAE.FOR_EQUATION(iter=iterExp,start=start, stop=stop,left=lhs,right=rhs,source=source,attr=attr))
    equation
      (lhs,_) = Expression.traverseExpBottomUp(lhs,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iterExp,DAE.RANGE(Expression.typeof(lhs),start,NONE(),stop)));
      (rhs,_) = Expression.traverseExpBottomUp(rhs,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iterExp,DAE.RANGE(Expression.typeof(rhs),start,NONE(),stop)));
  then BackendDAE.EQUATION(lhs,rhs,source,attr);
  else
    equation
  then eqIn;
  end matchcontinue;
end insertRangeInForEquation;


protected function getIteratorVarForIndex"gets a certain scalar index e.g. a[3] and the corresponding iteration cref e.g. a[i+1]
,checks that i is 2 and splits this equation the given range"
  input DAE.ComponentRef crefScalar;
  input DAE.ComponentRef crefWithIter;
  input DAE.Exp iterator;
  input tuple<DAE.Exp,list<DAE.Exp>> tplIn;
  output tuple<DAE.Exp,list<DAE.Exp>> tplOut;
protected
  Integer startI,stopI,i;
  DAE.Type ty;
  DAE.Exp it,value,range;
  list<DAE.Exp> rest;
algorithm
  try
    (range,rest) := tplIn;
    DAE.RANGE(ty=ty,start=DAE.ICONST(startI),stop=DAE.ICONST(stopI)) := range;
    {DAE.INDEX(it)} := ComponentReference.crefSubs(crefWithIter);
    {DAE.INDEX(value)} := ComponentReference.crefSubs(crefScalar);
    (DAE.ICONST(i),_) := ExpressionSolve.solve(it,value,iterator);
    if intEq(i,startI) then
      range := DAE.RANGE(ty,DAE.ICONST(startI+1),NONE(),DAE.ICONST(stopI));
      rest := DAE.ICONST(i)::rest;
    elseif intEq(i,stopI) then
      range := DAE.RANGE(ty,DAE.ICONST(startI),NONE(),DAE.ICONST(stopI-1));
      rest := DAE.ICONST(i)::rest;
    else
      range := DAE.ICONST(-1);
      rest := listAppend(List.map(List.intRange2(startI,stopI),Expression.makeIntegerExp),rest);
    end if;
      tplOut := (range,rest);
  else
    tplOut := tplIn;
  end try;
end getIteratorVarForIndex;

public function crefFitsInVar"check if the subs of cref are covered by the subs of the var"
  input BackendDAE.Var var;
  input DAE.ComponentRef cref;
  output Boolean b;
protected
  DAE.ComponentRef varName;
algorithm
  BackendDAE.VAR(varName=varName) := var;
  b := crefFitsInCref(cref,varName);
end crefFitsInVar;

public function varFitsInCref"check if the subs of var crefs are covered by the subs of the cref"
  input BackendDAE.Var var;
  input DAE.ComponentRef cref;
  output Boolean b;
protected
  DAE.ComponentRef varName;
algorithm
  BackendDAE.VAR(varName=varName) := var;
  b := crefFitsInCref(varName,cref);
end varFitsInCref;

protected function crefFitsInCref"check if the subs of cref1 are covered by the subs of cref2"
  input DAE.ComponentRef cref1;
  input DAE.ComponentRef cref2;
  output Boolean b;
protected
  DAE.Subscript sub1,sub2;
algorithm
  if ComponentReference.crefEqualWithoutSubs(cref1,cref2) then
      //print("compare: "+stringDelimitList(List.map({cref1,cref2},ComponentReference.printComponentRefStr)," with ")+"\n\n");
    {sub1} := ComponentReference.crefSubs(cref1);

    {sub2} := ComponentReference.crefSubs(cref2);
    b := subFitsInSub(sub1,sub2);
  else
    b := false;
  end if;
end crefFitsInCref;

public function subFitsInSub"checks if sub1 fits in sub2"
  input DAE.Subscript sub1;
  input DAE.Subscript sub2;
  output Boolean b;
algorithm
  b := matchcontinue(sub1,sub2)
    local
      Integer i1,start1,stop1,start2,stop2;
  case(DAE.INDEX(DAE.ICONST(i1)),DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start2),stop=DAE.ICONST(stop2))))
    equation
        //print(" i1 "+intString(i1)+" start2 "+intString(start2)+" stop2 "+intString(stop2)+"\n");
      b = intLe(start2,i1) and intGe(stop2,i1);
  then b;

  case(DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start1),stop=DAE.ICONST(stop1))),DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start2),stop=DAE.ICONST(stop2))))
    equation
        //print(" i1 "+intString(i1)+" start2 "+intString(start2)+" stop2 "+intString(stop2)+"\n");
      b = intLe(start2,start1) and intGe(stop2,stop1);
  then b;

  else
    then false;
  end matchcontinue;
end subFitsInSub;

public function subExtendsSub"checks if sub1 extends sub2. either appends or interleaves and appends/prepends partly"
  input DAE.Subscript sub1;
  input DAE.Subscript sub2;
  output Boolean b;
  output DAE.Subscript extendedSub;
algorithm
  (b,extendedSub) := matchcontinue(sub1,sub2)
    local
      Integer i1,i2,start1,stop1,start2,stop2;
      DAE.Subscript extSub;
      DAE.Type ty;
  case(DAE.INDEX(DAE.ICONST(i1)),DAE.INDEX(DAE.RANGE(ty=ty,start=DAE.ICONST(start2),stop=DAE.ICONST(stop2))))
    equation
        //print(" i1 "+intString(i1)+" start2 "+intString(start2)+" stop2 "+intString(stop2)+"\n");
      b = intEq(i1,stop2+1) or intEq(i1,start2-1);
      extSub = DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(intMin(start2,i1)),NONE(),DAE.ICONST(intMax(stop2,i1))));
  then (b,extSub);

  case(DAE.INDEX(DAE.RANGE(ty=ty,start=DAE.ICONST(start1),stop=DAE.ICONST(stop1))),DAE.INDEX(DAE.ICONST(i2)))
    equation
        //print(" i2 "+intString(i2)+" start1 "+intString(start1)+" stop1 "+intString(stop1)+"\n");
      b = intEq(i2,stop1+1) or intEq(i2,start1-1);
      extSub = DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(intMin(start1,i2)),NONE(),DAE.ICONST(intMax(stop1,i2))));
  then (b,extSub);

  case(DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start1),stop=DAE.ICONST(stop1))),DAE.INDEX(DAE.RANGE(ty=ty,start=DAE.ICONST(start2),stop=DAE.ICONST(stop2))))
    equation
        //print(" start1 "+intString(start1)+" stop1 "+intString(stop1)+" start2 "+intString(start2)+" stop2 "+intString(stop2)+"\n");
      b = intGt(stop1,stop2) and intLe(stop2,start1) or intLt(start1,start2) and intGe(stop2,stop1); // appends or prepends
      extSub = DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(intMin(start1,start2)),NONE(),DAE.ICONST(intMax(stop1,stop2))));
  then (b,extSub);


  else
    then (false,sub2);
  end matchcontinue;
end subExtendsSub;


public function isRangeCref"checks whether a cref has a range subscript"
  input DAE.ComponentRef cref;
  output Boolean b;
protected
  DAE.Exp exp;
algorithm
  try
    {DAE.INDEX(exp)} := ComponentReference.crefSubs(cref);
    b := Expression.isRange(exp);
  else
    b := false;
  end try;
end isRangeCref;

//-----------------------------------------------
// removeSimpleEquationsWithFor
//-----------------------------------------------

protected function removeSimpleEquationsWithFor"implementation for removeSimpleEquationsForEquations that handles eqSystems"
  input list<BackendDAE.Equation> eqsIn;
  input BackendDAE.Variables varsIn;
  input Option<BackendVarTransform.VariableReplacements> replIn;
  output list<BackendDAE.Equation> eqsOut;
  output BackendVarTransform.VariableReplacements replOut;
protected
  Boolean replaced;
  Integer size, i;
  BackendDAE.EqSystem eqSys;
  BackendDAE.EquationArray eqs;
  BackendDAE.Variables vars;
  BackendVarTransform.VariableReplacements repl;
  list<BackendDAE.Equation> allEqLst, eqLst, simpleEqLst;
  list<BackendDAE.Var> knownVarLst, aliasLst, varLst;
  Option<BackendDAE.IncidenceMatrix> m;
  Option<BackendDAE.IncidenceMatrixT> mT;
  BackendDAE.Matching matching;
  BackendDAE.StateSets stateSets "the statesets of the system";
  BackendDAE.BaseClockPartitionKind partitionKind;
algorithm
  // add empty replacement with bucketSize or use input repl
  if Util.isSome(replIn) then
    repl := Util.getOption(replIn);
  else
    size := listLength(eqsIn);
    size := intMax(BaseHashTable.defaultBucketSize, realInt(realMul(intReal(size), 0.7)));
    repl := BackendVarTransform.emptyReplacementsSized(size);
  end if;

  //traverse for equations
  eqLst := {};
  simpleEqLst := {};
  allEqLst := eqsIn;
  vars := varsIn;
  replaced := true;
  while replaced loop
    (vars, repl, eqLst, simpleEqLst,replaced) := List.fold(allEqLst, findSimpleEquationsWithFor1, (vars, repl, {}, simpleEqLst,false));
    allEqLst := eqLst;
  end while;
    // replace one final round
    //(eqsOut,_) := BackendVarTransform.replaceEquations(eqLst,repl,NONE());
  eqsOut := eqLst;
  replOut := repl;
end removeSimpleEquationsWithFor;

protected function findSimpleEquationsWithFor1 "gets an equation, apply replacements and checks for new replacement rules"
  input BackendDAE.Equation eqIn;
  input tuple<BackendDAE.Variables, BackendVarTransform.VariableReplacements, list<BackendDAE.Equation>, list<BackendDAE.Equation>, Boolean> tplIn;
  output tuple<BackendDAE.Variables, BackendVarTransform.VariableReplacements, list<BackendDAE.Equation>, list<BackendDAE.Equation>, Boolean> tplOut;
protected
  list<BackendDAE.Equation> replEqs;
  BackendVarTransform.VariableReplacements repl;
algorithm
  (_,repl,_,_,_) := tplIn;
    //print("\nCHECKEQ: "+BackendDump.equationString(eqIn)+"\n");
  (replEqs,_) := BackendVarTransform.replaceEquations({eqIn},repl,NONE());
    //print("REPL EQS: "+stringDelimitList(List.map(replEqs,BackendDump.equationString),"\n")+"\n");
  tplOut := List.fold(replEqs,findSimpleEquationsWithFor2,tplIn);
end findSimpleEquationsWithFor1;

protected function findSimpleEquationsWithFor2"equation traverse function that looks for alias assignments in for equations and introduces alias statements"
  input BackendDAE.Equation eqIn;
  input tuple<BackendDAE.Variables, BackendVarTransform.VariableReplacements, list<BackendDAE.Equation>, list<BackendDAE.Equation>, Boolean> tplIn;
  output tuple<BackendDAE.Variables, BackendVarTransform.VariableReplacements, list<BackendDAE.Equation>, list<BackendDAE.Equation>, Boolean> tplOut;
algorithm
  (tplOut) := matchcontinue(eqIn,tplIn)
    local
      Boolean replaced,b1,b2;
      DAE.Ident ident1,ident2;
      DAE.Exp iter, start, stop, exp, e1, e2;
      DAE.Operator op;
      DAE.Type ty;
      BackendDAE.Variables vars;
      BackendVarTransform.VariableReplacements repl;
      DAE.ComponentRef cref1, cref2;
      list<BackendDAE.Equation> eqLst, simpleEqLst;
      list<DAE.Subscript> subs1,sub2;

  // cref = const
  case(BackendDAE.EQUATION(scalar=DAE.CREF(cref1), exp=exp),(vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isConst(exp);
      //print("REPL_EQ1 "+BackendDump.equationString(eqIn)+"\n");
      repl = BackendVarTransform.addReplacement(repl,cref1,exp,NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // const = cref
  case(BackendDAE.EQUATION(exp=DAE.CREF(cref1), scalar=exp),(vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isConst(exp);
      //print("REPL_EQ2 "+BackendDump.equationString(eqIn)+"\n");
      repl = BackendVarTransform.addReplacement(repl,cref1,exp,NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // cref = cref
  case(BackendDAE.EQUATION(scalar=DAE.CREF(cref1), exp=DAE.CREF(cref2)),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //print("REPL_EQ3 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,Expression.crefExp(cref2),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,Expression.crefExp(cref1),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // cref = - cref
  case(BackendDAE.EQUATION(scalar=DAE.CREF(cref1), exp=DAE.UNARY(operator=op,exp=DAE.CREF(cref2))),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //print("REPL_EQ4 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,DAE.UNARY(op,Expression.crefExp(cref2)),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,DAE.UNARY(op,Expression.crefExp(cref1)),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // - cref = cref
  case(BackendDAE.EQUATION(scalar=DAE.UNARY(operator=op,exp=DAE.CREF(cref1)), exp=DAE.CREF(cref2)),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //print("REPL_EQ5 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,DAE.UNARY(op,Expression.crefExp(cref2)),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,DAE.UNARY(op,Expression.crefExp(cref1)),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // cref + cref = 0
  case(BackendDAE.EQUATION(scalar=e1, exp=DAE.BINARY(exp1=DAE.CREF(cref1), operator=DAE.ADD(ty=ty), exp2=DAE.CREF(cref2))), (vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(e1);
      //print("REPL_EQ6 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,DAE.UNARY(DAE.UMINUS(ty),Expression.crefExp(cref2)),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,DAE.UNARY(DAE.UMINUS(ty),Expression.crefExp(cref1)),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // cref - cref = 0
  case(BackendDAE.EQUATION(scalar=e1, exp=DAE.BINARY(exp1=DAE.CREF(cref1), operator=DAE.SUB(ty=ty), exp2=DAE.CREF(cref2))), (vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(e1);
      //print("REPL_EQ7 "+BackendDump.equationString(eqIn)+"\n");
      //BackendVarTransform.dumpReplacements(repl);
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,Expression.crefExp(cref2),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,Expression.crefExp(cref1),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // 0 = cref + cref
  case(BackendDAE.EQUATION(exp=e1, scalar=DAE.BINARY(exp1=DAE.CREF(cref1), operator=DAE.ADD(ty=ty), exp2=DAE.CREF(cref2))), (vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(e1);
      //print("REPL_EQ8 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,DAE.UNARY(DAE.UMINUS(ty),Expression.crefExp(cref2)),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,DAE.UNARY(DAE.UMINUS(ty),Expression.crefExp(cref1)),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // 0 = cref - cref
  case(BackendDAE.EQUATION(exp=e1, scalar=DAE.BINARY(exp1=DAE.CREF(cref1), operator=DAE.SUB(ty=ty), exp2=DAE.CREF(cref2))), (vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(e1);
      //print("REPL_EQ9 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,Expression.crefExp(cref2),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,Expression.crefExp(cref1),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  // (-cref) - cref = 0
  case(BackendDAE.EQUATION(scalar=e1, exp=DAE.BINARY(exp1=DAE.UNARY(operator=op,exp=DAE.CREF(cref1)), operator=DAE.SUB(ty=ty), exp2=DAE.CREF(cref2))), (vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(e1);
        //print("REPL_EQ10 "+BackendDump.equationString(eqIn)+"\n");
      if isConnectionVar(cref1,vars) or ComponentReference.crefHaveSubs(cref2) then
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" cref2: "+ComponentReference.printComponentRefStr(cref2)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref1,Expression.crefExp(cref2),NONE());
      else
        //print("cref2: "+ComponentReference.printComponentRefStr(cref2)+" --> "+" cref1: "+ComponentReference.printComponentRefStr(cref1)+"\n");
        repl = BackendVarTransform.addReplacement(repl,cref2,Expression.crefExp(cref1),NONE());
      end if;
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

 // replacements in for equations!!
 //--------------------------------

  //cref[iter] = cref[iter] for whole dimension;
  case(BackendDAE.FOR_EQUATION(iter=iter, start=start, stop=stop,left=DAE.CREF(componentRef=cref1),right=DAE.CREF(componentRef=cref2)),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //alias vars in for equation
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident1)))} = ComponentReference.crefSubs(cref1);
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident2)))} = ComponentReference.crefSubs(cref2);
      true = stringEqual(ident1,ident2);
      cref1 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref1,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
      cref2 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref2,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
        //print("-->EQ00: "+BackendDump.equationString(eqIn)+"\n\n");
      //add replacement
      (cref1,cref2) = chooseAliasVar(cref1,cref2,vars);
      repl = BackendVarTransform.addReplacement(repl,cref1,Expression.crefExp(cref2),NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  //cref[iter] = -(cref[iter]) for whole dimension;
  case(BackendDAE.FOR_EQUATION(iter=iter, start=start, stop=stop,left=DAE.CREF(componentRef=cref1),right=DAE.UNARY(operator=DAE.UMINUS(ty=ty),exp=DAE.CREF(componentRef=cref2))),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //alias vars in for equation
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident1)))} = ComponentReference.crefSubs(cref1);
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident2)))} = ComponentReference.crefSubs(cref2);
      true = stringEqual(ident1,ident2);
      cref1 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref1,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
      cref2 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref2,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
        //print("-->EQ01: "+BackendDump.equationString(eqIn)+"\n\n");
      //add replacement
      (cref1,cref2) = chooseAliasVar(cref1,cref2,vars);
      repl = BackendVarTransform.addReplacement(repl,cref1,DAE.UNARY(DAE.UMINUS(ty),DAE.CREF(cref2,ty)),NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  //0 = cref[iter] +- cref[iter];
  case(BackendDAE.FOR_EQUATION(iter=iter, start=start, stop=stop, left=exp, right=DAE.BINARY(DAE.CREF(componentRef=cref1),op,DAE.CREF(componentRef=cref2))),(vars,repl,eqLst,simpleEqLst,_))
    equation
      true = Expression.isZero(exp);
      //alias vars in for equation
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident1)))} = ComponentReference.crefSubs(cref1);
      {DAE.INDEX(DAE.CREF(DAE.CREF_IDENT(ident=ident2)))} = ComponentReference.crefSubs(cref2);
      true = stringEqual(ident1,ident2);
      cref1 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref1,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
      cref2 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref2,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
       // print("-->EQ02: "+BackendDump.equationString(eqIn)+"\n");
      //add replacement
      (cref1,cref2) = chooseAliasVar(cref1,cref2,vars);
      e2 = if Expression.isAdd(op) then DAE.UNARY(DAE.UMINUS(Expression.typeof(exp)),Expression.crefExp(cref2)) else Expression.crefExp(cref2);
      repl = BackendVarTransform.addReplacement(repl,cref1,e2,NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  //cref[iter] = cref[iter+x] for whole dimension;
  case(BackendDAE.FOR_EQUATION(iter=iter, start=start, stop=stop,left=DAE.CREF(componentRef=cref1),right=DAE.CREF(componentRef=cref2)),(vars,repl,eqLst,simpleEqLst,_))
    equation
      //alias vars in for equation
      true = ComponentReference.crefEqualWithoutSubs(cref1,cref2);
      cref1 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref1,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
      cref2 = BackendArrayVarTransform.replaceIteratorWithRangeInCref(cref2,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
        //print("-->EQ03: "+BackendDump.equationString(eqIn)+"\n\n");
      (e1,b1) = getAnyArrayReplacement(repl,cref1);
      (e2,b2) = getAnyArrayReplacement(repl,cref1);
      //add replacement
      true = b1 or b2;
      if b1 then exp = e1; end if;
      if b2 then exp = e2; end if;
        //print("cref1: "+ComponentReference.printComponentRefStr(cref1)+" --> "+" exp: "+ExpressionDump.printExpStr(exp)+"\n");
      repl = BackendVarTransform.addReplacement(repl,cref1,exp,NONE());
      repl = BackendVarTransform.addReplacement(repl,cref2,exp,NONE());
    then (vars,repl,eqLst,eqIn::simpleEqLst,true);

  case(_,(vars,repl,eqLst,simpleEqLst,replaced))
    equation
      //print("MISSED EQ "+BackendDump.equationString(eqIn)+"\n");
    then (vars,repl,eqIn::eqLst,simpleEqLst,replaced);
  end matchcontinue;
end findSimpleEquationsWithFor2;


public function getAnyArrayReplacement "
  gets the replacement exp if the replacements contain a rule for any of the scalar array crefs
"
  input BackendVarTransform.VariableReplacements inVariableReplacements;
  input DAE.ComponentRef inComponentRef;
  output DAE.Exp eOut;
  output Boolean gotRepl;
protected
  Boolean search;
  DAE.ComponentRef cref, crefNoSubs;
  list<DAE.ComponentRef> crefs;
  HashTable2.HashTable ht;
  HashTable3.HashTable arrHT;
algorithm
   BackendVarTransform.REPLACEMENTS(hashTable=ht, arrayHashTable=arrHT) := inVariableReplacements;
   crefNoSubs := ComponentReference.crefStripSubs(inComponentRef);
   crefs := BaseHashTable.get(crefNoSubs,arrHT);
   search := true;
   eOut := Expression.crefExp(inComponentRef);
   gotRepl := false;
   while search and not listEmpty(crefs) loop
     cref::crefs := crefs;
     if crefFitsInCref(cref,inComponentRef) then
       eOut := BaseHashTable.get(cref,ht);
       search := false;
       gotRepl := true;
     end if;
   end while;
end getAnyArrayReplacement;

protected function chooseAliasVar"selects a good alias var"
  input DAE.ComponentRef cref1;
  input DAE.ComponentRef cref2;
  input BackendDAE.Variables vars;
  output DAE.ComponentRef replVar;  // will be replaced
  output DAE.ComponentRef aliasVar; // will remain
algorithm
  //pick the parameters
  if not BackendVariable.existsVar(cref1,vars,false) then
    replVar := cref2;
    aliasVar := cref1;
  elseif not BackendVariable.existsVar(cref2,vars,false) then
     replVar := cref1;
     aliasVar := cref2;
  else
    // pick the non-connection vars
    if isConnectionVar(cref1,vars) then
      replVar := cref1;
      aliasVar := cref2;
    elseif isConnectionVar(cref2,vars) then
      replVar := cref2;
      aliasVar := cref1;
    else
      // pick the array vars
      if ComponentReference.crefHaveSubs(cref1) then
        replVar := cref2;
        aliasVar := cref1;
      else
        replVar := cref1;
        aliasVar := cref2;
      end if;
    end if;
  end if;
  //print("replVar: "+ComponentReference.printComponentRefStr(replVar)+" --> "+" aliasVar: "+ComponentReference.printComponentRefStr(aliasVar)+"\n");
end chooseAliasVar;


/*
public function replaceExp"same as BackendVarTransform but check of a arraysub cref has no replacement, if there is another whole range cref"
  input DAE.Exp inExp;
  input BackendVarTransform.VariableReplacements replIn;
  output DAE.Exp expOut;
algorithm
  (expOut) := matchcontinue(inExp,replIn)
    local
      Integer dim;
      DAE.ComponentRef cref;
      DAE.Exp e1, e2;
      DAE.Operator op;
      DAE.Subscript sub;
      DAE.Type ty;
case(DAE.CREF(componentRef=cref, ty=ty),_)
    equation
      if ComponentReference.crefHaveSubs(cref) and not BackendVarTransform.hasReplacement(replIn,cref) then
        {sub} = ComponentReference.crefSubs(cref);
        // check the max dimension
        ComponentReference.debugPrintComponentRefTypeStr(cref);
        print("check dim for "+ComponentReference.debugPrintComponentRefTypeStr(cref)+":\n");
        dim = Expression.dimensionSize(listHead(ComponentReference.crefDims(cref)));
        print(intString(dim)+"!!!!\n");
        cref =  replaceFirstSubsInCref(cref,{DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(1),NONE(),DAE.ICONST(dim)))});
        if BackendVarTransform.hasReplacement(replIn,cref) then
          e1 = BackendVarTransform.getReplacement(replIn,cref);
          (e1,_) = Expression.traverseExpBottomUp(e1,replaceSubscriptInCrefExp,{sub});
        else
          e1 = inExp;
        end if;
      end if;
    then e1;

  case(DAE.BINARY(exp1=e1,operator=op,exp2=e2),_)
    equation
      e1 = replaceExp(e1,replIn);
      e2 = replaceExp(e2,replIn);
      e1 = ExpressionSimplify.simplify(DAE.BINARY(e1,op,e2));
    then e1;

  case(DAE.UNARY(operator=op,exp=e1),_)
    equation
      e1 = replaceExp(e1,replIn);
      e1 = ExpressionSimplify.simplify(DAE.UNARY(op,e1));
    then e1;

  else
    equation
      e1 = BackendVarTransform.replaceExp(inExp,replIn,NONE());
    then e1;
  end matchcontinue;
end replaceExp;

public function replaceEquation"same as BackendVarTransform.replaceEquations but with my replaceExp"
  input BackendDAE.Equation eqIn;
  input BackendVarTransform.VariableReplacements replIn;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := matchcontinue(eqIn,replIn)
    local
      DAE.Exp e1, e2;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      BackendDAE.Equation eq;
    case(BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr),_)
      equation
        print("replace in equation: "+BackendDump.equationString(eqIn)+"\n");
        e1 = replaceExp(e1, replIn);
        e2 = replaceExp(e2, replIn);
      then BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr);
      else
        equation
          ({eq},_) = BackendVarTransform.replaceEquations({eqIn},replIn,NONE());
      then eq;
  end matchcontinue;
end replaceEquation;
*/
protected function isConnectionVar"outputs true if the var according to the cref comes from a connection equation"
  input DAE.ComponentRef crefIn;
  input BackendDAE.Variables vars;
  output Boolean isConnVar;
protected
  BackendDAE.Var var;
  list<BackendDAE.Var> varLst;
algorithm
  try
    (varLst,_) := getVar_unexpanded(crefIn,vars);
    isConnVar := BackendVariable.isVarConnector(listHead(varLst));
  else
    isConnVar := false;
  end try;
end isConnectionVar;


public function getVar_unexpanded"gets the var according to the cref. works for unexpanded and sliced array vars as well"
  input DAE.ComponentRef cref;
  input BackendDAE.Variables vars;
  output list<BackendDAE.Var> outVarLst;
  output list<Integer> outIntegerLst;
protected
  BackendDAE.Var var;
algorithm
  for idx in List.intRange(BackendVariable.varsSize(vars)) loop
     var := BackendVariable.getVarAt(vars,idx);
     if varIsEqualCrefWithoutSubs(var,cref) then
       outVarLst := {var};
       outIntegerLst := {idx};
       break;
     else
       outVarLst := {};
       outIntegerLst := {};
     end if;
  end for;
end getVar_unexpanded;

/*
protected function crefVarEqual"the var cref is equal to the cref or includes it in its range."
  input BackendDAE.Var var;
  input DAE.ComponentRef cref;
  output Boolean b;
protected
  list<DAE.Subscript> subs1,subs2;
algorithm
  if varIsEqualCrefWithoutSubs(var,cref) then
    subs1 := ComponentReference.crefSubs(cref);
    subs2 := ComponentReference.crefSubs(BackendVariable.varCref(var));
    b := List.threadFold(subs1,subs2,subsAreValid,true);
  else
    b := false;
  end if;
end crefVarEqual;

protected function subsAreValid"checks whether the two subs are equal or include each other. e.g. sub1=[3], sub2=[2:7] --> true"
  input DAE.Subscript sub1;
  input DAE.Subscript sub2;
  input Boolean bIn;
  output Boolean bOut;
algorithm
  bOut := matchcontinue(sub1,sub2,bIn)
    local
      Integer i1,i2,i3;
  case(DAE.INDEX(DAE.ICONST(i1)),DAE.INDEX(DAE.ICONST(i2)),_)
    equation
  then bIn and intEq(i1,i2);
  case(DAE.SLICE(DAE.RANGE(start=DAE.ICONST(i1),step=NONE(),stop=DAE.ICONST(i2))),DAE.INDEX(DAE.ICONST(i3)),_)
    equation
  then bIn and intGe(i3,i1) and intLe(i3,i2);
  case(DAE.INDEX(DAE.ICONST(i3)),DAE.SLICE(DAE.RANGE(start=DAE.ICONST(i1),step=NONE(),stop=DAE.ICONST(i2))),_)
    equation
  then bIn and intGe(i3,i1) and intLe(i3,i2);
  case(DAE.INDEX(DAE.ICONST(i3)),DAE.WHOLEDIM(),_)
    equation
  then bIn;
  case(DAE.WHOLEDIM(),DAE.INDEX(DAE.ICONST(i3)),_)
    equation
  then bIn;
  else
    then false;
  end matchcontinue;
end subsAreValid;


protected function getFirstRangeCref"gets the first indexed cref of the range cref"
  input DAE.ComponentRef crefIn;
  output DAE.ComponentRef crefOut;
algorithm
  crefOut := matchcontinue(crefIn)
    local
      DAE.Ident ident;
      DAE.Type ty;
      list<DAE.Subscript> subs;
      DAE.ComponentRef cref1;
  case(DAE.CREF_QUAL(ident,ty,subs,cref1))
    equation
      subs = List.map(subs,getFirstRangeCref1);
      cref1 = getFirstRangeCref(cref1);
  then DAE.CREF_QUAL(ident,ty,subs,cref1);

  case(DAE.CREF_IDENT(ident,ty,subs))
    equation
      subs = List.map(subs,getFirstRangeCref1);
  then DAE.CREF_IDENT(ident,ty,subs);

  else
    then crefIn;
  end matchcontinue;
end getFirstRangeCref;


protected function getFirstRangeCref1"implementation for getFirstRangeCref. sets the first subscript from the indexed range subscripts"
  input DAE.Subscript subIn;
  output DAE.Subscript subOut;
algorithm
  subOut := matchcontinue(subIn)
    local
      DAE.Exp exp;
    case(DAE.INDEX(exp=DAE.RANGE(start=exp)))
      equation
      then DAE.INDEX(exp);
    else
      then subIn;
  end matchcontinue;
end getFirstRangeCref1;

*/


//-----------------------------------------------
// Slice the unexpanded array vars according to the occurence of concrete indexed elements in the mixed equations
//-----------------------------------------------

protected function sliceArrayVarsForCref"fold function to slice out the cref from the arrayVar"
  input DAE.ComponentRef crefIn;
  input list<BackendDAE.Var> varsIn;
  output list<BackendDAE.Var> varsOut;
protected
  Integer pos;
  BackendDAE.Var var;
  list<BackendDAE.Var> addVars, vars;
algorithm
  pos := List.position1OnTrue(varsIn,crefFitsInVar,crefIn);
  if intGt(pos,0) then
    var := listGet(varsIn,pos);
    (var,addVars) := sliceArrayVarsForCref1(var,crefIn);
    vars := List.replaceAt(var,pos,varsIn);
  else
    addVars := {};
    vars := varsIn;
  end if;
    varsOut := listAppend(vars,addVars);
end sliceArrayVarsForCref;


protected function sliceArrayVarsForCref1"fold function to slice out the cref from the arrayVar.
the returned var is the single indexed var, the addVars are the partially sliced rest arrays"
  input BackendDAE.Var varIn;
  input DAE.ComponentRef crefIn;
  output BackendDAE.Var varOut;
  output list<BackendDAE.Var> addVars;
algorithm
  (varOut,addVars) := matchcontinue(varIn,crefIn)
    local
      Integer dim, start, stop, idx;
      list<Integer> idxRange;
      BackendDAE.Var var;
      DAE.ComponentRef cref;
      DAE.Subscript sub;
      list<DAE.ComponentRef> slicedCrefs;
      list<BackendDAE.Var> slicedVars;
      list<DAE.Subscript> subs;
  case(BackendDAE.VAR(varName=cref),_)
    equation
      // slice a wholedim
      {DAE.WHOLEDIM()} = ComponentReference.crefSubs(cref);
      {DAE.DIM_INTEGER(dim)} = ComponentReference.crefDims(cref);
      {DAE.INDEX(DAE.ICONST(idx))} = ComponentReference.crefSubs(crefIn);
      idxRange = List.deleteMember(List.intRange(dim),idx);
      subs = List.fold1(idxRange,makeRangeSubscripts,ComponentReference.crefType(crefIn),{});// a list of slice subs
      slicedCrefs = List.map1r(List.map(subs,List.create),replaceFirstSubsInCref,cref);
      slicedVars = List.map1(slicedCrefs,BackendVariable.copyVarNewName,varIn);
      var = BackendVariable.copyVarNewName(crefIn,varIn);
    then (var,slicedVars);
  case(BackendDAE.VAR(varName=cref),_)
    equation
      // slice a range
      {DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start),stop=DAE.ICONST(stop)))} = ComponentReference.crefSubs(cref);
      {DAE.DIM_INTEGER(dim)} = ComponentReference.crefDims(cref);
      {DAE.INDEX(DAE.ICONST(idx))} = ComponentReference.crefSubs(crefIn);
      idxRange = List.deleteMember(List.intRange2(start,stop),idx);
      subs = List.fold1(idxRange,makeRangeSubscripts,ComponentReference.crefType(crefIn),{});// a list of slice subs
      slicedCrefs = List.map1r(List.map(subs,List.create),replaceFirstSubsInCref,cref);
      slicedVars = List.map1(slicedCrefs,BackendVariable.copyVarNewName,varIn);
      var = BackendVariable.copyVarNewName(replaceFirstSubsInCref(cref, {DAE.INDEX(DAE.ICONST(idx))}),varIn);
    then (var,slicedVars);
  else
    equation
      print("missing case in sliceArrayVarsForCref1\n");
    then fail();
  end matchcontinue;
end sliceArrayVarsForCref1;

protected function makeRangeSubscripts"fold function that makes DAE.SLICE() subscripts from an ordered list of indexes"
  input Integer idx;
  input DAE.Type tyIn;
  input list<DAE.Subscript> subsIn;
  output list<DAE.Subscript> subsOut;
algorithm
  subsOut := matchcontinue(idx,tyIn,subsIn)
    local
      Integer start,stop;
      DAE.Type ty;
      list<DAE.Subscript> rest;

  case(_,_,{})
    equation
    //start a new range
  then {DAE.INDEX(DAE.RANGE(tyIn,DAE.ICONST(idx),NONE(),DAE.ICONST(idx)))};

  case(_,_,DAE.INDEX(DAE.RANGE(ty=ty,start=DAE.ICONST(start),step=NONE(),stop=DAE.ICONST(stop)))::rest)
    equation
    //extend range
    true = intEq(idx,stop+1);
  then (DAE.INDEX(DAE.RANGE(ty,DAE.ICONST(start),NONE(),DAE.ICONST(idx)))::rest);

  case(_,_,DAE.INDEX(DAE.RANGE(ty=ty,start=DAE.ICONST(start),step=NONE(),stop=DAE.ICONST(stop)))::rest)
    equation
    //start an interrupted range
    true = intGt(idx,stop+1);
  then (DAE.INDEX(DAE.RANGE(tyIn,DAE.ICONST(idx),NONE(),DAE.ICONST(idx)))::subsIn);

  else
    equation
      print("missing case in makeRangeSubscripts\n");
    then fail();
  end matchcontinue;
end makeRangeSubscripts;

protected function getScalarArrayCrefsFromReplacements
  input BackendVarTransform.VariableReplacements repl;
  output list<DAE.ComponentRef> crefsOut  = {};
protected
  DAE.ComponentRef cref;
  list<DAE.ComponentRef> crefs;
algorithm
  (crefs,_) := BackendVarTransform.getAllReplacements(repl);
  for cref in crefs loop
    if ComponentReference.crefHaveSubs(cref) and not isRangeCref(cref) then
      crefsOut := cref::crefsOut;
    end if;
  end for;
end getScalarArrayCrefsFromReplacements;


protected function getScalarArrayCrefsFromEquation"fold function to collect scalar crefs from equations"
  input BackendDAE.Equation eqIn;
  input list<DAE.ComponentRef> crefsIn;
  output list<DAE.ComponentRef> crefsOut;
protected
  list<DAE.ComponentRef> crefs;
algorithm
  (_,crefs) := BackendEquation.traverseExpsOfEquation(eqIn,getScalarArrayCrefsFromExp,{});
  crefsOut := List.unique(listAppend(crefs,crefsIn));
end getScalarArrayCrefsFromEquation;


protected function getScalarArrayCrefsFromExp"exp traverse function to collect scalar crefs from expressions"
  input DAE.Exp expIn;
  input list<DAE.ComponentRef> crefsIn;
  output DAE.Exp expOut;
  output list<DAE.ComponentRef> crefsOut;
algorithm
  (expOut,crefsOut) := matchcontinue(expIn,crefsIn)
    local
      DAE.ComponentRef cref;
      DAE.Exp exp1, exp2;
      list<DAE.ComponentRef> crefs;
  case(DAE.CREF(componentRef= cref),_)
    equation
      true = ComponentReference.crefHaveSubs(cref); // why is crefHasScalarSubscripts() true for crefs without subs
      true = ComponentReference.crefHasScalarSubscripts(cref);
      {DAE.INDEX(DAE.ICONST(_))} = ComponentReference.crefSubs(cref);
    then (expIn,(cref::crefsIn));
  case(DAE.UNARY(exp=exp1),_)
    equation
      (_,crefs) = getScalarArrayCrefsFromExp(exp1,crefsIn);
    then (expIn,crefs);
  case(DAE.BINARY(exp1=exp1,exp2=exp2),_)
    equation
      (_,crefs) = getScalarArrayCrefsFromExp(exp1,crefsIn);
      (_,crefs) = getScalarArrayCrefsFromExp(exp2,crefs);
    then (expIn,crefs);
  case(DAE.SUM(),_)
    then (expIn,crefsIn);
  else
    then (expIn,crefsIn);
  end matchcontinue;
end getScalarArrayCrefsFromExp;


//-----------------------------------------------
// The implementation to get a DAE with BackendDAE.FOR_EQUATION and unexpanded array vars.
//-----------------------------------------------

protected function unexpandArrayVariables"build non-expanded var arrays"
  input list<BackendDAE.Var> varsIn;
  input list<BackendDAE.Var> foldIn;
  output list<BackendDAE.Var> foldOut;
algorithm
  foldOut := matchcontinue(varsIn,foldIn)
    local
      BackendDAE.Var var;
      DAE.ComponentRef cref;
      list<DAE.BackendDAE.Var> rest, scalars;
  case({},_)
    then foldIn;
  case(var::rest,_)
    equation
      cref = BackendVariable.varCref(var);
      true = ComponentReference.crefHaveSubs(cref);
      (scalars,rest) = List.split1OnTrue(rest,varIsEqualCrefWithoutSubs,cref);
      cref = replaceFirstSubsInCref(cref,{DAE.INDEX(DAE.RANGE(BackendVariable.varType(var),DAE.ICONST(1),NONE(),DAE.ICONST(listLength(scalars)+1)))});
      var = BackendVariable.copyVarNewName(cref,var);
    then unexpandArrayVariables(rest,var::foldIn);
  case(var::rest,_)
    then unexpandArrayVariables(rest,var::foldIn);
  end matchcontinue;
end unexpandArrayVariables;

protected function varIsEqualCrefWithoutSubs"checks if a var is equal to the cref without considering the subscripts"
  input BackendDAE.Var varIn;
  input DAE.ComponentRef crefIn;
  output Boolean b;
protected
  DAE.ComponentRef cref;
algorithm
  cref := BackendVariable.varCref(varIn);
  b := ComponentReference.crefEqualWithoutSubs(cref,crefIn);
end varIsEqualCrefWithoutSubs;

protected function buildAccumExpInEquations"if there is an accumulation of array variables in an equation, check whether we can summarize these to an accumulated expression"
  input BackendDAE.Equation mixEq;
  input list<BackendDAE.Equation> foldIn;
  output list<BackendDAE.Equation> foldOut;
algorithm
  foldOut := matchcontinue(mixEq,foldIn)
    local
      DAE.Exp rhs, lhs;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      list<DAE.Exp> allTerms;
      list<tuple<DAE.Exp,Integer,Integer>> minmaxTerms;
  case(BackendDAE.EQUATION(exp=rhs,scalar=lhs,source=source,attr=attr),_)
    algorithm
      //handle left hand side
      allTerms := Expression.allTerms(lhs);
      minmaxTerms := List.fold(allTerms,buildAccumExpInEquations1,{});
      {lhs} := buildAccumExpInEquations2(listReverse(minmaxTerms),{});

      //handle right hand side
      allTerms := Expression.allTerms(rhs);
      minmaxTerms := List.fold(allTerms,buildAccumExpInEquations1,{});
      {rhs} := buildAccumExpInEquations2(listReverse(minmaxTerms),{});
    then BackendDAE.EQUATION(rhs,lhs,source,attr)::foldIn;
  else
    then mixEq::foldIn;
  end matchcontinue;
end buildAccumExpInEquations;

protected function buildAccumExpInEquations1"checks if a term occurs multiple times among all terms, if so update min max"
  input DAE.Exp termIn;
  input list<tuple<DAE.Exp,Integer,Integer>> minmaxTermsIn;
  output list<tuple<DAE.Exp,Integer,Integer>> minmaxTermsOut;
protected
  Integer pos, idx, min, max;
  DAE.ComponentRef cref;
  DAE.Exp term;
  list<DAE.Exp> terms;
algorithm
  try
    {cref} := Expression.extractCrefsFromExp(termIn);
    true := ComponentReference.crefHaveSubs(cref);
    pos := List.position1OnTrue(minmaxTermsIn,minmaxTermEqual,termIn);
    if intEq(pos,-1) then
      // not yet collected array cref term
      {DAE.INDEX(DAE.ICONST(idx))} := ComponentReference.crefSubs(cref);
      minmaxTermsOut := (termIn,idx,idx)::minmaxTermsIn;
    else
    // an already collected array cref term
    (term,min,max) := listGet(minmaxTermsIn,pos);
    {DAE.INDEX(DAE.ICONST(idx))} := ComponentReference.crefSubs(cref);
    minmaxTermsOut := List.replaceAt((term,intMin(idx,min),intMax(idx,max)),pos,minmaxTermsIn);
    end if;
  else
    minmaxTermsOut := (termIn,-1,-1)::minmaxTermsIn;
  end try;
end buildAccumExpInEquations1;

protected function minmaxTermEqual"checks if a term is equal to the minmaxTerm without considering the subscripts"
  input tuple<DAE.Exp,Integer,Integer> minmaxTerm;
  input DAE.Exp term;
  output Boolean b;
protected
  DAE.Exp term0;
algorithm
  (term0,_,_) := minmaxTerm;
  b := expEqualNoCrefSubs(term0, term);
end minmaxTermEqual;

protected function buildAccumExpInEquations2"sums up the terms and build accumulated expresssions if necessary"
  input list<tuple<DAE.Exp,Integer,Integer>> minmaxTerm;
  input list<DAE.Exp> foldIn;
  output list<DAE.Exp> foldOut;
algorithm
  foldOut := matchcontinue(minmaxTerm,foldIn)
    local
      Integer min, max;
      DAE.Exp exp0, exp1, iter;
      list<DAE.Exp> resExp;
      list<tuple<DAE.Exp,Integer,Integer>> rest;
  case({},{exp1})
    equation
    then {exp1};
  case((exp1,min,max)::rest,{})
    equation
    // build a sigma operator exp and start with the first term
    true = intNe(min,max);
    (_,rest) = List.split1OnTrue(rest,minmaxTermEqual,exp1);  // remove other instances of the term
    iter = DAE.CREF(DAE.CREF_IDENT("i",DAE.T_INTEGER_DEFAULT,{}),DAE.T_INTEGER_DEFAULT);
    (exp1,_) = Expression.traverseExpBottomUp(exp1,replaceSubscriptInCrefExp,{DAE.INDEX(iter)});
    exp1 = DAE.SUM(Expression.typeof(exp1),iter,DAE.ICONST(min),DAE.ICONST(max),exp1);
    resExp = buildAccumExpInEquations2(rest,{exp1});
    then resExp;
  case((exp1,min,max)::rest,{exp0})
    equation
    // build a sigma operator exp and add to folding expression
    true = intNe(min,max);
    (_,rest) = List.split1OnTrue(rest,minmaxTermEqual,exp1);  // remove other instances of the term
    iter = DAE.CREF(DAE.CREF_IDENT("i",DAE.T_INTEGER_DEFAULT,{}),DAE.T_INTEGER_DEFAULT);
    (exp1,_) = Expression.traverseExpBottomUp(exp1,replaceSubscriptInCrefExp,{DAE.INDEX(iter)});
    exp1 = DAE.SUM(Expression.typeof(exp1),iter,DAE.ICONST(min),DAE.ICONST(max),exp1);
    resExp = buildAccumExpInEquations2(rest,{DAE.BINARY(exp0,DAE.ADD(Expression.typeof(exp0)),exp1)});
    then resExp;
  case((exp1,_,_)::rest,{})
    equation
      // the first exp is a non-array cref
    resExp = buildAccumExpInEquations2(rest,{exp1});
    then resExp;
  case((exp1,_,_)::rest,{exp0})
    equation
      //add this non-array cref
      resExp = buildAccumExpInEquations2(rest,{DAE.BINARY(exp0,DAE.ADD(Expression.typeof(exp0)),exp1)});
    then resExp;
  end matchcontinue;
end buildAccumExpInEquations2;


public function replaceSubscriptInCrefExp"exp-traverse-function to replace the first occuring subscripts in a cref"
  input DAE.Exp expIn;
  input list<DAE.Subscript> subsIn;
  output DAE.Exp expOut;
  output list<DAE.Subscript> subsOut;
algorithm
  (expOut,subsOut) := matchcontinue(expIn,subsIn)
    local
      DAE.ComponentRef cref;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref, ty=ty),_)
    equation
      cref =  replaceFirstSubsInCref(cref,subsIn);
    then (DAE.CREF(cref,ty),subsIn);
  else
    then(expIn,subsIn);
  end matchcontinue;
end replaceSubscriptInCrefExp;


protected function buildBackendDAEForEquations"creates BackendDAE.FOR_EQUATION for similar equations"
  input list<BackendDAE.Equation> classEqs;
  input list<BackendDAE.Equation> foldIn;
  output list<BackendDAE.Equation> foldOut;
algorithm
  foldOut := matchcontinue(classEqs, foldIn)
    local
      Integer min, max, numCrefs;
      BackendDAE.Equation eq;
      DAE.ComponentRef cref1,cref2;
      DAE.Exp lhs,rhs, iterator;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      list<BackendDAE.Equation> similarEqs, rest, foldEqs;
      list<DAE.ComponentRef> crefs, crefs2;
      list<tuple<DAE.ComponentRef,Integer,Integer>> crefMinMax;
  case({},_)
    algorithm
      then foldIn;

case(eq::rest,_)
    algorithm
      //special case for a[i] = a[x]
      BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=attr) := eq;
      true := ComponentReference.crefEqualWithoutSubs(Expression.expCref(lhs),Expression.expCref(rhs));
            //print("found constant array-var\n");
      //get similar equations
      (similarEqs,rest) := List.separate1OnTrue(classEqs,equationEqualNoCrefSubs,eq);
        //BackendDump.dumpEquationList(similarEqs,"simEqs");
      cref1 := Expression.expCref(lhs);
      cref2 := Expression.expCref(rhs);
      // update crefs in equation
      iterator := DAE.CREF(DAE.CREF_IDENT("i",DAE.T_INTEGER_DEFAULT,{}),DAE.T_INTEGER_DEFAULT);
      lhs := BackendArrayVarTransform.replaceSubExp(Expression.crefExp(cref1),DAE.INDEX(iterator));
      rhs := BackendArrayVarTransform.replaceSubExp(Expression.crefExp(cref1),DAE.INDEX(DAE.ICONST(listLength(similarEqs)+1)));
      eq := BackendDAE.FOR_EQUATION(iterator,DAE.ICONST(1),DAE.ICONST(listLength(similarEqs)),lhs,rhs,source,attr);
        //BackendDump.dumpEquationList({eq},"got eq assignment");
      foldEqs := buildBackendDAEForEquations(rest,(eq::foldIn));
    then
      foldEqs;

  case(eq::rest,_)
    algorithm
      BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=attr) := eq;
      //get similar equations
      (similarEqs,rest) := List.separate1OnTrue(classEqs,equationEqualNoCrefSubs,eq);
        //BackendDump.dumpEquationList(similarEqs,"simEqs");
      crefs := BackendEquation.equationCrefs(eq);
      //filter array-vars that appear in every equation
      crefs2 := BackendEquation.equationCrefs(listGet(similarEqs,1));
      (crefs2,crefs,_) := List.intersection1OnTrue(crefs,crefs2,ComponentReference.crefEqual);
        //print("varCrefs: "+stringDelimitList(List.map(crefs,ComponentReference.printComponentRefStr),",")+"\n");
        //print("consCrefs: "+stringDelimitList(List.map(crefs2,ComponentReference.printComponentRefStr),",")+"\n");
      numCrefs := listLength(crefs);
      // all crefs and their minimum as well as their max iterator
      crefMinMax := List.thread3Map(listReverse(crefs),List.fill(999999999,numCrefs),List.fill(0,numCrefs),Util.make3Tuple);
      crefMinMax :=  List.fold1(similarEqs,getCrefIdcsForEquation,crefs2,crefMinMax);
      //((min,max)) := List.fold1(crefMinMax,getIterationRangesForCrefs,listLength(similarEqs),(-1,-1));
      min := 1;
      max := listLength(similarEqs);
      //print("min "+intString(min)+" max "+intString(max)+"\n");
      // update crefs in equation
      iterator := DAE.CREF(DAE.CREF_IDENT("i",DAE.T_INTEGER_DEFAULT,{}),DAE.T_INTEGER_DEFAULT);
      (BackendDAE.EQUATION(exp=lhs,scalar=rhs),_) := BackendEquation.traverseExpsOfEquation(eq,setIteratorSubscriptCrefinEquation,(crefMinMax,iterator,crefs2));
      eq := BackendDAE.FOR_EQUATION(iterator,DAE.ICONST(min),DAE.ICONST(max),lhs,rhs,source,attr);
        //BackendDump.dumpEquationList({eq},"got eq");
      foldEqs := buildBackendDAEForEquations(rest,(eq::foldIn));
    then
      foldEqs;
  else
    then foldIn;
  end matchcontinue;
end buildBackendDAEForEquations;


protected function getIterationRangesForCrefs"for all cref+minIter+maxIter, the overall min, max iterator is figured out."
  input tuple<DAE.ComponentRef,Integer,Integer> crefInfo; // a cref and their min and max index among all similar eqs
  input Integer range;
  input tuple<Integer,Integer> minmaxIn;
  output tuple<Integer,Integer> minmaxOut;
protected
  Integer min=0,min0,max0,min1,max1;
  DAE.ComponentRef cref;
algorithm
  (cref,min1,max1) := crefInfo;
  (min0,max0) := minmaxIn;
  if intEq(min0,-1) then min0 := min1;  end if;
  min := intMin(min0,min1);
  minmaxOut := (min, intMin(max1,min+range-1));
end getIterationRangesForCrefs;


protected function setIteratorSubscriptCrefinEquation"traverse function that replaces crefs in the exp according to the iterated crefMinMax"
  input DAE.Exp inExp;
  input tuple<list<tuple<DAE.ComponentRef,Integer,Integer>>,DAE.Exp,list<DAE.ComponentRef>> tplIn; //creMinMax,iterator,constCrefs
  output DAE.Exp outExp;
  output tuple<list<tuple<DAE.ComponentRef,Integer,Integer>>,DAE.Exp,list<DAE.ComponentRef>> tplOut;
algorithm
  (outExp,tplOut) := matchcontinue(inExp,tplIn)
    local
      Integer min, max;
      Absyn.Path path;
      DAE.CallAttributes attr;
      DAE.ComponentRef cref, refCref;
      DAE.Exp exp1, exp2,iterator, iterator1;
      DAE.Operator op;
      DAE.Type ty;
      list<DAE.Exp> eLst;
      list<DAE.ComponentRef> constCrefs;
      tuple<DAE.ComponentRef,Integer,Integer> refCrefMinMax;
      list<tuple<DAE.ComponentRef,Integer,Integer>> crefMinMax0, crefMinMax1;

  case(DAE.CREF(componentRef=cref,ty=ty),(crefMinMax0,iterator,constCrefs))
    algorithm
      true := not List.exist1(constCrefs,ComponentReference.crefEqual,cref);//dont substitute array-vars which are constant in the for-equations
      crefMinMax1 := {};
      for refCrefMinMax in crefMinMax0 loop
        (refCref,min,max) := refCrefMinMax;
         // if the cref fits the refCref, update the iterator
        if ComponentReference.crefEqualWithoutSubs(refCref,cref) then
          iterator1 := ExpressionSimplify.simplify(DAE.BINARY(iterator,DAE.ADD(DAE.T_INTEGER_DEFAULT),DAE.ICONST(min-1)));
          cref := replaceFirstSubsInCref(cref,{DAE.INDEX(iterator1)});
        else
          // add the non used crefs to the fold list
          crefMinMax1 := refCrefMinMax::crefMinMax1;
        end if;
      end for;
    then (DAE.CREF(cref,ty),(crefMinMax1,iterator,constCrefs));

  case(DAE.BINARY(exp1=exp1,operator=op,exp2=exp2),(crefMinMax0,iterator,constCrefs))
    algorithm
      // continue traversing
      (exp1,(crefMinMax0,iterator,constCrefs))  := setIteratorSubscriptCrefinEquation(exp1,tplIn);
      (exp2,(crefMinMax0,iterator,constCrefs))  := setIteratorSubscriptCrefinEquation(exp2,(crefMinMax0,iterator,constCrefs));
    then (DAE.BINARY(exp1,op,exp2),(crefMinMax0,iterator,constCrefs));

  case(DAE.UNARY(operator=op,exp=exp1),(crefMinMax0,iterator,constCrefs))
    algorithm
      // continue traversing
      (exp1,(crefMinMax0,iterator,constCrefs))  := setIteratorSubscriptCrefinEquation(exp1,tplIn);
    then (DAE.UNARY(op,exp1),(crefMinMax0,iterator,constCrefs));

  case(DAE.CALL(path=path,expLst=eLst,attr=attr),(crefMinMax0,iterator,constCrefs))
    algorithm
      // continue traversing
      (eLst,(crefMinMax0,iterator,constCrefs))  := List.mapFold(eLst,setIteratorSubscriptCrefinEquation,tplIn);
    then (DAE.CALL(path,eLst,attr),(crefMinMax0,iterator,constCrefs));

  else
    then (inExp,tplIn);
  end matchcontinue;
end setIteratorSubscriptCrefinEquation;


protected function getCrefIdcsForEquation"gets all crefs of the equation and dispatches the information about min and max subscript to crefMinMax"
  input BackendDAE.Equation eq;
  input list<DAE.ComponentRef> constCrefs;
  input list<tuple<DAE.ComponentRef,Integer,Integer>> crefMinMaxIn;
  output list<tuple<DAE.ComponentRef,Integer,Integer>> crefMinMaxOut;
algorithm
  crefMinMaxOut := matchcontinue(eq,constCrefs,crefMinMaxIn)
    local
      Integer pos,max,min,sub;
      DAE.ComponentRef cref, refCref;
      tuple<DAE.ComponentRef,Integer,Integer> refCrefMinMax;
      list<tuple<DAE.ComponentRef,Integer,Integer>> crefMinMax;
      list<DAE.ComponentRef> eqCrefs, crefs;
  case(BackendDAE.EQUATION(_),_,crefMinMax)
    algorithm
      eqCrefs := BackendEquation.equationCrefs(eq);
      //traverse all crefs of the equation
      eqCrefs := List.filter1OnTrue(eqCrefs,ComponentReference.crefNotInLst,constCrefs);
      for cref in eqCrefs loop
        {DAE.INDEX(DAE.ICONST(sub))} := ComponentReference.crefSubs(cref);
        pos := 1;
        for refCrefMinMax in crefMinMax loop
          (refCref,min,max) := refCrefMinMax;
          // if the cref fits the refCref, update min max
          if ComponentReference.crefEqualWithoutSubs(refCref,cref) then
            max := intMax(max,sub);
            min := intMin(min,sub);
            crefMinMax := List.replaceAt((refCref,min,max),pos,crefMinMax);
          end if;
          pos := pos+1;
        end for;
      end for;
    then crefMinMax;
  else
    then crefMinMaxIn;
  end matchcontinue;
end getCrefIdcsForEquation;

//-----------------------------------------------
//-----------------------------------------------

protected function shortenArrayVars
  input tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>> arrayCref;
  input BackendDAE.Variables arrayVars;
  input Integer size;
  input list<BackendDAE.Var> varLstIn;
  output list<BackendDAE.Var> varLstOut;
algorithm
  varLstOut := matchcontinue(arrayCref,arrayVars,size,varLstIn)
    local
      Integer subRange;
      DAE.ComponentRef headCref;
      list<BackendDAE.Var> varLst;
      list<list<BackendDAE.Var>> varLstLst;
      list<DAE.ComponentRef> tailCrefs, headsWithSubs;
  case((headCref,subRange,tailCrefs),_,_,_)
    equation
      headsWithSubs = List.map1r(List.intRange(size),ComponentReference.subscriptCrefWithInt,headCref);
      headsWithSubs = List.flatten(List.map1(headsWithSubs,joinWithCrefLst,tailCrefs));
        //print("headsWithSubs2: "+stringDelimitList(List.map(headsWithSubs,ComponentReference.printComponentRefStr),"\n|")+"\n\n");
      (varLstLst,_) = List.map1_2(headsWithSubs, BackendVariable.getVar,arrayVars);
      varLst = List.flatten(varLstLst);
  then listAppend(varLst,varLstIn);
  else
    then varLstIn;
  end matchcontinue;
end shortenArrayVars;

protected function joinWithCrefLst
  input DAE.ComponentRef cref;
  input list<DAE.ComponentRef> crefLstIn;
  output list<DAE.ComponentRef> crefLstOut;
algorithm
  crefLstOut := List.map1r(crefLstIn,ComponentReference.joinCrefs,cref);
end joinWithCrefLst;

protected function reduceLoopEquations
  input BackendDAE.Equation eqIn;
  input list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> arrayCrefs; //headCref, range, tailcrefs
  input Integer maxSize;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := matchcontinue(eqIn,arrayCrefs,maxSize)
    local
      DAE.Exp lhs,rhs, startIt, endIt;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      list<BackendDAE.IterCref> iterCrefs;
  case(BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=attr as BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs={BackendDAE.ACCUM_ITER_CREF()}))),_,_)
    equation
      // strip the higher indexes in accumulated iterations
      (lhs,_) = reduceLoopExpressions(lhs,maxSize);
      (rhs,_) = reduceLoopExpressions(rhs,maxSize);
  then BackendDAE.EQUATION(lhs,rhs,source,attr);
  else
    equation
    then eqIn;
  end matchcontinue;
end reduceLoopEquations;

protected function buildIteratedEquation
  input BackendDAE.Equation eqIn;
  input list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> arrayCrefs; //headCref, range, tailcrefs
  input list<BackendDAE.Equation> foldIn;
  output list<BackendDAE.Equation> foldOut;
algorithm
  foldOut := matchcontinue(eqIn,arrayCrefs,foldIn)
    local
      Integer startIt,endIt, maxItOffset, endRange;
      list<Integer> idxOffsets;
      DAE.Exp lhs,rhs;
      DAE.ElementSource source;
      BackendDAE.Equation eq;
      list<BackendDAE.Equation> eqLst;
      list<BackendDAE.IterCref> iterCrefs;

  case(BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs=iterCrefs as BackendDAE.ITER_CREF()::_, startIt=DAE.ICONST(startIt),endIt=DAE.ICONST(endIt)))),_,_)
    algorithm
      // handle no accumulated equations here
       //print("eq: "+BackendDump.equationString(eqIn)+"\n");
      eqLst := {};
      idxOffsets := List.fold(iterCrefs,getIterationCrefIterator,{});
      maxItOffset := List.fold(idxOffsets,intMax,listHead(idxOffsets));
      endRange := intMin(endIt,2-maxItOffset);
        //print("maxItOffset "+intString(maxItOffset)+"\n");
        //print("start "+intString(startIt)+"\n");
        //print("end "+intString(endIt)+"\n");
        //print("endRange "+intString(endRange)+"\n");
      eqLst := buildIteratedEquation1(eqIn,startIt,endRange,{});
        //print("eqsOut: "+stringDelimitList(List.map(eqLst,BackendDump.equationString),"\n")+"\n");
      eqLst := listAppend(eqLst,foldIn);
  then eqLst;
  case(BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs=BackendDAE.ACCUM_ITER_CREF()::_, startIt=DAE.ICONST(startIt),endIt=DAE.ICONST(endIt)))),_,_)
    algorithm
      // accumulated equations, remove higher subscripts, no duplication
      eq := reduceLoopEquations(eqIn,arrayCrefs,2);
    then eq::foldIn;
  else
    algorithm
      // in case there is a higher idx
      (eq,_) := BackendEquation.traverseExpsOfEquation(eqIn,limitCrefSubscripts,2);
    then eq::foldIn;
  end matchcontinue;
end buildIteratedEquation;

protected function limitCrefSubscripts
  input DAE.Exp inExp;
  input Integer maxSubIn;
  output DAE.Exp outExp;
  output Integer maxSubOut;
algorithm
  (outExp,maxSubOut) := matchcontinue(inExp,maxSubIn)
    local
      Integer idx;
      DAE.ComponentRef cref;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref,ty=ty),_)
    equation
      {DAE.INDEX(DAE.ICONST(idx))} = ComponentReference.crefSubs(cref);
      true = intGt(idx,maxSubIn);
      cref = replaceFirstSubsInCref(cref,{DAE.INDEX(DAE.ICONST(maxSubIn))});
    then (DAE.CREF(cref,ty),maxSubIn);
  else
    then (inExp,maxSubIn);
  end matchcontinue;
end limitCrefSubscripts;

protected function buildIteratedEquation1
  input BackendDAE.Equation eqIn;
  input Integer idx;
  input Integer maxIdx; // used to shorten constant interators
  input list<BackendDAE.Equation> eqLstIn;
  output list<BackendDAE.Equation> eqLstOut;
algorithm
  eqLstOut := matchcontinue(eqIn,idx,maxIdx,eqLstIn)
    local
      DAE.Exp lhs,rhs, startIt, endIt;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      BackendDAE.Equation eq;
      list<BackendDAE.IterCref> iterCrefs;
      list<BackendDAE.Equation> eqLst;
  case(BackendDAE.EQUATION(exp=lhs,scalar=rhs,source=source,attr=attr as BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs=iterCrefs))),_,_,eqLst)
    equation
      // its a loop equation
      true = intLe(idx,maxIdx);
      (lhs,(_,_,iterCrefs)) = Expression.traverseExpTopDown(lhs,setIteratedSubscriptInCref,(DAE.ICONST(idx),maxIdx,iterCrefs));
      (rhs,(_,_,iterCrefs)) = Expression.traverseExpTopDown(rhs,setIteratedSubscriptInCref,(DAE.ICONST(idx),maxIdx,iterCrefs));
      if Expression.expEqual(lhs,rhs) then
        eqLst = eqLst;
      else
        eqLst = buildIteratedEquation1(eqIn,idx+1,maxIdx,BackendDAE.EQUATION(lhs,rhs,source,attr)::eqLst);
      end if;
  then eqLst;
  else
    then eqLstIn;
  end matchcontinue;
end buildIteratedEquation1;

public function setIteratedSubscriptInCref "sets the subscript in the cref according the given iteration idx"
  input DAE.Exp expIn;
  input tuple<DAE.Exp, Integer, list<BackendDAE.IterCref>> tplIn; //idx, maxIdx, iterCrefs
  output DAE.Exp expOut;
  output Boolean cont;
  output tuple<DAE.Exp, Integer, list<BackendDAE.IterCref>> tplOut;
algorithm
  (expOut,cont,tplOut) := matchcontinue(expIn,tplIn)
    local
     Integer idxOffset,maxIdx,constIdx;
     String constIdxOffset;
     DAE.ComponentRef cref;
     DAE.Exp itExp, idxExp, idxExp0;
     DAE.Type ty;
     list<BackendDAE.IterCref> iterCrefs,restIterCrefs;
  case(_,(_,_,{}))
    then (expIn,false,tplIn);
  case(DAE.CREF(componentRef=cref, ty=ty),(idxExp0,maxIdx,iterCrefs))
    equation
      // iterated cref in a for-loop
      (BackendDAE.ITER_CREF(iterator=DAE.ICONST(idxOffset))::restIterCrefs,iterCrefs) = List.split1OnTrue(iterCrefs, isIterCref, cref);
      idxExp = DAE.BINARY(idxExp0, DAE.ADD(ty=DAE.T_INTEGER_DEFAULT), DAE.ICONST(idxOffset));
        //print("for "+ComponentReference.printComponentRefStr(cref)+" offset: "+intString(idxOffset)+" idxExp: "+ExpressionDump.printExpStr(idxExp)+"\n");
      idxExp = ExpressionSimplify.simplify(idxExp);
      cref = replaceFirstSubsInCref(cref,{DAE.INDEX(idxExp)});
  then (DAE.CREF(cref, ty),true,(idxExp0,maxIdx,listAppend(restIterCrefs,iterCrefs)));

  case(DAE.CREF(componentRef=cref, ty=ty),(idxExp0,maxIdx,iterCrefs))
    equation
      // constant cref in a for-loop
      (BackendDAE.ITER_CREF(iterator=DAE.SCONST(constIdxOffset))::restIterCrefs,iterCrefs) = List.split1OnTrue(iterCrefs, isIterCref, cref);
      constIdx = stringInt(constIdxOffset);
      idxExp = DAE.ICONST(intMin(constIdx,maxIdx));
        //print("for "+ComponentReference.printComponentRefStr(cref)+" constIdx: "+intString(constIdx)+" idxExp: "+ExpressionDump.printExpStr(idxExp)+"\n");
      cref = replaceFirstSubsInCref(cref,{DAE.INDEX(idxExp)});
  then (DAE.CREF(cref, ty),true,(idxExp0,maxIdx,listAppend(restIterCrefs,iterCrefs)));

  case(DAE.CREF(componentRef=cref, ty=ty),(idxExp0,maxIdx,iterCrefs))
    equation
      // accumulated expressions
      (BackendDAE.ACCUM_ITER_CREF()::restIterCrefs,iterCrefs) = List.split1OnTrue(iterCrefs, isIterCref, cref);
      cref = replaceFirstSubsInCref(cref, {DAE.INDEX(idxExp0)});
  then (DAE.CREF(cref, ty),true,(idxExp0,maxIdx,listAppend(restIterCrefs,iterCrefs)));
  else
     then (expIn,true,tplIn);
  end matchcontinue;
end setIteratedSubscriptInCref;


public function replaceFirstSubsInCref"replaces the first occuring subscript in the cref"
  input DAE.ComponentRef crefIn;
  input list<DAE.Subscript> subs;
  output DAE.ComponentRef crefOut;
algorithm
  crefOut := matchcontinue(crefIn,subs)
    local
      DAE.Ident ident;
      DAE.Type identType;
      list<DAE.Subscript> subscriptLst;
      DAE.ComponentRef cref;
  case(DAE.CREF_QUAL(ident=ident, identType=identType, subscriptLst=subscriptLst, componentRef=cref),_)
    equation
      if List.hasOneElement(subscriptLst) then  subscriptLst = subs; end if;
      cref = replaceFirstSubsInCref(cref,subs);
    then DAE.CREF_QUAL(ident, identType, subscriptLst, cref);
  case(DAE.CREF_IDENT(ident=ident, identType=identType, subscriptLst=subscriptLst),_)
    equation
      if List.hasOneElement(subscriptLst) then  subscriptLst = subs; end if;
    then DAE.CREF_IDENT(ident, identType, subscriptLst);
  else
    then crefIn;
  end matchcontinue;
end replaceFirstSubsInCref;

public function reduceLoopExpressions "strip the higher indexes in accumulated iterations"
  input DAE.Exp expIn;
  input Integer maxSub;
  output DAE.Exp expOut;
  output Boolean notRemoved;
algorithm
  (expOut,notRemoved) := matchcontinue(expIn,maxSub)
    local
      Boolean b, b1, b2;
      DAE.ComponentRef cref;
      DAE.Exp exp, exp1, exp2;
      DAE.Type ty;
      DAE.Operator op;
  case(DAE.CREF(componentRef=cref),_)
    equation
      b = intLe(getIndexSubScript(listHead(ComponentReference.crefSubs(cref))),maxSub);
        //print("crerfsub: "+intString(getIndexSubScript(listHead(ComponentReference.crefSubs(cref))))+" <> "+intString(maxSub)+"\n");
        //print("reduce cref: "+ComponentReference.crefStr(cref)+" is higher sub: "+boolString(b)+"\n");
  then (expIn,b);

  case(DAE.BINARY(exp1=exp1, operator=op, exp2=exp2),_)
    equation
      (exp1,b1) = reduceLoopExpressions(exp1,maxSub);
      (exp2,b2) = reduceLoopExpressions(exp2,maxSub);
        //print("exp: "+ExpressionDump.printExpStr(expIn)+" b1: "+boolString(b1)+" b2: "+boolString(b2)+"\n");
      if b1 and not b2 then
        exp = exp1;
      elseif b2 and not b1 then
        exp = exp2;
      else
        exp = DAE.BINARY(exp1,op,exp2);
      end if;
        //print("expOut: "+ExpressionDump.printExpStr(exp)+"\n");
  then (exp,boolOr(b1,b2));

  case(DAE.UNARY(operator=op, exp=exp),_)
    equation
      (exp,b) = reduceLoopExpressions(exp,maxSub);
  then (exp,b);
   else
     equation
         //print("else: "+ExpressionDump.dumpExpStr(expIn,0)+"\n");
     then (expIn,true);
  end matchcontinue;
end reduceLoopExpressions;

protected function addLoopInfosForClassEqs
  input list<BackendDAE.Equation> classEqs;
  input list<DAE.ComponentRef> arrayCrefs;
  input tuple<Integer,list<BackendDAE.Equation>> foldIn;
  output tuple<Integer,list<BackendDAE.Equation>> foldOut;
algorithm
  foldOut := matchcontinue(classEqs, arrayCrefs, foldIn)
    local
      BackendDAE.Equation eq;
      BackendDAE.LoopInfo loopInfo;
      list<BackendDAE.Equation> similarEqs, rest, foldEqs;
      list<DAE.ComponentRef> crefs, arrCrefs, nonArrayCrefs;
      list<DAE.Subscript> subs;
      list<Integer> idxs;
      list<BackendDAE.IterCref> iterCrefs;
      Integer start, range, idx;
      tuple<Integer,list<BackendDAE.Equation>> tpl;
  case({},_,_)
    equation
      then foldIn;
  case(eq::rest,_,(idx,foldEqs))
    equation
      //get similar equations
      (similarEqs,rest) = List.separate1OnTrue(classEqs,equationEqualNoCrefSubs,eq);
        //BackendDump.dumpEquationList(similarEqs,"similarEqs");
      range = listLength(similarEqs)-1;
        //print("range: "+intString(range)+"\n");
      (iterCrefs,start) = getIterCrefsFromEqs(similarEqs,arrayCrefs);
        //print("iterCrfs "+stringDelimitList(List.map(iterCrefs,BackendDump.printIterCrefStr),"\n")+"\n");
      loopInfo = BackendDAE.LOOP(idx,DAE.ICONST(start),DAE.ICONST(intAdd(start,range)),listReverse(iterCrefs));
        //print("loopInfo "+BackendDump.printLoopInfoStr(loopInfo)+"\n");
      eq = setLoopInfoInEq(loopInfo,eq);
        //print("eq "+BackendDump.equationString(eq)+"\n");
      tpl = addLoopInfosForClassEqs(rest, arrayCrefs, (idx+1,eq::foldEqs));
    then
      tpl;
  else
    then foldIn;
  end matchcontinue;
end addLoopInfosForClassEqs;

protected function addLoopInfosForMixEqs
  input list<BackendDAE.Equation> mixEqs;
  input list<DAE.ComponentRef> arrayCrefs;
  input tuple<Integer,list<BackendDAE.Equation>> foldIn;
  output tuple<Integer,list<BackendDAE.Equation>> foldOut;
algorithm
  foldOut := matchcontinue(mixEqs, arrayCrefs, foldIn)
    local
      BackendDAE.Equation eq;
      BackendDAE.LoopInfo loopInfo;
      list<BackendDAE.Equation> similarEqs, rest, foldEqs;
      list<DAE.ComponentRef> crefs, arrCrefs, nonArrayCrefs;
      list<DAE.Subscript> subs;
      list<Integer> idxs;
      list<BackendDAE.IterCref> iterCrefs;
      Integer startIt, range, endIt, idx;
      tuple<Integer,list<BackendDAE.Equation>> tpl;
  case({},_,_)
    equation
      then foldIn;
  case(eq::rest,_,(idx,foldEqs))
    equation
      //get similar equations
      (similarEqs,rest) = List.separate1OnTrue(mixEqs,equationEqualNoCrefSubs,eq);
        //BackendDump.dumpEquationList(similarEqs,"similarEqs");
      range = listLength(similarEqs)-1;
        //print("range: "+intString(range)+"\n");
      if intNe(range,0) then
        // there are iteraded equations
        (iterCrefs,startIt) = getIterCrefsFromEqs(similarEqs,arrayCrefs);
          //print("iters "+stringDelimitList(List.map(iterCrefs,BackendDump.printIterCrefStr),"\n")+"\n");
        loopInfo = BackendDAE.LOOP(idx,DAE.ICONST(startIt),DAE.ICONST(intAdd(startIt,range)),iterCrefs);
      else
        // there is an iterated operation e.g. x[1]+x[2]+x[3]+...
        (iterCrefs,startIt,endIt) = getAccumulatedIterCrefsFromEqs(similarEqs,arrayCrefs);
        if listEmpty(iterCrefs) then loopInfo = BackendDAE.NO_LOOP();
        else loopInfo = BackendDAE.LOOP(idx,DAE.ICONST(startIt),DAE.ICONST(endIt),iterCrefs);
        end if;
      end if;
      eq = setLoopInfoInEq(loopInfo,eq);
      tpl = addLoopInfosForMixEqs(rest, arrayCrefs, (idx+1,eq::foldEqs));
    then
      tpl;
  else
    then foldIn;
  end matchcontinue;
end addLoopInfosForMixEqs;

protected function getIterCrefsFromEqs
  input list<BackendDAE.Equation> eqs;
  input list<DAE.ComponentRef> arrCrefs;
  output list<BackendDAE.IterCref> iterCrefs;
  output Integer start;
protected
  list<DAE.ComponentRef> crefs;
  list<DAE.Subscript> subs;
  list<Integer> idxs, idxs0 = {};
  list<list<Integer>> idxLst;
  list<DAE.Exp> idxExps;
  Integer min = 1, max = 1;
algorithm
  idxLst := {};
  for eq in eqs loop
    crefs := BackendEquation.equationCrefs(eq);
    crefs := List.filter1OnTrue(crefs,crefPartlyEqualToCrefs,arrCrefs);
    subs := List.flatten(List.map(crefs,ComponentReference.crefSubs));
    idxs := List.map(subs,getIndexSubScript);
      //print("idxs "+stringDelimitList(List.map(idxs,intString),", ")+"\n");
    if listEmpty(idxLst) then idxLst := List.map(idxs,List.create);
    else idxLst := List.threadMap(idxs,idxLst,List.cons); end if;
      //print("idxLst "+stringDelimitList(List.map(idxLst,intLstString),"\n")+"\n");
    min := intMin(List.fold(idxs,intMin,listHead(idxs)),min);
      //print("min "+intString(min)+"\n");
  end for;
    //print("idxLst! "+stringDelimitList(List.map(idxLst,intLstString),"\n")+"\n");
  idxExps := List.map(idxLst,getIterCrefsFromEqs1);
  iterCrefs := List.threadMap(crefs,idxExps,makeIterCref);
  start := min;
end getIterCrefsFromEqs;

protected function getIterCrefsFromEqs1
  input list<Integer> iLstIn;
  output DAE.Exp eOut;
protected
  DAE.Exp e;
  Integer min,max,range;
algorithm
  if intEq(listLength(List.unique(iLstIn)),1) then
    //the iterated var does not change
    e := DAE.SCONST(intString(listGet(iLstIn,1)));
  else
    //get the offset
    min := List.fold(iLstIn,intMin,listHead(iLstIn));
    max := List.fold(iLstIn,intMax,listHead(iLstIn));
    range := listLength(iLstIn);
    e := DAE.ICONST(min-1);
  end if;
  eOut := e;
end getIterCrefsFromEqs1;

protected function intLstString
  input list<Integer> i1;
  output String s;
algorithm
  s := stringDelimitList(List.map(i1,intString),",");
end intLstString;

protected function intDiff
  input Integer i1;
  input Integer i2;
  output Integer i3;
algorithm
  i3 := intAbs(intSub(i1,i2));
end intDiff;

protected function getAccumulatedIterCrefsFromEqs
  input list<BackendDAE.Equation> eqs;
  input list<DAE.ComponentRef> arrCrefs;
  output list<BackendDAE.IterCref> iterCrefs;
  output Integer startIt;
  output Integer endIt;
protected
  list<DAE.ComponentRef> crefs;
  list<DAE.Subscript> subs;
  list<Integer> idxs,idxs0 = {};
  list<DAE.Exp> idxExps;
  Integer min = 1, max = 1;
algorithm
  for eq in eqs loop
    crefs := BackendEquation.equationCrefs(eq);
    crefs := List.filter1OnTrue(crefs,crefPartlyEqualToCrefs,arrCrefs);
    //print("shared Crefs: "+stringDelimitList(List.map(crefs,ComponentReference.printComponentRefStr),"\n|")+"\n\n");
    subs := List.flatten(List.map(crefs,ComponentReference.crefSubs));
    idxs := List.map(subs,getIndexSubScript);
    //print("idxs "+stringDelimitList(List.map(idxs,intString),", ")+"\n");
    min := List.fold(idxs,intMin,listHead(idxs));
    max := List.fold(idxs,intMax,listHead(idxs));
  end for;
    //print("min "+intString(min)+" max "+intString(max)+"\n");
  if intNe(min,max) then
    iterCrefs := {BackendDAE.ACCUM_ITER_CREF(listHead(crefs),DAE.ADD(DAE.T_REAL_DEFAULT))};
  else
    iterCrefs := {};
  end if;
  startIt := min;
  endIt := max;
end getAccumulatedIterCrefsFromEqs;

protected function getIndexSubScript
  input DAE.Subscript sub;
  output Integer int;
algorithm
  DAE.INDEX(DAE.ICONST(int)) := sub;
end getIndexSubScript;

protected function dispatchLoopEquations
  input BackendDAE.Equation eqIn;
  input list<DAE.ComponentRef> arrayCrefs; //headCrefs
  input tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tplIn; //classEqs,mixEqs,nonArrEqs
  output tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tplOut;//classEqs,mixEqs,nonArrEqs
algorithm
  tplOut := matchcontinue(eqIn,arrayCrefs,tplIn)
    local
      list<BackendDAE.Equation> classEqs,mixEqs,nonArrEqs;
      list<DAE.ComponentRef> crefs, arrCrefs, nonArrCrefs;
      tuple<list<BackendDAE.Equation>,list<BackendDAE.Equation>,list<BackendDAE.Equation>> tpl;
    case(_,_,(classEqs,mixEqs,nonArrEqs))
      equation
        crefs = BackendEquation.equationCrefs(eqIn);
        (arrCrefs,nonArrCrefs) = List.separate1OnTrue(crefs,crefPartlyEqualToCrefs,arrayCrefs);
        if listEmpty(nonArrCrefs) then
          classEqs = eqIn::classEqs;
        elseif listEmpty(arrCrefs) then
          nonArrEqs = eqIn::nonArrEqs;
        else
          mixEqs = eqIn::mixEqs;
        end if;
      then (classEqs,mixEqs,nonArrEqs);
  end matchcontinue;
end dispatchLoopEquations;

protected function crefPartlyEqualToCrefs
  input DAE.ComponentRef cref0;
  input list<DAE.ComponentRef> crefLst;
  output Boolean b;
algorithm
  b := List.exist1(crefLst,crefPartlyEqual,cref0);
end crefPartlyEqualToCrefs;

protected function crefPartlyEqual
  input DAE.ComponentRef cref0;
  input DAE.ComponentRef cref1;
  output Boolean partlyEq;
algorithm
  partlyEq := matchcontinue(cref0,cref1)
    local
      Boolean b;
      DAE.ComponentRef cref01, cref11;
  case(DAE.CREF_IDENT(), DAE.CREF_IDENT())
      then cref0.ident ==cref1.ident;
  case(DAE.CREF_QUAL(componentRef=cref01), DAE.CREF_QUAL(componentRef=cref11))
    equation
      if cref0.ident ==cref1.ident then b = crefPartlyEqual(cref01,cref11);
      else  b = false;
      end if;
    then b;
  case(DAE.CREF_QUAL(), DAE.CREF_IDENT())
      then cref0.ident ==cref1.ident;
  case(DAE.CREF_IDENT(), DAE.CREF_QUAL())
      then cref0.ident ==cref1.ident;
  else
    then false;
  end matchcontinue;
end crefPartlyEqual;

protected function getArrayVarCrefs"gets the array-cref and its dimension from a var."
  input BackendDAE.Var varIn;
  input tuple<list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>>,list<BackendDAE.Var>> tplIn; //{headCref,range,tailcrefs},arrVarlst
  output tuple<list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>>,list<BackendDAE.Var>> tplOut;
algorithm
  tplOut := matchcontinue(varIn,tplIn)
    local
      Integer idx;
      list<Integer> ranges;
      list<BackendDAE.Var> arrVars;
      DAE.ComponentRef cref, crefHead, crefTail;
      Option<DAE.ComponentRef> crefTailOpt;
      list<DAE.ComponentRef> crefLst;
      list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> tplLst;
      tuple<list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>>,list<BackendDAE.Var>> tpl;
  case(BackendDAE.VAR(varName=cref),(tplLst,arrVars))
    equation
    true = ComponentReference.isArrayElement(cref);
    (crefHead,idx,crefTailOpt) = ComponentReference.stripArrayCref(cref);
    if Util.isSome(crefTailOpt) then
      crefLst = {Util.getOption(crefTailOpt)};
    else
      crefLst = {};
    end if;
    (tplLst,arrVars) = addToArrayCrefLst(tplLst,varIn,(crefHead,idx,crefLst),{},arrVars);
    tpl = (tplLst,arrVars);
  then tpl;
  else
    then tplIn;
  end matchcontinue;
end getArrayVarCrefs;

protected function addToArrayCrefLst"checks if the tplRef-cref is already in the list, if not append, if yes update index"
  input list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> tplLstIn;
  input BackendDAE.Var varIn;
  input tuple<DAE.ComponentRef, Integer,list<DAE.ComponentRef>> tplRef;
  input list<tuple<DAE.ComponentRef, Integer,list<DAE.ComponentRef>>> tplLstFoldIn;
  input list<BackendDAE.Var> varLstIn;
  output list<tuple<DAE.ComponentRef, Integer,list<DAE.ComponentRef>>> tplLstFoldOut;
  output list<BackendDAE.Var> varLstOut;
algorithm
  (tplLstFoldOut,varLstOut) := matchcontinue(tplLstIn,varIn,tplRef,tplLstFoldIn,varLstIn)
    local
      Integer idx0,idx1;
      list<BackendDAE.Var> varLst;
      DAE.ComponentRef cref0,cref1,crefTailRef;
      list<tuple<DAE.ComponentRef,Integer,list<DAE.ComponentRef>>> rest, tplLst;
      list<DAE.ComponentRef> tailCrefs0, tailCrefs1;
  case((cref0,idx0,tailCrefs0)::rest,_,(cref1,idx1,{crefTailRef}),_,_)
    equation
    // this cref already exist, update idx, append tailCrefs if necessary
    true = ComponentReference.crefEqual(cref0,cref1);
    if List.notMember(crefTailRef,tailCrefs0) then
      tailCrefs0 = crefTailRef::tailCrefs0;
      //append var with new tail
      varLst =varIn::varLstIn;
    else
      varLst = varLstIn;
    end if;
    tplLst = (cref0,intMax(idx0,idx1),tailCrefs0)::rest;
    tplLst = listAppend(listReverse(tplLst),tplLstFoldIn);
  then (tplLst,varLst);

  case((cref0,idx0,tailCrefs0)::rest,_,(cref1,idx1,tailCrefs1),_,_)
    equation
      // this cref is not the same, continue
    false = ComponentReference.crefEqual(cref0,cref1);
    (tplLst,varLst) = addToArrayCrefLst(rest,varIn,tplRef,(cref0,idx0,tailCrefs0)::tplLstFoldIn,varLstIn);
  then (tplLst,varLst);

  case({},_,(cref1,idx1,tailCrefs1),_,_)
    equation
      // this cref is new, append
    tplLst = (cref1,idx1,tailCrefs1)::tplLstFoldIn;
  then (tplLst,varIn::varLstIn);

  end matchcontinue;
end addToArrayCrefLst;


protected function getArrayVars
  input BackendDAE.Var varIn;
  input tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> tplIn; //non-array vars,arrayVars
  output tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> tplOut;
algorithm
  tplOut := matchcontinue(varIn,tplIn)
    local
      DAE.ComponentRef cref;
      list<BackendDAE.Var> varLstIn, arrVarLstIn;
  case(BackendDAE.VAR(varName=cref),(varLstIn, arrVarLstIn))
    equation
    true = ComponentReference.isArrayElement(cref);
  then(varLstIn, varIn::arrVarLstIn);
  case(_,(varLstIn, arrVarLstIn))
    equation
  then(varIn::varLstIn, arrVarLstIn);
  end matchcontinue;
end getArrayVars;

protected function setLoopInfoInEquationAttributes
  input BackendDAE.LoopInfo loopInfo;
  input BackendDAE.EquationAttributes eqAttIn;
  output BackendDAE.EquationAttributes eqAttOut;
protected
  Boolean differentiated;
  BackendDAE.EquationKind kind;
  BackendDAE.EQUATION_ATTRIBUTES attrs;
algorithm
  BackendDAE.EQUATION_ATTRIBUTES(differentiated=differentiated, kind=kind) := eqAttIn;
  eqAttOut := BackendDAE.EQUATION_ATTRIBUTES(differentiated, kind, loopInfo);
end setLoopInfoInEquationAttributes;

protected function setLoopInfoInEq
  input BackendDAE.LoopInfo loopInfo;
  input BackendDAE.Equation eqIn;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := match(loopInfo,eqIn)
    local
      DAE.Exp e11,e12;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
    case (_,BackendDAE.EQUATION(exp=e11, scalar=e12, source=source, attr=attr))
      equation
        attr = setLoopInfoInEquationAttributes(loopInfo,attr);
    then BackendDAE.EQUATION(e11, e12, source, attr=attr);
  end match;
end setLoopInfoInEq;

protected function makeIterCref "makes a IteratedCref with the given cref and iterator exp."
  input DAE.ComponentRef cref;
  input DAE.Exp exp;
  output BackendDAE.IterCref itcref;
algorithm
  itcref := BackendDAE.ITER_CREF(cref,exp);
end makeIterCref;

public function equationEqualNoCrefSubs "
  Returns true if two equations are equal without considering subscripts"
  input BackendDAE.Equation e1;
  input BackendDAE.Equation e2;
  output Boolean res;
algorithm
  res := matchcontinue (e1, e2)
    local
      DAE.Exp e11, e12, e21, e22, exp1, exp2;
      DAE.ComponentRef cr1, cr2;
      DAE.Algorithm alg1, alg2;
      list<DAE.Exp> explst1, explst2, terms1,terms2,commTerms;
      list<DAE.ComponentRef> crefs1,crefs2,commCrefs;
    case (_, _) equation
      true = referenceEq(e1, e2);
    then true;
    case (BackendDAE.EQUATION(exp=e11, scalar=e12), BackendDAE.EQUATION(exp=e21, scalar=e22)) equation
      if boolAnd(expEqualNoCrefSubs(e11, e21), expEqualNoCrefSubs(e12, e22)) then
        //its completely identical
        res=true;
      else
        // at least the crefs should be equal
        crefs1 = BackendEquation.equationCrefs(e1);
        crefs2 = BackendEquation.equationCrefs(e2);
        commCrefs = List.intersectionOnTrue(crefs1,crefs2,ComponentReference.crefEqualWithoutSubs);
        if intEq(listLength(crefs1),listLength(commCrefs)) and intEq(listLength(crefs2),listLength(commCrefs)) then
          //compare terms
          terms1 = listAppend(Expression.allTerms(e11),Expression.allTerms(e12));
          terms2 = listAppend(Expression.allTerms(e21),Expression.allTerms(e22));
            //print("We have to check the terms:\n");
            //print("terms1: "+stringDelimitList(List.map(terms1,ExpressionDump.printExpStr),"| ")+"\n");
            //print("terms2: "+stringDelimitList(List.map(terms2,ExpressionDump.printExpStr),"| ")+"\n");
          (commTerms,terms1,terms2) = List.intersection1OnTrue(terms1,terms2,expEqualNoCrefSubs);
          res =  listEmpty(terms1) and listEmpty(terms2);
            //print("is it the same: "+boolString(res)+"\n");
        else
          res = false;
        end if;
      end if;
    then res;
    case (BackendDAE.ARRAY_EQUATION(left=e11, right=e12), BackendDAE.ARRAY_EQUATION(left=e21, right=e22)) equation
      res = boolAnd(expEqualNoCrefSubs(e11, e21), expEqualNoCrefSubs(e12, e22));
    then res;
    case (BackendDAE.COMPLEX_EQUATION(left=e11, right=e12), BackendDAE.COMPLEX_EQUATION(left=e21, right=e22)) equation
      res = boolAnd(expEqualNoCrefSubs(e11, e21), expEqualNoCrefSubs(e12, e22));
    then res;
    case (BackendDAE.SOLVED_EQUATION(componentRef=cr1, exp=exp1), BackendDAE.SOLVED_EQUATION(componentRef=cr2, exp=exp2)) equation
      res = boolAnd(ComponentReference.crefEqualWithoutSubs(cr1, cr2), expEqualNoCrefSubs(exp1, exp2));
    then res;
    case (BackendDAE.RESIDUAL_EQUATION(exp=exp1), BackendDAE.RESIDUAL_EQUATION(exp=exp2)) equation
      res = expEqualNoCrefSubs(exp1, exp2);
    then res;
    case (BackendDAE.ALGORITHM(alg=alg1), BackendDAE.ALGORITHM(alg=alg2)) equation
      explst1 = Algorithm.getAllExps(alg1);
      explst2 = Algorithm.getAllExps(alg2);
      res = List.isEqualOnTrue(explst1, explst2, expEqualNoCrefSubs);
    then res;
    case (BackendDAE.WHEN_EQUATION(whenEquation = BackendDAE.WHEN_EQ(left=cr1, right=exp1)), BackendDAE.WHEN_EQUATION(whenEquation=BackendDAE.WHEN_EQ(left=cr2, right=exp2))) equation
      res = boolAnd(ComponentReference.crefEqualWithoutSubs(cr1, cr2), expEqualNoCrefSubs(exp1, exp2));
    then res;
    else false;
  end matchcontinue;
end equationEqualNoCrefSubs;


public function expEqualNoCrefSubs
  "Returns true if the two expressions are equal, otherwise false."
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  output Boolean outEqual;
algorithm
  // Return true if the references are the same.
  if referenceEq(inExp1, inExp2) then
    outEqual := true;
    return;
  end if;

  // Return false if the expressions are not of the same type.
  if valueConstructor(inExp1) <> valueConstructor(inExp2) then
    outEqual := false;
    return;
  end if;

  // Otherwise, check if the expressions are equal or not.
  // Since the expressions have already been verified to be of the same type
  // above we can match on only one of them to allow the pattern matching to
  // optimize this to jump directly to the correct case.
  outEqual := match(inExp1)
    local
      Integer i;
      Real r;
      String s;
      Boolean b;
      Absyn.Path p;
      DAE.Exp e, e1, e2;
      Option<DAE.Exp> oe;
      list<DAE.Exp> expl;
      list<list<DAE.Exp>> mexpl;
      DAE.Operator op;
      DAE.ComponentRef cr;
      DAE.Type ty;

    case DAE.ICONST()
      algorithm
        DAE.ICONST(integer = i) := inExp2;
      then
        inExp1.integer == i;

    case DAE.RCONST()
      algorithm
        DAE.RCONST(real = r) := inExp2;
      then
        inExp1.real == r;

    case DAE.SCONST()
      algorithm
        DAE.SCONST(string = s) := inExp2;
      then
        inExp1.string == s;

    case DAE.BCONST()
      algorithm
        DAE.BCONST(bool = b) := inExp2;
      then
        inExp1.bool == b;

    case DAE.ENUM_LITERAL()
      algorithm
        DAE.ENUM_LITERAL(name = p) := inExp2;
      then
        Absyn.pathEqual(inExp1.name, p);

    case DAE.CREF()
      algorithm
        DAE.CREF(componentRef = cr) := inExp2;
      then
        ComponentReference.crefEqualWithoutSubs(inExp1.componentRef, cr);

    case DAE.ARRAY()
      algorithm
        DAE.ARRAY(ty = ty, array = expl) := inExp2;
      then
        valueEq(inExp1.ty, ty) and expEqualNoCrefSubsList(inExp1.array, expl);

    case DAE.MATRIX()
      algorithm
        DAE.MATRIX(ty = ty, matrix = mexpl) := inExp2;
      then
        valueEq(inExp1.ty, ty) and expEqualNoCrefSubsListList(inExp1.matrix, mexpl);

    case DAE.BINARY()
      algorithm
        DAE.BINARY(exp1 = e1, operator = op, exp2 = e2) := inExp2;
      then
        Expression.operatorEqual(inExp1.operator, op) and
        expEqualNoCrefSubs(inExp1.exp1, e1) and
        expEqualNoCrefSubs(inExp1.exp2, e2);

    case DAE.LBINARY()
      algorithm
        DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2) := inExp2;
      then
        Expression.operatorEqual(inExp1.operator, op) and
        expEqualNoCrefSubs(inExp1.exp1, e1) and
        expEqualNoCrefSubs(inExp1.exp2, e2);

    case DAE.UNARY()
      algorithm
        DAE.UNARY(exp = e, operator = op) := inExp2;
      then
        Expression.operatorEqual(inExp1.operator, op) and
        expEqualNoCrefSubs(inExp1.exp, e);

    case DAE.LUNARY()
      algorithm
        DAE.LUNARY(exp = e, operator = op) := inExp2;
      then
        Expression.operatorEqual(inExp1.operator, op) and
        expEqualNoCrefSubs(inExp1.exp, e);

    case DAE.RELATION()
      algorithm
        DAE.RELATION(exp1 = e1, operator = op, exp2 = e2) := inExp2;
      then
        Expression.operatorEqual(inExp1.operator, op) and
        expEqualNoCrefSubs(inExp1.exp1, e1) and
        expEqualNoCrefSubs(inExp1.exp2, e2);

    case DAE.IFEXP()
      algorithm
        DAE.IFEXP(expCond = e, expThen = e1, expElse = e2) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.expCond, e) and
        expEqualNoCrefSubs(inExp1.expThen, e1) and
        expEqualNoCrefSubs(inExp1.expElse, e2);

    case DAE.CALL()
      algorithm
        DAE.CALL(path = p, expLst = expl) := inExp2;
      then
        Absyn.pathEqual(inExp1.path, p) and
        expEqualNoCrefSubsList(inExp1.expLst, expl);

    case DAE.RECORD()
      algorithm
        DAE.RECORD(path = p, exps = expl) := inExp2;
      then
        Absyn.pathEqual(inExp1.path, p) and
        expEqualNoCrefSubsList(inExp1.exps, expl);

    case DAE.PARTEVALFUNCTION()
      algorithm
        DAE.PARTEVALFUNCTION(path = p, expList = expl) := inExp2;
      then
        Absyn.pathEqual(inExp1.path, p) and
        expEqualNoCrefSubsList(inExp1.expList, expl);

    case DAE.RANGE()
      algorithm
        DAE.RANGE(start = e1, step = oe, stop = e2) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.start, e1) and
        expEqualNoCrefSubs(inExp1.stop, e2) and
        expEqualNoCrefSubsOpt(inExp1.step, oe);

    case DAE.TUPLE()
      algorithm
        DAE.TUPLE(PR = expl) := inExp2;
      then
        expEqualNoCrefSubsList(inExp1.PR, expl);

    case DAE.CAST()
      algorithm
        DAE.CAST(ty = ty, exp = e) := inExp2;
      then
        valueEq(inExp1.ty, ty) and expEqualNoCrefSubs(inExp1.exp, e);

    case DAE.ASUB()
      algorithm
        DAE.ASUB(exp = e, sub = expl) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.exp, e) and expEqualNoCrefSubsList(inExp1.sub, expl);

    case DAE.SIZE()
      algorithm
        DAE.SIZE(exp = e, sz = oe) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.exp, e) and expEqualNoCrefSubsOpt(inExp1.sz, oe);

    case DAE.REDUCTION()
      // Reductions contain too much information to compare in a sane manner.
      then valueEq(inExp1, inExp2);

    case DAE.LIST()
      algorithm
        DAE.LIST(valList = expl) := inExp2;
      then
        expEqualNoCrefSubsList(inExp1.valList, expl);

    case DAE.CONS()
      algorithm
        DAE.CONS(car = e1, cdr = e2) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.car, e1) and expEqualNoCrefSubs(inExp1.cdr, e2);

    case DAE.META_TUPLE()
      algorithm
        DAE.META_TUPLE(listExp = expl) := inExp2;
      then
        expEqualNoCrefSubsList(inExp1.listExp, expl);

    case DAE.META_OPTION()
      algorithm
        DAE.META_OPTION(exp = oe) := inExp2;
      then
        expEqualNoCrefSubsOpt(inExp1.exp, oe);

    case DAE.METARECORDCALL()
      algorithm
        DAE.METARECORDCALL(path = p, args = expl) := inExp2;
      then
        Absyn.pathEqual(inExp1.path, p) and expEqualNoCrefSubsList(inExp1.args, expl);

    case DAE.MATCHEXPRESSION()
      then valueEq(inExp1, inExp2);

    case DAE.BOX()
      algorithm
        DAE.BOX(exp = e) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.exp, e);

    case DAE.UNBOX()
      algorithm
        DAE.UNBOX(exp = e) := inExp2;
      then
        expEqualNoCrefSubs(inExp1.exp, e);

    case DAE.SHARED_LITERAL()
      algorithm
        DAE.SHARED_LITERAL(index = i) := inExp2;
      then
        inExp1.index == i;

    else false;
  end match;
end expEqualNoCrefSubs;


protected function expEqualNoCrefSubsOpt
  input Option<DAE.Exp> inExp1;
  input Option<DAE.Exp> inExp2;
  output Boolean outEqual;
protected
  DAE.Exp e1, e2;
algorithm
  outEqual := match(inExp1, inExp2)
    case (NONE(), NONE()) then true;
    case (SOME(e1), SOME(e2)) then expEqualNoCrefSubs(e1, e2);
    else false;
  end match;
end expEqualNoCrefSubsOpt;

protected function expEqualNoCrefSubsList
  input list<DAE.Exp> inExpl1;
  input list<DAE.Exp> inExpl2;
  output Boolean outEqual;
protected
  DAE.Exp e2;
  list<DAE.Exp> rest_expl2 = inExpl2;
algorithm
  // Check that the lists have the same length, otherwise they can't be equal.
  if listLength(inExpl1) <> listLength(inExpl2) then
    outEqual := false;
    return;
  end if;

  for e1 in inExpl1 loop
    e2 :: rest_expl2 := rest_expl2;

    // Return false if the expressions are not equal.
    if not expEqualNoCrefSubs(e1, e2) then
      outEqual := false;
      return;
    end if;
  end for;

  outEqual := true;
end expEqualNoCrefSubsList;

protected function expEqualNoCrefSubsListList
  input list<list<DAE.Exp>> inExpl1;
  input list<list<DAE.Exp>> inExpl2;
  output Boolean outEqual;
protected
  list<DAE.Exp> expl2;
  list<list<DAE.Exp>> rest_expl2 = inExpl2;
algorithm
  // Check that the lists have the same length, otherwise they can't be equal.
  if listLength(inExpl1) <> listLength(inExpl2) then
    outEqual := false;
    return;
  end if;

  for expl1 in inExpl1 loop
    expl2 :: rest_expl2 := rest_expl2;

    // Return false if the expression lists are not equal.
    if not expEqualNoCrefSubsList(expl1, expl2) then
      outEqual := false;
      return;
    end if;
  end for;

  outEqual := true;
end expEqualNoCrefSubsListList;

protected function getIterationCrefIterator
  input BackendDAE.IterCref cref;
  input list<Integer> iLstIn;
  output list<Integer> iLstOut;
protected
  Integer i;
algorithm
  try
    BackendDAE.ITER_CREF(iterator = DAE.ICONST(i)) := cref;
    iLstOut := i::iLstIn;
  else
    iLstOut := iLstIn;
  end try;
end getIterationCrefIterator;

protected function isIterCref"the iteration cref is a equal to the cref"
  input BackendDAE.IterCref iterCref;
  input DAE.ComponentRef cref;
  output Boolean b;
algorithm
  b := match(iterCref,cref)
    local
      DAE.ComponentRef cref1;
  case(BackendDAE.ITER_CREF(cref=cref1),_)
    then ComponentReference.crefEqualWithoutSubs(cref1,cref);
  case(BackendDAE.ACCUM_ITER_CREF(cref=cref1),_)
    then ComponentReference.crefEqualWithoutSubs(cref1,cref);
  else then false;
  end match;
end isIterCref;

public function isLoopEquation
  input BackendDAE.Equation eqIn;
  output Boolean isLoopEq;
algorithm
  isLoopEq := match(eqIn)
  case(BackendDAE.EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP())))
    then true;
  case(BackendDAE.SOLVED_EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP())))
    then true;
  else
    then false;
  end match;
end isLoopEquation;

public function isAccumLoopEquation
  input BackendDAE.Equation eqIn;
  output Boolean isLoopEq;
algorithm
  isLoopEq := match(eqIn)
  case(BackendDAE.EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs=BackendDAE.ACCUM_ITER_CREF()::_))))
    then true;
  case(BackendDAE.SOLVED_EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(crefs=BackendDAE.ACCUM_ITER_CREF()::_))))
    then true;
  else
    then false;
  end match;
end isAccumLoopEquation;

public function insertSUMexp "exp traversal function for insertSUMexp"
  input DAE.Exp expIn;
  input tuple<DAE.ComponentRef, DAE.Exp> tplIn; //<to be replaced, replace with>
  output DAE.Exp expOut;
  output tuple<DAE.ComponentRef, DAE.Exp> tplOut;
algorithm
  (expOut,tplOut) := matchcontinue(expIn,tplIn)
    local
      DAE.ComponentRef cref0,cref1;
      DAE.Exp repl, exp1, exp2;
      DAE.Operator op;
   case(DAE.BINARY(exp1=exp1, operator=op,exp2=exp2),(cref0,repl))
     equation
       (exp1,_) = insertSUMexp(exp1,tplIn);
       (exp2,_) = insertSUMexp(exp2,tplIn);
     then(DAE.BINARY(exp1,op,exp2),tplIn);
   case(DAE.UNARY(operator=op,exp=exp1),(cref0,repl))
     equation
       (exp1,_) = insertSUMexp(exp1,tplIn);
     then(DAE.UNARY(op,exp1),tplIn);
   case(DAE.CREF(componentRef=cref1),(cref0,repl))
     equation
       true = crefPartlyEqual(cref0,cref1);
     then(repl,tplIn);
   else
     then (expIn,tplIn);
   end matchcontinue;
end insertSUMexp;

public function prepareVectorizedDAE0
  input BackendDAE.EqSystem sysIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem sysOut;
  output BackendDAE.Shared sharedOut;
protected
  array<Integer> ass1, ass2;
  BackendDAE.Variables vars, aliasVars,knownVars;
  list<BackendDAE.Var> varLst, addAlias, aliasLst, knownLst;
  list<BackendDAE.Equation> eqLst;
  BackendDAE.EquationArray eqs;
  Option<BackendDAE.IncidenceMatrix> m;
  Option<BackendDAE.IncidenceMatrixT> mT;
  BackendDAE.Matching matching;
  BackendDAE.StrongComponents compsIn, comps;
  BackendDAE.StateSets stateSets "the statesets of the system";
  BackendDAE.BaseClockPartitionKind partitionKind;
  BackendDAE.Shared shared;
algorithm
  BackendDAE.EQSYSTEM(orderedVars=vars, orderedEqs=eqs, m=m, mT=mT, matching=matching, stateSets=stateSets, partitionKind=partitionKind) := sysIn;
  BackendDAE.SHARED(aliasVars=aliasVars, knownVars=knownVars) := sharedIn;


  eqLst := BackendEquation.equationList(eqs);
    //BackendDump.dumpEquationList(eqLst,"eqsIn");
  //remove partly unrolled for-equations
  // occasionally, there is a constantly indexed var in the for-equation
  (eqLst,_) := updateIterCrefs(eqLst,({},{}));
  // (eqLst,_) := List.fold(eqLst,markUnrolledForEqs,({},{}));

  // set subscripts at end of equation crefs
  eqLst := List.map(listReverse(eqLst),setSubscriptsAtEndForEquation);

  // set subscripts at end of vars
  varLst := BackendVariable.varList(vars);
  aliasLst := BackendVariable.varList(aliasVars);
  knownLst := BackendVariable.varList(knownVars);
  varLst := List.map(varLst,appendSubscriptsInVar);
  aliasLst := List.map(aliasLst,appendSubscriptsInVar);
  knownLst := List.map(knownLst,appendSubscriptsInVar);
  vars := BackendVariable.listVar1(varLst);
  aliasVars := BackendVariable.listVar1(aliasLst);
  knownVars := BackendVariable.listVar1(knownLst);

  eqs := BackendEquation.listEquation(eqLst);
    //BackendDump.dumpEquationList(eqLst,"eqsOut");
    //BackendDump.dumpVariables(vars,"VARSOUT");

  sysOut := BackendDAE.EQSYSTEM(vars, eqs, m, mT, matching, stateSets, partitionKind);
  shared := BackendDAEUtil.setSharedRemovedEqns(sharedIn, BackendEquation.listEquation({}));
  shared := BackendDAEUtil.setSharedAliasVars(shared, aliasVars);
  sharedOut := BackendDAEUtil.setSharedKnVars(shared,knownVars);
end prepareVectorizedDAE0;

protected function setSubscriptsAtEndForEquation
  input BackendDAE.Equation eqIn;
  output BackendDAE.Equation eqOut;
algorithm
  eqOut := matchcontinue(eqIn)
    local
      DAE.Exp lhs,rhs;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
      BackendDAE.LoopInfo loopInfo;
      BackendDAE.Equation eq;
      list<BackendDAE.IterCref> iterCrefs;
      Integer loopId;
      DAE.Exp startIt;
      DAE.Exp endIt;
  case(BackendDAE.EQUATION(exp=lhs, scalar=rhs, source=source, attr = attr as BackendDAE.EQUATION_ATTRIBUTES(loopInfo=
    BackendDAE.LOOP(loopId=loopId,startIt=startIt,endIt=endIt,crefs=iterCrefs))))
    algorithm
      lhs := Expression.traverseExpBottomUp(lhs,appendSubscriptsInExp,"bla");
      rhs := Expression.traverseExpBottomUp(rhs,appendSubscriptsInExp,"bla");
      eq := BackendDAE.EQUATION(lhs,rhs,source,attr);
      iterCrefs := List.map(iterCrefs,setSubscriptAtEndForIterCref);
      loopInfo := BackendDAE.LOOP(loopId,startIt,endIt,iterCrefs);
      eq := setLoopInfoInEq(loopInfo,eq);
    then eq;
  case(BackendDAE.EQUATION(exp=lhs, scalar=rhs, source=source, attr=attr))
    algorithm
      lhs := Expression.traverseExpBottomUp(lhs,appendSubscriptsInExp,"bla");
      rhs := Expression.traverseExpBottomUp(rhs,appendSubscriptsInExp,"bla");
      eq := BackendDAE.EQUATION(lhs,rhs,source,attr);
    then eq;
  end matchcontinue;
end setSubscriptsAtEndForEquation;

protected function setSubscriptAtEndForIterCref
  input BackendDAE.IterCref crefIn;
  output BackendDAE.IterCref crefOut;
algorithm
  crefOut := matchcontinue(crefIn)
    local
      DAE.ComponentRef cr;
      DAE.Exp iterator;
      DAE.Operator op;
      DAE.Subscript sub;
  case(BackendDAE.ITER_CREF(cref=cr, iterator=iterator))
    algorithm
      {sub} := ComponentReference.crefSubs(cr);
      cr := replaceSubscriptAtEnd(sub,cr);
  then (BackendDAE.ITER_CREF(cr,iterator));
  case(BackendDAE.ACCUM_ITER_CREF(cref=cr, op=op))
    algorithm
      {sub} := ComponentReference.crefSubs(cr);
      cr := replaceSubscriptAtEnd(sub,cr);
  then (BackendDAE.ACCUM_ITER_CREF(cr,op));
  else
    then crefIn;
  end matchcontinue;
end setSubscriptAtEndForIterCref;

protected function updateIterCrefs"checks if the iterated crefs still refer to an iterated index"
  input list<BackendDAE.Equation> eqLstIn;
  input tuple<list<BackendDAE.Equation>,list<Integer>> tplIn;  //eqsFoldIn, indxFold
  output tuple<list<BackendDAE.Equation>,list<Integer>> tplOut;
algorithm
  tplOut := matchcontinue(eqLstIn,tplIn)
    local
      Integer id,idx;
      list<Integer> idxsIn, idxs;
      BackendDAE.Equation eq;
      DAE.ComponentRef cref;
      DAE.Exp startIt,endIt;
      list<BackendDAE.Equation> eqLst,eqFold,eqFoldIn,similarEqs,rest;
      list<BackendDAE.IterCref> iterCrefs, iterCrefs1;
      list<DAE.ComponentRef> allCrefs,crefs;
      list<DAE.Subscript> subs;
      BackendDAE.IterCref itCref;
      BackendDAE.LoopInfo loopInfo;
  case({},_)
    then (tplIn);
  case(BackendDAE.EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(loopId=id,startIt=startIt,endIt=endIt,crefs=iterCrefs)))::rest,(eqFoldIn,idxsIn))
    algorithm
      if List.exist1(idxsIn,intEq,id) then
        // the equation will be removed
        idxs := idxsIn;
        id := -1;
        iterCrefs1 := {};
      else
        idxs := id::idxsIn;

        (similarEqs,_) := List.separate1OnTrue(eqLstIn,equationEqualNoCrefSubs,listHead(eqLstIn));
          //BackendDump.dumpEquationList(similarEqs,"simEqs");
        allCrefs := BackendEquation.equationsCrefs(similarEqs);
        iterCrefs1 := {};
        //update iterCrefs
        for itCref in iterCrefs loop
          BackendDAE.ITER_CREF(cref=cref) := itCref;
          crefs := List.filter1OnTrue(allCrefs,crefPartlyEqual,cref);
          subs := List.unique(List.flatten(List.map(crefs,ComponentReference.crefSubs)));
          if intGt(listLength(subs),1) then
            iterCrefs1 := itCref::iterCrefs1;
          end if;
        end for;
      end if;

      loopInfo := BackendDAE.LOOP(id,startIt,endIt,listReverse(iterCrefs1));
      eq := setLoopInfoInEq(loopInfo,listHead(eqLstIn));
      (eqFold,idxs) := updateIterCrefs(rest,(eq::eqFoldIn,idxs));
    then (eqFold,idxs);
  case(eq::rest,(eqFoldIn,idxsIn))
    algorithm
      (eqFold,idxs) := updateIterCrefs(rest,(eq::eqFoldIn,idxsIn));
  then (eqFold,idxs);
  end matchcontinue;
end updateIterCrefs;

public function enlargeIteratedArrayVars
  input BackendDAE.EqSystem sysIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem sysOut;
  output BackendDAE.Shared sharedOut;
protected
  BackendDAE.Variables vars, aliasVars, knownVars;
  list<BackendDAE.Var> varLst, aliasLst, knownLst, knownLst2;
  list<BackendDAE.Equation> eqLst;
  BackendDAE.EquationArray eqs;
  Option<BackendDAE.IncidenceMatrix> m;
  Option<BackendDAE.IncidenceMatrixT> mT;
  BackendDAE.Matching matching;
  BackendDAE.StrongComponents compsIn, comps;
  BackendDAE.StateSets stateSets;
  BackendDAE.BaseClockPartitionKind partitionKind;
algorithm
  BackendDAE.EQSYSTEM(orderedVars=vars, orderedEqs=eqs, m=m, mT=mT, matching=matching, stateSets=stateSets, partitionKind=partitionKind) := sysIn;
  BackendDAE.SHARED(aliasVars=aliasVars, knownVars=knownVars) := sharedIn;

  varLst := BackendVariable.varList(vars);
  aliasLst := BackendVariable.varList(aliasVars);
  knownLst := BackendVariable.varList(knownVars);
    //BackendDump.dumpVarList(varLst,"varLst0");
    //BackendDump.dumpVarList(aliasLst,"aliasVars0");
    //BackendDump.dumpVarList(knownLst,"knownLst0");
    //BackendDump.dumpVarList(aliasLst,"aliasVars0");

  (varLst,aliasLst) := enlargeIteratedArrayVars1(varLst,aliasLst,{},{});
  (knownLst,knownLst2) := enlargeIteratedArrayVars1(knownLst,{},{},{});

    //BackendDump.dumpVarList(varLst,"varLst1");
    //BackendDump.dumpVarList(aliasLst,"aliasVars1");
    //BackendDump.dumpVarList(knownLst,"knownLst1");

  vars := BackendVariable.listVar1(varLst);
  aliasVars := BackendVariable.listVar1(aliasLst);
  sysOut := BackendDAE.EQSYSTEM(vars,eqs,m,mT,matching,stateSets,partitionKind);
  sharedOut := BackendDAEUtil.setSharedAliasVars(sharedIn,aliasVars);
  sharedOut := BackendDAEUtil.setSharedKnVars(sharedOut,BackendVariable.listVar1(knownLst));
end enlargeIteratedArrayVars;


protected function enlargeIteratedArrayVars1
  input list<BackendDAE.Var> varLstIn;
  input list<BackendDAE.Var> aliasLstIn;
  input list<BackendDAE.Var> varLstFoldIn;
  input list<BackendDAE.Var> aliasFoldIn;
  output list<BackendDAE.Var> varLstFoldOut;
  output list<BackendDAE.Var> aliasFoldOut;
algorithm
  (varLstFoldOut,aliasFoldOut) := matchcontinue(varLstIn,aliasLstIn,varLstFoldIn,aliasFoldIn)
    local
      Integer dim;
      BackendDAE.Var var;
      DAE.ComponentRef cref, name;
      DAE.Exp bindExp;
      DAE.Subscript sub;
      list<DAE.ComponentRef> crefLst;
      list<DAE.Subscript> subs;
      list<BackendDAE.Var> varLst, rest, restAlias, simVars, simAlias, varFold, aliasFold;
  case({},{},_,_)
    algorithm
  then (listReverse(varLstFoldIn),listReverse(aliasFoldIn));

  case(BackendDAE.VAR(varName = name, arryDim=({DAE.DIM_INTEGER(integer=dim)}))::rest,_,_,_)
    algorithm
      // expand this simulation var
        //print("check var: "+BackendDump.varString(listHead(varLstIn))+"\n");
      (simVars,rest) := List.separate1OnTrue(varLstIn,isSimilarVarNoBind,listHead(varLstIn));
      (simAlias,restAlias) := List.separate1OnTrue(aliasLstIn,isSimilarVarNoBind,listHead(varLstIn));
          //BackendDump.dumpVarList(simVars,"similarVars");
          //BackendDump.dumpVarList(simAlias,"similarAlias");

      if listLength(simVars)+listLength(simAlias) == dim then
        // everything is correct, set subscripts at end
        varFold := varLstFoldIn;
        for var in simVars loop
          var := appendSubscriptsInVar(var);
          varFold := var::varFold;
        end for;

        aliasFold := aliasFoldIn;
        for var in simAlias loop
          var := appendSubscriptsInVar(var);
          aliasFold := var::aliasFold;
        end for;

          //print("its fine!\n");
      elseif listLength(simVars) == 1 and intLe(listLength(simAlias),dim-1) then
        // add new alias vars, if the array is mixed simulation and alias var, put everything in the simvar part
        cref := BackendVariable.varCref(listHead(simAlias));
        {sub} := ComponentReference.crefSubs(name);
        subs := List.map(List.intRange(dim),Expression.intSubscript);
        subs := List.deleteMember(subs,sub);
        crefLst := List.map1(subs,replaceSubscriptAtEnd,name);
        varLst := List.map1Reverse(crefLst,BackendVariable.copyVarNewName,listHead(simAlias));
        varLst := List.map(varLst,appendSubscriptsInVar);
        // put subscript at end for the var
          var := appendSubscriptsInVar(listHead(varLstIn));
        varFold := var::varLstFoldIn;
        aliasFold := listAppend(varLst,aliasFoldIn);
          //print("add new aliase\n");
      else
        // expand the simVars
        subs := List.map(List.intRange(dim),Expression.intSubscript);
        //crefLst := List.map1r(subs,replaceFirstSubsInCref,name);
        crefLst := List.map1(subs,replaceSubscriptAtEnd,name);
        varLst := List.map1Reverse(crefLst,BackendVariable.copyVarNewName,listHead(varLstIn));
        varLst := List.map(varLst,appendSubscriptsInVar);
        varFold := listAppend(varLst, varLstFoldIn);
        aliasFold := aliasFoldIn;
          //print("increase!\n");
      end if;
      (varFold,aliasFold) := enlargeIteratedArrayVars1(rest,restAlias,varFold,aliasFold);
    then (varFold,aliasFold);

  case({},BackendDAE.VAR(varName = name, arryDim=({DAE.DIM_INTEGER(integer=dim)}), bindExp=SOME(bindExp))::rest,_,_)
    algorithm
      // handle the remaining alias vars
        //print("check alias: "+BackendDump.varString(listHead(aliasLstIn))+"\n");
      (simAlias,restAlias) := List.separate1OnTrue(aliasLstIn,isSimilarVarNoBind,listHead(aliasLstIn));
          //BackendDump.dumpVarList(simAlias,"similarAlias");
      if listLength(simAlias) == dim then
        // everything is correct
        varFold := varLstFoldIn;
        simAlias := List.map(simAlias,appendSubscriptsInVar);
        aliasFold := listAppend(simAlias,aliasFoldIn);
          //print("its fine alias!\n");
      else
        // expand the aliasVars
        subs := List.map(List.intRange(dim),Expression.intSubscript);
        //crefLst := List.map1r(subs,replaceFirstSubsInCref,name);
        crefLst := List.map1(subs,replaceSubscriptAtEnd,name);
        varLst := List.map1Reverse(crefLst,BackendVariable.copyVarNewName,listHead(aliasLstIn));
        varLst := List.map(varLst,appendSubscriptsInVar);
        aliasFold := listAppend(varLst, aliasFoldIn);
        varFold := varLstFoldIn;
          //print("increase alias!\n");
      end if;
      (varFold,aliasFold) := enlargeIteratedArrayVars1({},restAlias,varFold,aliasFold);
    then (varFold,aliasFold);

  case(_::rest,_,_,_)
    algorithm
      // add this non-array var
      //print("add non arry var: "+BackendDump.varString(listHead(varLstIn))+"\n");
      var := appendSubscriptsInVar(listHead(varLstIn));
      (varFold,aliasFold) := enlargeIteratedArrayVars1(rest,aliasLstIn,var::varLstFoldIn,aliasFoldIn);
    then (varFold,aliasFold);

  case({},_::restAlias,_,_)
    algorithm
      // add this non-array alias
       //print("add non array alias var: "+BackendDump.varString(listHead(aliasLstIn))+"\n");
       var := appendSubscriptsInVar(listHead(aliasLstIn));
      (varFold,aliasFold) := enlargeIteratedArrayVars1({},restAlias,varLstFoldIn,var::aliasFoldIn);
    then (varFold,aliasFold);

  end matchcontinue;
end enlargeIteratedArrayVars1;

protected function appendSubscriptsInVar
  input BackendDAE.Var varIn;
  output BackendDAE.Var varOut;
algorithm
  varOut := matchcontinue(varIn)
    local
      DAE.Exp bindExp;
      DAE.ComponentRef name;
      BackendDAE.Var var;
      DAE.Subscript sub;
  case(BackendDAE.VAR(varName=name,bindExp=SOME(bindExp)))
    equation
      if ComponentReference.crefHaveSubs(name) then
        {sub} = ComponentReference.crefSubs(name);
        name = replaceSubscriptAtEnd(sub,name);
      end if;
      bindExp = Expression.traverseExpBottomUp(bindExp,appendSubscriptsInExp,"bla");
      var = BackendVariable.setBindExp(varIn,SOME(bindExp));
      var = BackendVariable.copyVarNewName(name,var);
  then var;
  case(BackendDAE.VAR(varName=name))
    equation
      {sub} = ComponentReference.crefSubs(name);
      name = replaceSubscriptAtEnd(sub,name);
      var = BackendVariable.copyVarNewName(name,varIn);
  then var;
    else
    then varIn;
  end matchcontinue;
end appendSubscriptsInVar;

protected function appendSubscriptsInExp
  input DAE.Exp expIn;
  input String blaIn;
  output DAE.Exp expOut;
  output String blaOut;
algorithm
 (expOut, blaOut) := matchcontinue(expIn,blaIn)
  local
    DAE.ComponentRef cref;
    DAE.Subscript sub;
    DAE.Type ty;
  case(DAE.CREF(componentRef=cref,ty=ty),_)
    equation
      {sub} = ComponentReference.crefSubs(cref);
      cref = replaceSubscriptAtEnd(sub,cref);
     then (DAE.CREF(cref,ty),blaIn);
    else
      then(expIn,blaIn);
  end matchcontinue;
end appendSubscriptsInExp;

protected function replaceSubscriptAtEnd
  input DAE.Subscript sub;
  input DAE.ComponentRef crefIn;
  output DAE.ComponentRef crefOut;
protected
  DAE.ComponentRef cref;
algorithm
  cref := ComponentReference.crefStripSubs(crefIn);
  crefOut := ComponentReference.crefSetLastSubs(cref,{sub});
end replaceSubscriptAtEnd;

public function updateSimCode"updates some things in the simCode"
  input SimCode.SimCode simCodeIn;
  output SimCode.SimCode simCodeOut;
protected
  list<SimCode.SimEqSystem> initialEquations;
  list<SimCodeVar.SimVar> aliasVars;
algorithm
  SimCode.SIMCODE(modelInfo=SimCode.MODELINFO(vars=SimCodeVar.SIMVARS(aliasVars=aliasVars)),initialEquations=initialEquations) := simCodeIn;
  initialEquations := List.map1(initialEquations,updateAliasInSimEqSystem, aliasVars);
  simCodeOut := setSimCodeInitialEquations(simCodeIn,initialEquations);
end updateSimCode;

protected function updateAliasInSimEqSystem
  input SimCode.SimEqSystem eqIn;
  input list<SimCodeVar.SimVar> aliasVars;
  output SimCode.SimEqSystem eqOut;
algorithm
  eqOut := matchcontinue(eqIn,aliasVars)
    local
      Integer idx;
      DAE.ComponentRef cref;
      DAE.Exp exp;
      DAE.ElementSource source;
  case(SimCode.SES_SIMPLE_ASSIGN(index=idx,cref=cref,exp=exp,source=source),_)
    equation
      (exp,_) = Expression.traverseExpBottomUp(exp,updateAliasInSimEqSystem1,aliasVars);
    then SimCode.SES_SIMPLE_ASSIGN(idx,cref,exp,source);
  else
    then eqIn;
  end matchcontinue;
end updateAliasInSimEqSystem;

protected function updateAliasInSimEqSystem1"replaces crefs with its alias"
  input DAE.Exp expIn;
  input list<SimCodeVar.SimVar> aliasVarsIn;
  output DAE.Exp expOut;
  output list<SimCodeVar.SimVar> aliasVarsOut;
algorithm
  (expOut,aliasVarsOut) := matchcontinue(expIn,aliasVarsIn)
    local
      Boolean isNegated;
      DAE.ComponentRef cref;
      DAE.Exp exp;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref,ty=ty),_)
    equation
      (cref,isNegated) = getSimCodeVarAlias(aliasVarsIn,cref);
      if isNegated then
        exp = DAE.UNARY(DAE.UMINUS(ty),DAE.CREF(cref,ty));
      else
        exp = DAE.CREF(cref,ty);
      end if;
  then (exp,aliasVarsIn);
  else
    then(expIn,aliasVarsIn);
  end matchcontinue;
end updateAliasInSimEqSystem1;

protected function getSimCodeVarAlias
  input list<SimCodeVar.SimVar> simVar;
  input DAE.ComponentRef crefIn;
  output DAE.ComponentRef crefOut;
  output Boolean isNegated;
algorithm
  (crefOut,isNegated) := matchcontinue(simVar,crefIn)
    local
      DAE.ComponentRef name, varName;
      list<SimCodeVar.SimVar> rest;
  case({},_)
    then (crefIn,false);
  case(SimCodeVar.SIMVAR(name=name,aliasvar=SimCodeVar.ALIAS(varName=varName))::_,_)
    equation
      true = ComponentReference.crefEqual(crefIn,name);
  then (varName,false);
  case(SimCodeVar.SIMVAR(name=name,aliasvar=SimCodeVar.NEGATEDALIAS(varName=varName))::_,_)
    equation
      true = ComponentReference.crefEqual(crefIn,name);
  then (varName,true);
  case(_::rest,_)
    then getSimCodeVarAlias(rest,crefIn);
  end matchcontinue;
end getSimCodeVarAlias;

protected function setSimCodeInitialEquations
  input SimCode.SimCode simCode;
  input list<SimCode.SimEqSystem> initEqs;
  output SimCode.SimCode outSimCode;
algorithm
  outSimCode := match (simCode, initEqs)
    local
      SimCode.ModelInfo modelInfo;
      list<DAE.Exp> literals;
      list<SimCode.RecordDeclaration> recordDecls;
      list<String> externalFunctionIncludes;
      list<SimCode.SimEqSystem> allEquations;
      list<list<SimCode.SimEqSystem>> odeEquations;
      list<list<SimCode.SimEqSystem>> algebraicEquations;
      Boolean useHomotopy;
      list<SimCode.SimEqSystem> initialEquations, removedInitialEquations;
      list<SimCode.SimEqSystem> startValueEquations;
      list<SimCode.SimEqSystem> nominalValueEquations;
      list<SimCode.SimEqSystem> minValueEquations;
      list<SimCode.SimEqSystem> maxValueEquations;
      list<SimCode.SimEqSystem> parameterEquations;
      list<SimCode.SimEqSystem> removedEquations;
      list<SimCode.SimEqSystem> algorithmAndEquationAsserts;
      list<SimCode.SimEqSystem> jacobianEquations;
      list<SimCode.SimEqSystem> equationsForZeroCrossings;
      list<SimCode.StateSet> stateSets;
      list<DAE.Constraint> constraints;
      list<DAE.ClassAttributes> classAttributes;
      list<BackendDAE.ZeroCrossing> zeroCrossings, relations;
      list<BackendDAE.TimeEvent> timeEvents;
      list<SimCode.SimWhenClause> whenClauses;
      list<DAE.ComponentRef> discreteModelVars;
      SimCode.ExtObjInfo extObjInfo;
      SimCode.MakefileParams makefileParams;
      SimCode.DelayedExpression delayedExps;
      list<SimCode.JacobianMatrix> jacobianMatrixes;
      Option<SimCode.SimulationSettings> simulationSettingsOpt;
      String fileNamePrefix;
      // *** a protected section *** not exported to SimCodeTV
      SimCode.HashTableCrefToSimVar crefToSimVarHT "hidden from typeview - used by cref2simvar() for cref -> SIMVAR lookup available in templates.";
      HpcOmSimCode.HpcOmData hpcomData;
      HashTableCrIListArray.HashTable varToArrayIndexMapping;
      HashTableCrILst.HashTable varToIndexMapping;
      Option<SimCode.FmiModelStructure> modelStruct;
      Option<SimCode.BackendMapping> backendMapping;
      list<BackendDAE.BaseClockPartitionKind> partitionsKind;
      list<DAE.ClockKind> baseClocks;

    case (SimCode.SIMCODE( modelInfo, literals, recordDecls, externalFunctionIncludes,
                           allEquations, odeEquations, algebraicEquations, partitionsKind, baseClocks,
                           useHomotopy, initialEquations, removedInitialEquations, startValueEquations,
                           nominalValueEquations, minValueEquations, maxValueEquations,
                           parameterEquations, removedEquations, algorithmAndEquationAsserts, equationsForZeroCrossings,
                           jacobianEquations, stateSets, constraints, classAttributes, zeroCrossings,
                           relations, timeEvents, whenClauses, discreteModelVars, extObjInfo, makefileParams,
                           delayedExps, jacobianMatrixes, simulationSettingsOpt, fileNamePrefix, hpcomData, varToArrayIndexMapping,
                           varToIndexMapping, crefToSimVarHT, backendMapping, modelStruct ), _)
      then SimCode.SIMCODE( modelInfo, literals, recordDecls, externalFunctionIncludes,
                            allEquations, odeEquations, algebraicEquations, partitionsKind, baseClocks,
                            useHomotopy, initEqs, removedInitialEquations, startValueEquations,
                            nominalValueEquations, minValueEquations, maxValueEquations,
                            parameterEquations, removedEquations, algorithmAndEquationAsserts,equationsForZeroCrossings,
                            jacobianEquations, stateSets, constraints, classAttributes, zeroCrossings,
                            relations, timeEvents, whenClauses, discreteModelVars, extObjInfo, makefileParams,
                            delayedExps, jacobianMatrixes, simulationSettingsOpt, fileNamePrefix, hpcomData,
                            varToArrayIndexMapping, varToIndexMapping, crefToSimVarHT, backendMapping, modelStruct );
  end match;
end setSimCodeInitialEquations;

/*
public function prepareVectorizedDAE1
  input BackendDAE.EqSystem sysIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem sysOut;
  output BackendDAE.Shared sharedOut;
protected
  BackendDAE.Variables vars, aliasVars;
  list<BackendDAE.Var> varLst, addAlias, addAliasLst1, aliasVars0;
  list<BackendDAE.Equation> eqLst;
  BackendDAE.EquationArray eqs;
  Option<BackendDAE.IncidenceMatrix> m;
  Option<BackendDAE.IncidenceMatrixT> mT;
  BackendDAE.Matching matching;
  BackendDAE.StateSets stateSets "the statesets of the system";
  BackendDAE.BaseClockPartitionKind partitionKind;
algorithm
  BackendDAE.EQSYSTEM(orderedVars=vars, orderedEqs=eqs, m=m, mT=mT, matching=matching, stateSets=stateSets, partitionKind=partitionKind) := sysIn;
  BackendDAE.SHARED(aliasVars=aliasVars) := sharedIn;

  //unroll variables
  varLst := BackendVariable.varList(vars);
  aliasVars0 := BackendVariable.varList(aliasVars);
    BackendDump.dumpVarList(varLst,"varLst1");
    BackendDump.dumpVarList(aliasVars0,"alias1");
  (varLst,addAlias) := List.fold1(varLst,rollOutArrays,aliasVars0,({},{}));
    BackendDump.dumpVarList(varLst,"the unrolled vars");
    BackendDump.dumpVarList(addAlias,"teh additional alias");
  aliasVars := BackendVariable.mergeVariables(aliasVars,BackendVariable.listVar1(addAlias));
    //BackendDump.dumpVariables(aliasVars,"final alias");
  vars := BackendVariable.listVar(varLst);
  // add missing aliase
  //there are still alias vars that need to be expanded
  addAliasLst1 := expandAliasVars(aliasVars0,vars,{});

  sysOut := BackendDAE.EQSYSTEM(vars,eqs,m,mT,matching,stateSets,partitionKind);
  sharedOut := BackendDAEUtil.setSharedAliasVars(sharedIn,aliasVars);
end prepareVectorizedDAE1;

protected function expandAliasVars
  input list<BackendDAE.Var> varsIn;
  input BackendDAE.Variables algVars;
  input list<BackendDAE.Var> foldIn;
  output list<BackendDAE.Var> foldOut;
algorithm
  foldOut := matchcontinue(varsIn,algVars,foldIn)
    local
      Integer dim;
      list<BackendDAE.Var> rest, similarVars,rest;
  case({},_,_)
    equation
  then foldIn;
  case(BackendDAE.VAR(arryDim=({DAE.DIM_INTEGER(integer=dim)}))::rest,_,_)
    equation
      (similarVars,rest) = List.separate1OnTrue(varsIn,isSimilarVar,listHead(varsIn));
      //there are less vars than dimensions
      true = intLt(listLength(similarVars),dim);
      BackendDump.dumpVarList(similarVars,"simVars");
  then expandAliasVars(rest,algVars,foldIn);
  case(_::rest,_,_)
    then expandAliasVars(rest,algVars,foldIn);
  end matchcontinue;
end expandAliasVars;



protected function markUnrolledForEqs"checks the loop ids for every for-equation. the loop ids have to be unique."
  input BackendDAE.Equation eqIn;
  input tuple<list<BackendDAE.Equation>,list<Integer>> tplIn; //foldEqs, loopIds
  output tuple<list<BackendDAE.Equation>,list<Integer>> tplOut;
algorithm
  tplOut := matchcontinue(eqIn,tplIn)
    local
      Integer id;
      list<Integer> ids0, ids;
      list<BackendDAE.Equation> eqLst0, eqLst;
    case(BackendDAE.EQUATION(attr=BackendDAE.EQUATION_ATTRIBUTES(loopInfo=BackendDAE.LOOP(loopId=id))),(eqLst0,ids0))
      equation
        if List.exist1(ids0,intEq,id) then
          ids = ids0;
          eqLst = setLoopId(eqIn,-1)::eqLst0;
        else
          ids = id::ids0;
          eqLst = eqIn::eqLst0;
        end if;
    then (eqLst,ids);
    case(_,(eqLst0,ids0))
      then (eqIn::eqLst0,ids0);
  end matchcontinue;
end markUnrolledForEqs;


protected function setLoopId
  input BackendDAE.Equation eqIn;
  input Integer id;
  output BackendDAE.Equation eqOut;
protected
  DAE.Exp exp,scalar,startIt,endIt;
  list<BackendDAE.IterCref> iterCrefs;
  DAE.ElementSource source;
  BackendDAE.EquationAttributes attr;
  Boolean differentiated;
  BackendDAE.EquationKind kind;
  BackendDAE.LoopInfo loopInfo;
algorithm
  try
    BackendDAE.EQUATION(exp=exp,scalar=scalar,source=source,attr=BackendDAE.EQUATION_ATTRIBUTES(differentiated=differentiated,kind=kind,loopInfo=BackendDAE.LOOP(startIt=startIt,endIt=endIt,crefs=iterCrefs))) := eqIn;
    eqOut := BackendDAE.EQUATION(exp,scalar,source,BackendDAE.EQUATION_ATTRIBUTES(differentiated,kind,BackendDAE.LOOP(id,startIt,endIt,iterCrefs)));
  else
    eqOut := eqIn;
  end try;
end setLoopId;

protected function rollOutArrays"expands the array vars. dispatch the unrolled vars to the algebraic and to the alias vars."
  input BackendDAE.Var inVar;
  input list<BackendDAE.Var> aliasVars;
  input tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> foldIn;
  output tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> foldOut;
algorithm
  foldOut := matchcontinue(inVar, foldIn)
    local
      Integer i,dim;
      DAE.ComponentRef cref;
      DAE.Subscript sub;
      BackendDAE.Var var;
      list<BackendDAE.Var> varLst0, aliasLst0, varLst, aliasLst, equalCrefLst, otherArrayVarLst, addAliasLst, addAliasLst1;
      list<DAE.ComponentRef> crefLst;
      list<DAE.Subscript> subs;
  case(BackendDAE.VAR(varName=cref, arryDim={DAE.DIM_INTEGER(integer=dim)}),(varLst0,aliasLst0))
   algorithm
     // its an array var with one subscript
       //print("analyse Var "+BackendDump.varString(inVar)+"\n");
     if List.exist1(varLst0,BackendVariable.varEqual,inVar) then
       // this var is already in the list, add nothing
       varLst := {};
       addAliasLst := {};
     else
       // add all rolled out vars, and aliase for the rolled outs
      {DAE.INDEX(DAE.ICONST(integer = i))} := ComponentReference.crefSubs(cref);
      (aliasLst, _) := List.separate1OnTrue(aliasVars,isAliasVarOf,inVar);
        //BackendDump.dumpVarList(aliasLst,"all aliase");
        //BackendDump.dumpVarList(varLst,"no aliase");
      (equalCrefLst, otherArrayVarLst) := List.fold1(aliasLst,dispatchAliasVars,inVar,({},{}));
        //BackendDump.dumpVarList(equalCrefLst,"aliase with equal crefs");
        //BackendDump.dumpVarList(otherArrayVarLst,"other aliase");
      addAliasLst := {};
      if listEmpty(equalCrefLst) then
        // there are no aliase equations for the iterated crefs, therefore we need algebraic vars for them
        subs := List.map(List.intRange(dim),Expression.intSubscript);
        crefLst := List.map1r(subs,replaceFirstSubsInCref,cref);
        varLst := List.map1(crefLst,BackendVariable.copyVarNewName,inVar);
      else
        // there are alias variables for the iterated crefs
        for var in equalCrefLst loop
          addAliasLst := listAppend(additionalAlias(var),addAliasLst);
        end for;
        varLst := {inVar};
      end if;
    end if;
       //BackendDump.dumpVarList(addAliasLst,"addAliasLst");
       //BackendDump.dumpVarList(varLst,"varLst");
   then (listAppend(varLst,varLst0),listAppend(addAliasLst,aliasLst0));
  case(_,(varLst0,aliasLst0))
    then (inVar::varLst0,aliasLst0);
  end matchcontinue;
end rollOutArrays;
*/


protected function isSimilarVar
  input BackendDAE.Var var1;
  input BackendDAE.Var var2;
  output Boolean bOut;
algorithm
  bOut := matchcontinue(var1,var2)
    local
      Boolean b;
      DAE.ComponentRef cref1, cref2;
      DAE.Exp bindExp1, bindExp2;
  case(BackendDAE.VAR(varName=cref1, bindExp=SOME(bindExp1)),BackendDAE.VAR(varName=cref2, bindExp=SOME(bindExp2)))
    equation
      then crefPartlyEqual(cref1,cref2) and expEqualNoCrefSubs(bindExp1,bindExp2);
  else
    then false;
  end matchcontinue;
end isSimilarVar;

protected function isSimilarVarNoBind
  input BackendDAE.Var var1;
  input BackendDAE.Var var2;
  output Boolean bOut;
algorithm
  bOut := matchcontinue(var1,var2)
    local
      Boolean b;
      DAE.ComponentRef cref1, cref2;
  case(BackendDAE.VAR(varName=cref1),BackendDAE.VAR(varName=cref2))
    equation
      then crefPartlyEqual(cref1,cref2);
  else
    then false;
  end matchcontinue;
end isSimilarVarNoBind;

protected function additionalAlias"adds additional alias vars"
  input BackendDAE.Var var;
  output list<BackendDAE.Var> varLstOut;
algorithm
  varLstOut := matchcontinue(var)
    local
      Integer i, dim;
      DAE.Exp bindExp;
      DAE.ComponentRef cref;
      list<DAE.ComponentRef> crefLst;
      list<BackendDAE.Var> varLst;
   case(BackendDAE.VAR(bindExp = SOME(bindExp), arryDim={DAE.DIM_INTEGER(integer=dim)}))
     algorithm
       {cref} := Expression.extractCrefsFromExp(bindExp);
       crefLst := {};
       for i in List.intRange(dim) loop
         crefLst := replaceFirstSubsInCref(cref,{DAE.INDEX(DAE.ICONST(i))})::crefLst;
       end for;
       (crefLst,_) := List.deleteMemberOnTrue(cref,crefLst,ComponentReference.crefEqual);
       varLst := List.map1(crefLst,BackendVariable.copyVarNewName,var);
   then varLst;
   else
     then {};
  end matchcontinue;
end additionalAlias;

protected function dispatchAliasVars"dispatches the aliasvars in a list of alias that have the same cref except the subscript and aliasvars that are array vars with other crefs.
non array vars are dismissed"
  input BackendDAE.Var aliasVar;
  input BackendDAE.Var refVar;
  input tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> tplIn;
  output tuple<list<BackendDAE.Var>,list<BackendDAE.Var>> tplOut;
algorithm
  tplOut := matchcontinue(aliasVar,refVar,tplIn)
    local
      Integer dim;
      list<BackendDAE.Var> equalCrefLst, otherArrayVarLst;
      DAE.ComponentRef cref1, cref2;
  case(BackendDAE.VAR(varName = cref1, arryDim={DAE.DIM_INTEGER(integer=dim)}),BackendDAE.VAR(varName = cref2),(equalCrefLst, otherArrayVarLst))
    equation
      true = crefPartlyEqual(cref1,cref2);
      then (aliasVar::equalCrefLst, otherArrayVarLst);
  case(BackendDAE.VAR(varName = cref1, arryDim={DAE.DIM_INTEGER(integer=dim)}),BackendDAE.VAR(varName = cref2),(equalCrefLst, otherArrayVarLst))
    equation
      false = crefPartlyEqual(cref1,cref2);
      then (equalCrefLst, aliasVar::otherArrayVarLst);
  else
  equation
    then tplIn;
  end matchcontinue;
end dispatchAliasVars;

protected function isAliasVarOf"checks if the var is the aliasVar of varWithAlias"
  input BackendDAE.Var varWithAlias;
  input BackendDAE.Var var;
  output Boolean b;
algorithm
  b := matchcontinue(varWithAlias,var)
    local
      DAE.ComponentRef cref0, cref1;
      DAE.Exp bindExp;
  case(BackendDAE.VAR(bindExp=SOME(bindExp)),BackendDAE.VAR(varName=cref0))
    equation
      {cref1} = Expression.extractCrefsFromExp(bindExp);
    then ComponentReference.crefEqual(cref0,cref1);
  else
  then false;
  end matchcontinue;
end isAliasVarOf;

//-----------------------------------------------
// Scalarize the equation system
//-----------------------------------------------

public function scalarizeBackendDAE"scalarized everythin in the backenddae"
  input BackendDAE.BackendDAE daeIn;
  output BackendDAE.BackendDAE daeOut;
algorithm
  daeOut := BackendDAEUtil.mapEqSystem(daeIn,scalarizeEqSystem);
end scalarizeBackendDAE;

public function scalarizeEqSystem
  input BackendDAE.EqSystem systIn;
  input BackendDAE.Shared sharedIn;
  output BackendDAE.EqSystem systOut;
  output BackendDAE.Shared sharedOut;
protected
  BackendDAE.Variables vars, alias, knVars;
  BackendDAE.EquationArray eqs;
  BackendDAE.StateSets stateSets;
  BackendDAE.BaseClockPartitionKind partitionKind;
  list<BackendDAE.Var> varLst, aliasLst, knLst;
  list<BackendDAE.Equation> eqLst;
algorithm
  BackendDAE.EQSYSTEM(orderedVars=vars,orderedEqs=eqs,stateSets=stateSets,partitionKind=partitionKind) := systIn;
  BackendDAE.SHARED(aliasVars=alias, knownVars=knVars) := sharedIn;

  //scalarize variables
  varLst := BackendVariable.traverseBackendDAEVars(vars,scalarizeVar,{});
  aliasLst := BackendVariable.traverseBackendDAEVars(alias,scalarizeVar,{});
  knLst := BackendVariable.traverseBackendDAEVars(knVars,scalarizeVar,{});

  //scalarize equations
  eqLst := BackendEquation.traverseEquationArray(eqs,scalarizeEquation,{});

  systOut := BackendDAE.EQSYSTEM(BackendVariable.listVar(varLst),BackendEquation.listEquation(eqLst),NONE(),NONE(),BackendDAE.NO_MATCHING(),stateSets,partitionKind);
  sharedOut := BackendDAEUtil.setSharedAliasVars(sharedIn, BackendVariable.listVar(aliasLst));
  sharedOut := BackendDAEUtil.setSharedKnVars(sharedOut, BackendVariable.listVar(knLst));
end scalarizeEqSystem;

protected function scalarizeVar"scalarizes unexpanded array-variables"
  input BackendDAE.Var varIn;
  input list<BackendDAE.Var> varsFoldIn;
  output BackendDAE.Var varOut;
  output list<BackendDAE.Var> varsFoldOut;
algorithm
  (varOut,varsFoldOut) := matchcontinue(varIn,varsFoldIn)
    local
      Integer start,stop;
      DAE.ComponentRef cref;
      DAE.Exp bindExp;
      Option<DAE.Exp> bindExpOpt;
      DAE.Subscript sub;
      BackendDAE.Var var;
      list<BackendDAE.Var> varLst={};
    case(BackendDAE.VAR(varName=cref, bindExp=bindExpOpt),_)
      algorithm
        {sub} := ComponentReference.crefSubs(cref);
        DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start),stop=DAE.ICONST(stop))) := sub;
        for i in List.intRange2(start,stop) loop
          cref := replaceFirstSubsInCref(cref,{DAE.INDEX(DAE.ICONST(i))});
          if Util.isSome(bindExpOpt) then
            bindExp := Util.getOption(bindExpOpt);
            bindExp := ExpressionSimplify.simplify(bindExp);
            bindExp := BackendArrayVarTransform.replaceSubExp(bindExp,DAE.INDEX(DAE.ICONST(i)));
            var := BackendVariable.setBindExp(varIn,SOME(bindExp));
          else
            var := varIn;
          end if;
          var := BackendVariable.copyVarNewName(cref,var);
          varLst := var::varLst;
        end for;
     then (varIn,listAppend(varLst,varsFoldIn));
   else
     then (varIn,varIn::varsFoldIn);
  end matchcontinue;
end scalarizeVar;


protected function scalarizeEquation"scalarizes for equations and rolls out sum-expressions"
  input BackendDAE.Equation eqIn;
  input list<BackendDAE.Equation> eqsFoldIn;
  output BackendDAE.Equation eqOut;
  output list<BackendDAE.Equation> eqsFoldOut;
algorithm
  (eqOut,eqsFoldOut) := matchcontinue(eqIn,eqsFoldIn)
    local
      Integer start,stop,i;
      DAE.ElementSource source;
      DAE.Exp iter, left, right, left1, right1;
      DAE.Subscript sub;
      BackendDAE.Equation eq;
      BackendDAE.EquationAttributes attr;
      list<BackendDAE.Equation> eqLst={};
    case(BackendDAE.FOR_EQUATION(iter=iter,start=DAE.ICONST(start), stop=DAE.ICONST(stop), left=left, right=right, source=source, attr=attr),_)
      algorithm
        for i in List.intRange2(start,stop) loop
          (left1,_) := Expression.traverseExpBottomUp(left,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iter,DAE.ICONST(i)));
          (right1,_) := Expression.traverseExpBottomUp(right,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iter,DAE.ICONST(i)));
          eq := BackendDAE.EQUATION(left1,right1,source,attr);
          eqLst := eq::eqLst;
        end for;
     then (eqIn,listAppend(eqLst,eqsFoldIn));
   else
     algorithm
     (eq,_) := BackendEquation.traverseExpsOfEquation(eqIn,scalarizeExp,"dummy");
     then (eqIn,eq::eqsFoldIn);
  end matchcontinue;
end scalarizeEquation;


protected function scalarizeExp"rolls out sum-expressions"
  input DAE.Exp eIn;
  input String argIn;
  output DAE.Exp eOut;
  output String argOut;
algorithm
  (eOut,argOut) := matchcontinue(eIn,argIn)
    local
      Integer start,stop,i;
      DAE.ElementSource source;
      DAE.Exp iter, left,right, body, summand, summation;
      DAE.Operator op;
      DAE.Subscript sub;
      DAE.Type ty;
    case(DAE.SUM(iterator=iter,startIt=DAE.ICONST(start), endIt=DAE.ICONST(stop), body=body),_)
      algorithm
        ty := Expression.typeof(body);
        summation := Expression.createZeroExpression(ty);
        for i in List.intRange2(start,stop) loop
          (summand,_) := Expression.traverseExpBottomUp(body,BackendArrayVarTransform.replaceIteratorWithRangeInCrefInExp,(iter,DAE.ICONST(i)));
          summation := DAE.BINARY(summation,DAE.ADD(ty),summand);
        end for;

     then (summation,argIn);

    case(DAE.BINARY(exp1=left,operator=op,exp2=right),_)
      algorithm
        (left,_) := scalarizeExp(left,argIn);
        (right,_) := scalarizeExp(right,argIn);
      then (DAE.BINARY(left,op,right),argIn);

    case(DAE.UNARY(operator=op,exp=right),_)
      algorithm
        (right,_) := scalarizeExp(right,argIn);
      then (DAE.UNARY(operator=op,exp=right),argIn);

   else
     algorithm
     then (eIn,argIn);
  end matchcontinue;
end scalarizeExp;

//-----------------------------------------------
// solveExpressions
//-----------------------------------------------

public function solveForEquationForArrayVar"solves a for equation for a ranged var."
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.Exp iter;
  input DAE.Exp forRange;
  input DAE.Exp solveFor;
  input Integer iuniqueEqIndex;
  output DAE.Exp rhsOut;
  output DAE.ComponentRef lhsOut;
protected
  Boolean isDer;
  Integer start1,start2;
  DAE.ComponentRef cref;
  DAE.Exp sub, offset, crefExp;
algorithm
  isDer := Expression.isDerCall(solveFor);
  if isDer then
    cref := Expression.expCref(Expression.getDerExp(solveFor));
  else
    cref := Expression.expCref(solveFor);
  end if;
  {DAE.INDEX(sub)} := ComponentReference.crefSubs(cref);
  DAE.RANGE(start=DAE.ICONST(start1)) := forRange;
  DAE.RANGE(start=DAE.ICONST(start2)) := sub;
  offset := DAE.ICONST(start2-start1);
  sub := ExpressionSimplify.simplify(DAE.BINARY(iter,DAE.ADD(DAE.T_INTEGER_DEFAULT),offset));
  cref := replaceFirstSubsInCref(cref,{DAE.INDEX(sub)});
  if isDer then
    crefExp := Expression.expDer(Expression.crefExp(cref));
    lhsOut := replaceRangeWithSliceInCref(ComponentReference.crefPrefixDer(cref));
  else
    crefExp := Expression.crefExp(cref);
    lhsOut := replaceRangeWithSliceInCref(cref);
  end if;
      //print("SOLVE_EQ: "+ExpressionDump.printExpStr(lhs)+" = "+ExpressionDump.printExpStr(rhs)+" ---> "+ExpressionDump.printExpStr(crefExp)+"\n");
  (rhsOut,_) := ExpressionSolve.solve(lhs, rhs, crefExp);
    //print("rhsOut: "+ExpressionDump.printExpStr(rhsOut)+"\n");
end solveForEquationForArrayVar;

protected function replaceRangeWithSliceInExp
  input DAE.Exp eIn;
  output DAE.Exp eOut;
algorithm
  eOut := matchcontinue(eIn)
    local
      DAE.Type ty;
      DAE.ComponentRef cref;
  case(DAE.CREF(ty=ty, componentRef=cref))
    equation
      cref = replaceRangeWithSliceInCref(cref);
    then DAE.CREF(cref, ty);
  else
    then eIn;
  end matchcontinue;
end replaceRangeWithSliceInExp;

protected function replaceRangeWithSliceInCref
  input DAE.ComponentRef crefIn;
  output DAE.ComponentRef crefOut;
algorithm
  crefOut := matchcontinue(crefIn)
    local
      DAE.Type ty;
      DAE.Exp start, stop, range;
  case(_)
    equation
      {DAE.INDEX(range)} = ComponentReference.crefSubs(crefIn);
      crefOut = replaceSubscriptAtEnd(DAE.SLICE(range),crefIn);
    then crefIn;
  else
    then crefIn;
  end matchcontinue;
end replaceRangeWithSliceInCref;

annotation(__OpenModelica_Interface="backend");
end Vectorization;
