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

encapsulated package BackendArrayVarTransform
" file:        BackendArrayVarTransform.mo
  package:     BackendArrayVarTransform
  description: BackendArrayVarTransform contains a Binary Tree representation of variable replacements.

  RCS: $Id: BackendVarTransform.mo 25836 2015-04-30 07:08:15Z vwaurich $

  This module contain a Binary tree representation of variable replacements
  along with some functions for performing replacements of variables in equations"

public import BackendDAE;
public import DAE;
public import HashTable2;
public import HashTable3;

protected import Absyn;
protected import BaseHashTable;
protected import BaseHashSet;
protected import BackendDAEUtil;
protected import BackendEquation;
protected import BackendVariable;
protected import ClassInf;
protected import ComponentReference;
protected import DAEUtil;
protected import Debug;
protected import Expression;
protected import ExpressionDump;
protected import ExpressionSimplify;
protected import Flags;
protected import HashSet;
protected import List;
protected import Util;
protected import Vectorization;

public uniontype ArrayVarRepl
"VariableReplacements consists of a mapping between variables and expressions, the first binary tree of this type.
 To eliminate a variable from an equation system a replacement rule varname->expression is added to this
 datatype.
 To be able to update these replacement rules incrementally a backward lookup mechanism is also required.
 For instance, having a rule a->b and adding a rule b->c requires to find the first rule a->b and update it to
 a->c. This is what the second binary tree is used for."
  record REPLACEMENTS
    HashTable2.HashTable nonArrayHT "cref --> exp";
    HashTable.HashTable arrayHT "cref --> idx, idx is used to find concrete arrayCrefs";
    HashTable3.HashTable invHashTable "cref-->crefs, to loop backwars";
    array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps "for each arraycref, a list of corresponding subscripts and their replaced expressions";
    Integer nextFreeIdx;
  end REPLACEMENTS;
end ArrayVarRepl;


//-------------
//BASIC FUNCTIONS
//-------------

public function emptyReplacementsSized "
  Returns an empty set of replacement rules
"
  input Integer size;
  input Integer arrSize;
  output ArrayVarRepl outRepl;
algorithm
  outRepl:=  match (size,arrSize)
    local
      array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps;
      HashTable2.HashTable nonArrayHT;
      HashTable.HashTable arrayHT;
      HashTable3.HashTable invHashTable;
    case (_,_)
      equation
        arrayHT = HashTable.emptyHashTableSized(size);
        nonArrayHT = HashTable2.emptyHashTableSized(size);
        invHashTable = HashTable3.emptyHashTableSized(size);
        arrayExps  = arrayCreate(arrSize,{});
      then
        REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,1);
  end match;
end emptyReplacementsSized;


public function addArrReplacement "adds a replacement for an array cref and saves the replacements for the scalars in a compact way"
  input ArrayVarRepl inRepl;
  input DAE.ComponentRef inSrc;
  input DAE.Exp inDst;
  input Option<DAE.Subscript> subInOpt; // the range
  output ArrayVarRepl outRepl;
algorithm
  outRepl:=
  matchcontinue (inRepl,inSrc,inDst,subInOpt)
    local
      Integer idx;
      ArrayVarRepl repl;
      DAE.ComponentRef src, dst, alias;
      DAE.Exp bind;
      DAE.Subscript subIn,sub;
      HashTable.HashTable arrayHT;
      HashTable2.HashTable nonArrayHT;
      HashTable3.HashTable invHashTable;
      list<DAE.ComponentRef> srcLst, aliasCrefs;
      list<DAE.Exp> aliasBinds;
      list<tuple<DAE.Subscript,DAE.Exp>> crefEntries;
      array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps;

    case (REPLACEMENTS(nonArrayHT=nonArrayHT, arrayHT=arrayHT, invHashTable=invHashTable, arrayExps=arrayExps, nextFreeIdx=idx),_,_,SOME(subIn))
      equation
        // an array cref with a certain slice
        true = ComponentReference.crefHaveSubs(inSrc);
        src = ComponentReference.crefStripSubs(inSrc);
        print("source: "+ComponentReference.printComponentRefStr(src)+"\n");

        //set replacement rules
        if BaseHashTable.hasKey(src,arrayHT) then
          crefEntries = arrayGet(arrayExps,BaseHashTable.get(src,arrayHT));
          crefEntries = insertSubInCrefEntries((subIn,inDst),crefEntries,{});
          arrayUpdate(arrayExps,BaseHashTable.get(src,arrayHT),crefEntries);
        else
          arrayHT = BaseHashTable.add((src, idx),arrayHT);
          crefEntries = {(subIn,inDst)};
          arrayUpdate(arrayExps,idx,crefEntries);
          idx = idx+1;
        end if;

        //update the other alias vars of this one
        //repl = updateAlias(inSrc,REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,idx));
        repl = REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,idx);
      then repl;

    case (REPLACEMENTS(nonArrayHT=nonArrayHT, arrayHT=arrayHT, invHashTable=invHashTable, arrayExps=arrayExps, nextFreeIdx=idx),_,_,NONE())
      algorithm
        // an array cref without! a certain slice
        true := ComponentReference.crefHaveSubs(inSrc);
        src := ComponentReference.crefStripSubs(inSrc);
        {subIn} := ComponentReference.crefSubs(inSrc);
        print("source: "+ComponentReference.printComponentRefStr(src)+"\n");

        //set replacement rules
        if BaseHashTable.hasKey(src,arrayHT) then
          crefEntries := arrayGet(arrayExps,BaseHashTable.get(src,arrayHT));
          crefEntries := insertSubInCrefEntries((subIn,inDst),crefEntries,{});
          arrayUpdate(arrayExps,BaseHashTable.get(src,arrayHT),crefEntries);
        else
          arrayHT := BaseHashTable.add((src, idx),arrayHT);
          crefEntries := {(subIn,inDst)};
          arrayUpdate(arrayExps,idx,crefEntries);
          idx := idx+1;
        end if;

        //update the other alias vars of this one
        repl := updateAlias(inSrc,REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,idx));
      then repl;

    case (REPLACEMENTS(nonArrayHT=nonArrayHT, arrayHT=arrayHT, invHashTable=invHashTable, arrayExps=arrayExps, nextFreeIdx=idx),_,_,NONE())
      algorithm
        // a non array cref
        false := ComponentReference.crefHaveSubs(inSrc);
        nonArrayHT := BaseHashTable.add((inSrc, inDst),nonArrayHT);

        // add cref assignment to inverse hash table
        if Expression.isCref(inDst) or Expression.isNegativeUnary(inDst) then
          print("check inverse!\n");
          dst := if Expression.isNegativeUnary(inDst) then Expression.expCrefNegCref(inDst) else Expression.expCref(inDst);
          dst := ComponentReference.crefStripSubs(dst);
          if BaseHashTable.hasKey(dst,invHashTable) then
            print("inverse has key!\n");
            srcLst := BaseHashTable.get(dst,invHashTable);
            invHashTable := BaseHashTable.add((dst, inSrc::srcLst),invHashTable);
          else invHashTable := BaseHashTable.add((dst, {inSrc}),invHashTable);
          end if;
        end if;

        //update the other alias vars of this one
        repl := updateAlias(inSrc,REPLACEMENTS(nonArrayHT, arrayHT, invHashTable, arrayExps, idx));
      then repl;
    case (_,_,_,_)
      equation
        print("-BackendArrayVarTransform.addArrReplacement failed for " + ComponentReference.printComponentRefStr(inSrc)+"\n");
      then
        fail();
  end matchcontinue;
end addArrReplacement;


protected function updateAlias"checks if the src is already the bindExp of other alias. update these alias with the new repl"
  input DAE.ComponentRef src;
  input ArrayVarRepl replIn;
  output ArrayVarRepl replOut;
protected
  ArrayVarRepl repl;
  DAE.ComponentRef alias;
  DAE.Exp bind;
  HashTable3.HashTable invHashTable;
  list<DAE.ComponentRef> aliasCrefs;
  list<DAE.Exp> aliasBinds;
algorithm
  REPLACEMENTS(invHashTable=invHashTable) := replIn;
  try
	  //update the other alias vars of this one
	  if BaseHashTable.hasKey(src,invHashTable) then
	    aliasCrefs := BaseHashTable.get(src,invHashTable);
	    repl := replIn;
	    for alias in aliasCrefs loop
	      (aliasBinds,{}) := getReplacement(alias,repl);
	      aliasBinds := List.map1(aliasBinds,replaceExp,repl);
	        for bind in aliasBinds loop
	          repl := addArrReplacement(repl,alias,bind,NONE());
	        end for;
	    end for;
	  end if;
	else
    repl := replIn;
  end try;
  replOut := repl;
end updateAlias;


protected function insertSubInCrefEntries"inserts a subentry in the list of subentries"
  input tuple<DAE.Subscript,DAE.Exp> entry;
  input list<tuple<DAE.Subscript,DAE.Exp>> crefEntriesIn;
  input list<tuple<DAE.Subscript,DAE.Exp>> foldIn;
  output list<tuple<DAE.Subscript,DAE.Exp>> foldOut;
protected
  Boolean merged;
  DAE.Subscript sub0, sub1;
  DAE.Exp exp0, exp1;
  list<tuple<DAE.Subscript,DAE.Exp>> lst, rest;
algorithm
  foldOut := matchcontinue(entry,crefEntriesIn,foldIn)
    local
  case(_,{},{})
    //no entry yet
    then({entry});
  case((sub0,exp0),(sub1,exp1)::rest,_)
    equation
    //merge subscripts if necessary
      (lst,merged) = mergeSubscripts((sub0,exp0),(sub1,exp1));
      if merged then
        lst = listAppend(foldIn,lst);
      else
        lst = insertSubInCrefEntries((sub0,exp0),rest,listAppend(foldIn,lst));
      end if;
    then lst;
  case(_,{},_)
    equation
    //append entry
      lst = entry::foldIn;
    then lst;
  end matchcontinue;
end insertSubInCrefEntries;

protected function mergeSubscripts
"compares 2 subscripts and merges both entries to get a rising subscript order.
If sub1 is smaller than sub2, it will be prepended.
If sub1 is bigger it wont be merched and the upper function calls the next bigger sub2
Always merge only the parts of sub1 that interfer with sub2"
  input tuple<DAE.Subscript,DAE.Exp> sub1; // to be inserted
  input tuple<DAE.Subscript,DAE.Exp> sub2;
  output list<tuple<DAE.Subscript,DAE.Exp>> mergeLst;
  output Boolean finished; // true: stop at this sub2, false: upper function calls next sub2
algorithm
  (mergeLst,finished) := matchcontinue(sub1,sub2)
    local
      Integer i1,i2,start1, start2, stop1 ,stop2;
      DAE.Exp exp1,exp2;
      DAE.Type ty;

  case((DAE.INDEX(DAE.ICONST(i1)),exp1),(DAE.INDEX(DAE.ICONST(i2)),exp2))
    equation
      if intEq(i1,i2) then
        mergeLst = {sub1};//equal
        finished = true;
      elseif intLt(i1,i2) then
        mergeLst = {sub1,sub2};//less
        finished = true;
      elseif intGt(i1,i2) then
        mergeLst = {sub2};//bigger
        finished = false;
      else
        print("check this1!");
      end if;
    then (mergeLst,finished);

  case((DAE.INDEX(DAE.ICONST(i1)),exp1), (DAE.SLICE(DAE.RANGE(ty=ty,start=DAE.ICONST(start2),step=NONE(),stop=DAE.ICONST(stop2))),exp2))
    equation
      if intLt(i1,start2) then
        //less
        mergeLst={sub1,sub2};
        finished = true;
      elseif intEq(i1,start2) then
        //beginning of range
        mergeLst={sub1,(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(i1+1),NONE(),DAE.ICONST(stop2))),exp2)};
        finished = true;
      elseif intEq(i1,stop2) then
        //end of range
        mergeLst={(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start2),NONE(),DAE.ICONST(i1-1))),exp2),sub1};
        finished = true;
      elseif intGt(i1,start2) and intLt(i1,stop2) then
        //included
        mergeLst={(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start2),NONE(),DAE.ICONST(i1-1))),exp2),
                  sub1,
                  (DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(i1+1),NONE(),DAE.ICONST(stop2))),exp2) };
        finished = true;
      elseif intGt(i1,stop2) then
        //bigger
        mergeLst={sub2};
        finished = false;
      else
        print("check this2!");
      end if;
    then (mergeLst,finished);

  case((DAE.SLICE(DAE.RANGE(start=DAE.ICONST(start1),stop=DAE.ICONST(stop1))),exp1),(DAE.SLICE(DAE.RANGE(ty=ty,start=DAE.ICONST(start2),step=NONE(),stop=DAE.ICONST(stop2))),exp2))
    equation
      print("start1:"+intString(start1)+" stop1:"+intString(stop1)+" start2:"+intString(start2)+" stop2:"+intString(stop2)+"\n");
      if intLt(stop1,start2) then
        mergeLst={sub1,sub2}; //less
        finished = true;
      elseif intLe(start1,start2) and intLt(stop1,stop2) then
      // intersection sub1 before sub2
        mergeLst={(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start2),NONE(),DAE.ICONST(stop1))),exp1),
                  (DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(stop1+1),NONE(),DAE.ICONST(stop2))),exp2)};
        finished = true;
      elseif intLt(start2,start1) and intLe(stop2,stop1) then
      // intersection sub2 before sub1
        mergeLst={(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start2),NONE(),DAE.ICONST(start1-1))),exp2),
                  (DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start1),NONE(),DAE.ICONST(stop2))),exp1)};
        finished = false;
      elseif intGt(start1,start2) and intLt(stop1,stop2) then
      // inserted
        mergeLst={(DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(start2),NONE(),DAE.ICONST(start1-1))),exp2),
                  sub1,
                  (DAE.SLICE(DAE.RANGE(ty,DAE.ICONST(stop1+1),NONE(),DAE.ICONST(stop2))),exp2)}; //included
        finished = true;
      elseif intGt(start1,stop2) then
        mergeLst={sub2}; //bigger
        finished = false;
      else
        print("check this3!");
      end if;
    then (mergeLst,finished);

  case((DAE.INDEX(DAE.ICONST(i1)),exp1),(DAE.WHOLEDIM(),exp2))
    equation
      mergeLst={sub1, sub2}; //included;
      finished = true;
    then (mergeLst,finished);
  end matchcontinue;
end mergeSubscripts;


public function getReplacement "Retrives a replacement variable cref given a set of replacement rules and a
  source variable cref."
  input DAE.ComponentRef iCref;
  input ArrayVarRepl iRepl;
  output list<DAE.Exp> outCrefs;
  output list<DAE.ComponentRef> notFoundCrefs;
algorithm
  (outCrefs,notFoundCrefs) := matchcontinue(iCref,iRepl)
    local
      DAE.ComponentRef src;
      list<DAE.Exp> dst;
      HashTable2.HashTable nonArrayHT;
      HashTable.HashTable arrayHT;
      array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps;
      list<tuple<DAE.Subscript,DAE.Exp>> subExps;
      DAE.Subscript sub;
      list<DAE.ComponentRef> crefs;
      list<DAE.Subscript> subs;
    case(_, REPLACEMENTS(nonArrayHT=nonArrayHT,arrayHT=arrayHT,arrayExps=arrayExps))
      equation
        print("ststar\n");
        if ComponentReference.crefHaveSubs(iCref) then
        // its an array cref
          print("tes1\n");
          {sub} = ComponentReference.crefSubs(iCref);
          print("tes2\n");
          src = ComponentReference.crefStripSubs(iCref);
          print("tes3\n");
          subExps = arrayGet(arrayExps,BaseHashTable.get(src,arrayHT));
          print("tes4\n");
          (dst,subs) = getReplSubExps(sub,subExps);
          print("tes5\n");
          crefs = List.map1r(List.map(subs,List.create),Vectorization.replaceFirstSubsInCref,iCref);
          print("tes6\n");
        elseif BaseHashTable.hasKey(iCref,nonArrayHT) then
        print("jojo\n");
          dst = {BaseHashTable.get(iCref,nonArrayHT)};
                  print("jojo2\n");

          crefs = {};
        else
          dst = {DAE.CREF(iCref,ComponentReference.crefType(iCref))};
          crefs = {};
        end if;
      then (dst,crefs);
    else
      equation
        //dumpReplacements(iRepl);
        print("???????\n");
      then fail();
  end matchcontinue;
end getReplacement;


protected function getReplSubExps"gets the corresponding expressions for the givens ubscripts"
  input DAE.Subscript subIn;
  input list<tuple<DAE.Subscript,DAE.Exp>> subExps;
  output list<DAE.Exp> expsOut;
  output list<DAE.Subscript> notFoundSubs;
algorithm
  (expsOut,notFoundSubs) := matchcontinue(subIn,subExps)
    local
      Integer start, stop, i1;
      list<tuple<DAE.Subscript,DAE.Exp>> rest;
      DAE.Exp exp;
      list<DAE.Exp> exps;
      list<DAE.Subscript> restSubs;
  case(DAE.INDEX(DAE.ICONST(i1)),(DAE.SLICE(DAE.RANGE(start=DAE.ICONST(start), stop=DAE.ICONST(stop))),exp)::rest)
    equation
      // an index subscript
      if intGe(i1,start) and intLe(i1,stop) then
        exps = {replaceSubExp(exp,subIn)};
        restSubs = {};
      else
        (exps,restSubs) = getReplSubExps(subIn,rest);
      end if;
    then (exps,restSubs);
  case(_,{})
    then ({},{subIn});
  end matchcontinue;
end getReplSubExps;


protected function replaceSubExp"replaces a subscript in a cref exp"
  input DAE.Exp expIn;
  input DAE.Subscript subIn;
  output DAE.Exp expOut;
algorithm
  expOut := matchcontinue(expIn,subIn)
    local
      DAE.ComponentRef cref;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref, ty=ty),_)
    equation
      cref = Vectorization.replaceFirstSubsInCref(cref,{subIn});
    then (DAE.CREF(cref,ty));
  else
    then expIn;
  end matchcontinue;      
end replaceSubExp;


//-------------
//REPLACING FUNCTIONS
//-------------

public function replaceEquation
  input BackendDAE.Equation eqIn;
  input ArrayVarRepl replIn; 
  output list<BackendDAE.Equation> eqsOut;
algorithm
  eqsOut := matchcontinue(eqIn,replIn)
    local
      DAE.Exp e1, e2;
      list<DAE.Exp> es1, es2;
      list<DAE.ComponentRef> noReplCrefs1, noReplCref2;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
  case(BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr),_)
      equation
        e1 = replaceExp(e1, replIn);
        e2 = replaceExp(e2, replIn);
      then {BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr)};
    else
      then {eqIn};
  end matchcontinue;
end replaceEquation;

public function replaceExp
  input DAE.Exp inExp;
  input ArrayVarRepl replIn;
  output DAE.Exp expOut;
algorithm
  (expOut) := matchcontinue(inExp,replIn)
    local
      DAE.ComponentRef cref;
      DAE.Exp e1,e2;
      DAE.Operator op;
      list<DAE.Exp> crefExps;
      list<DAE.ComponentRef> noRepCrefs1,noRepCrefs2;
  case(DAE.CREF(componentRef=cref),_)
    equation
      (crefExps,noRepCrefs1) = getReplacement(cref,replIn);
        //print(stringDelimitList(List.map(crefExps,ExpressionDump.printExpStr),";")+"\n");
        //print(stringDelimitList(List.map(noRepCrefs1,ComponentReference.printComponentRefStr),";")+"\n");
      e1::_ = crefExps;
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

  case(_,_)
    equation
      true = Expression.isConst(inExp);
    then inExp;
  else
    equation
      print("missing case in replaceExp"+ExpressionDump.dumpExpStr(inExp,1)+"\n");
    then inExp;
  end matchcontinue; 
end replaceExp;


//-------------
//DUMPING STUFF
//-------------

public function dumpReplacements "Prints the variable replacements on form var1 -> var2"
  input ArrayVarRepl replIn;
algorithm
  _ := match (replIn)
    local
      String str, len_str;
      Integer len;
      HashTable2.HashTable naHT;
      HashTable.HashTable arrHT;
      HashTable3.HashTable invHT;
      list<tuple<DAE.ComponentRef,DAE.Exp>> tplLst;
      list<tuple<DAE.ComponentRef,Integer>> tplLst2;
      list<tuple<DAE.ComponentRef,list<DAE.ComponentRef>>> tplLst3;
      array<list<tuple<DAE.Subscript, DAE.Exp>>> arrayExps;

    case (REPLACEMENTS(nonArrayHT=naHT, arrayHT=arrHT, invHashTable=invHT, arrayExps=arrayExps)) equation
      (tplLst) = BaseHashTable.hashTableList(naHT);
      (tplLst2) = BaseHashTable.hashTableList(arrHT);
      (tplLst3) = BaseHashTable.hashTableList(invHT);
      print("\nReplacements: (");
      len = listLength(tplLst)+listLength(tplLst2);
      len_str = intString(len);
      print(len_str);
      print(")\n");
      print("NON-ARRAY-REPLACEMENTS========================================\n");
      str = stringDelimitList(List.map(tplLst,printReplacementTupleStr), "\n");
      print(str);
      print("\n");
      print("ARRAY-REPLACEMENTS========================================\n");
      str = stringDelimitList(List.map1(tplLst2,printReplacementTupleStr1,arrayExps), "\n");
      print(str);
      print("\n");
      print("INVERSE-REPLACEMENTS========================================\n");
      str = stringDelimitList(List.map(tplLst3,printReplacementTupleStr2), "\n");
      print(str);
      print("\n");
    then ();
  end match;
end dumpReplacements;

protected function printReplacementTupleStr "help function to dumpReplacements"
  input tuple<DAE.ComponentRef,DAE.Exp> tpl;
  output String str;
algorithm
  str := ComponentReference.printComponentRefStr(Util.tuple21(tpl)) + " -> " + ExpressionDump.printExpStr(Util.tuple22(tpl));
end printReplacementTupleStr;

protected function printReplacementTupleStr1 "help function to dumpReplacements"
  input tuple<DAE.ComponentRef,Integer> tpl;
  input array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps;
  output String str;
algorithm
  str := ComponentReference.printComponentRefStr(Util.tuple21(tpl)) + " -> " + stringDelimitList(List.map(arrayGet(arrayExps,(Util.tuple22(tpl))),printReplacementTupleStr1_1),"");
end printReplacementTupleStr1;

protected function printReplacementTupleStr2 "help function to dumpReplacements"
  input tuple<DAE.ComponentRef,list<DAE.ComponentRef>> tpl;
  output String str;
algorithm
  str := ComponentReference.printComponentRefStr(Util.tuple21(tpl)) + " -> " + stringDelimitList(List.map(Util.tuple22(tpl),ComponentReference.printComponentRefStr), ", ");
end printReplacementTupleStr2;

protected function printReplacementTupleStr1_1 "help function to dumpReplacements"
  input tuple<DAE.Subscript,DAE.Exp> tpl;
  output String str;
algorithm
  str := "["+ExpressionDump.printSubscriptStr(Util.tuple21(tpl)) + "] : " + ExpressionDump.printExpStr(Util.tuple22(tpl))+" ";
end printReplacementTupleStr1_1;

annotation(__OpenModelica_Interface="backend");
end BackendArrayVarTransform;
