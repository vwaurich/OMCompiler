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
protected import BackendDump;
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
  input ArrayVarRepl replIn;
  input DAE.ComponentRef inSrc;
  input DAE.Exp inDst;
  output ArrayVarRepl outRepl;
algorithm
  outRepl:=
  matchcontinue (replIn,inSrc,inDst)
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

    case (REPLACEMENTS(nonArrayHT=nonArrayHT, arrayHT=arrayHT, invHashTable=invHashTable, arrayExps=arrayExps, nextFreeIdx=idx),_,_)
      algorithm
        // an array cref with a certain slice
        true := ComponentReference.crefHaveSubs(inSrc);

        {subIn} := ComponentReference.crefSubs(inSrc);
        src := ComponentReference.crefStripSubs(inSrc);
        //print("source: "+ComponentReference.printComponentRefStr(src)+"\n");
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

        //add to inverse hash table
        if Expression.isCref(inDst) or Expression.isNegativeUnary(inDst) then
          //print("check inverse1!\n");
          dst := if Expression.isNegativeUnary(inDst) then Expression.expCrefNegCref(inDst) else Expression.expCref(inDst);
          dst := ComponentReference.crefStripSubs(dst);
          if BaseHashTable.hasKey(dst,invHashTable) then
            //print("inverse has key1!\n");
            srcLst := BaseHashTable.get(dst,invHashTable);
            invHashTable := BaseHashTable.add((dst, src::srcLst),invHashTable);
          else invHashTable := BaseHashTable.add((dst, {src}),invHashTable);
          end if;
        end if;

        //update the other alias vars of this one
        repl := updateAlias(inSrc,REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,idx));
        //repl = REPLACEMENTS(nonArrayHT,arrayHT,invHashTable,arrayExps,idx);
      then repl;

    case (REPLACEMENTS(nonArrayHT=nonArrayHT, arrayHT=arrayHT, invHashTable=invHashTable, arrayExps=arrayExps, nextFreeIdx=idx),_,_)
      algorithm
        // a non array cref
        false := ComponentReference.crefHaveSubs(inSrc);
        nonArrayHT := BaseHashTable.add((inSrc, inDst),nonArrayHT);
        // add cref assignment to inverse hash table
        if Expression.isCref(inDst) or Expression.isNegativeUnary(inDst) then
          //print("check inverse2!\n");
          dst := if Expression.isNegativeUnary(inDst) then Expression.expCrefNegCref(inDst) else Expression.expCref(inDst);
          dst := ComponentReference.crefStripSubs(dst);
          if BaseHashTable.hasKey(dst,invHashTable) then
            //print("inverse has key2!\n");
            srcLst := BaseHashTable.get(dst,invHashTable);
            invHashTable := BaseHashTable.add((dst, inSrc::srcLst),invHashTable);
          else invHashTable := BaseHashTable.add((dst, {inSrc}),invHashTable);
          end if;
        end if;
        //update the other alias vars of this one
        repl := updateAlias(inSrc,REPLACEMENTS(nonArrayHT, arrayHT, invHashTable, arrayExps, idx));
      then repl;
    case (_,_,_)
      equation
        print("-BackendArrayVarTransform.addArrReplacement failed for " + ComponentReference.printComponentRefStr(inSrc)+"\n");
        dumpReplacements(replIn);
      then
        fail();
  end matchcontinue;
end addArrReplacement;


protected function updateAlias"checks if the src is already the bindExp of other alias. update these alias with the new repl"
  input DAE.ComponentRef srcIn;
  input ArrayVarRepl replIn;
  output ArrayVarRepl replOut;
protected
  ArrayVarRepl repl;
  DAE.ComponentRef alias, src;
  DAE.Exp bind;
  HashTable3.HashTable invHashTable;
  list<DAE.ComponentRef> aliasCrefs;
  list<DAE.Exp> aliasBinds;
algorithm
  replOut := matchcontinue(srcIn,replIn)
    local

  case(_,REPLACEMENTS(invHashTable=invHashTable))
    algorithm
      // array cref
      true :=  ComponentReference.crefHaveSubs(srcIn);
      src := ComponentReference.crefStripSubs(srcIn);
      if BaseHashTable.hasKey(src,invHashTable) then
        repl := replIn;
	      aliasCrefs := BaseHashTable.get(src,invHashTable);
	      for alias in aliasCrefs loop
	      	if not ComponentReference.crefEqual(alias,srcIn) then
	          // dont get into an infinite loop when assigning array vars to themselves
	          (aliasBinds,{}) := getReplacement(alias,repl);
	          aliasBinds := List.map1(aliasBinds,replaceExp,repl);
	          for bind in aliasBinds loop
	            repl := addArrReplacement(repl,alias,bind);
	          end for;
	        end if;
	      end for;
	    else
	      repl := replIn;
	    end if;
    then replIn;

  case(_,REPLACEMENTS(invHashTable=invHashTable))
    algorithm
      // non-array cref
	    if BaseHashTable.hasKey(srcIn,invHashTable) then
	      aliasCrefs := BaseHashTable.get(srcIn,invHashTable);
	      repl := replIn;
	      for alias in aliasCrefs loop
	        if not ComponentReference.crefEqual(alias,srcIn) then
	        // dont get into an infinite loop when assigning array vars to themselves
	          (aliasBinds,{}) := getReplacement(alias,repl);
	          aliasBinds := List.map1(aliasBinds,replaceExp,repl);
	          for bind in aliasBinds loop
	            repl := addArrReplacement(repl,alias,bind);
	          end for;
	        end if;
	      end for;
	    else
	      repl := replIn;
      end if;
    then repl;
  end matchcontinue;
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
  input DAE.ComponentRef crefIn;
  input ArrayVarRepl replIn;
  output list<DAE.Exp> outCrefs;
  output list<DAE.ComponentRef> notFoundCrefs;
algorithm
  (outCrefs,notFoundCrefs) := matchcontinue(crefIn,replIn)
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
        if ComponentReference.crefHaveSubs(crefIn) then
        // its an array cref
          {sub} = ComponentReference.crefSubs(crefIn);
          src = ComponentReference.crefStripSubs(crefIn);
          if BaseHashTable.hasKey(src,arrayHT) then
          // is in replacements
            subExps = arrayGet(arrayExps,BaseHashTable.get(src,arrayHT));
              //dumpReplacements(replIn);
              //print("SUB "+ExpressionDump.printSubscriptStr(sub)+"\n");
              //print(""+ stringDelimitList(List.map(subExps,printReplacementTupleStr1_1),"")+"\n");
            (dst,subs) = getReplSubExps(sub,subExps);
            crefs = List.map1r(List.map(subs,List.create),Vectorization.replaceFirstSubsInCref,crefIn);
          else
          // is not in replacements
            crefs = {};
            dst = {Expression.crefExp(crefIn)};
          end if;
        elseif BaseHashTable.hasKey(crefIn,nonArrayHT) then
          dst = {BaseHashTable.get(crefIn,nonArrayHT)};
          crefs = {};
        else
        print("here\n");
          dst = {DAE.CREF(crefIn,ComponentReference.crefType(crefIn))};
          crefs = {};
        end if;
      then (dst,crefs);
    else
      equation
      then fail();
  end matchcontinue;
end getReplacement;


protected function getReplSubExps"gets the corresponding expressions for the given subscripts"
  input DAE.Subscript subIn;
  input list<tuple<DAE.Subscript,DAE.Exp>> subExps;
  output list<DAE.Exp> expsOut;
  output list<DAE.Subscript> notFoundSubs;
algorithm
  (expsOut,notFoundSubs) := matchcontinue(subIn,subExps)
    local
      Boolean cont;
      Integer start1, stop1, start2, stop2, i1, i2;
      list<tuple<DAE.Subscript,DAE.Exp>> rest;
      DAE.Exp exp;
      list<DAE.Exp> exps;
      list<DAE.Subscript> restSubs;

  // check indexes
  case(DAE.INDEX(DAE.ICONST(i1)),(DAE.INDEX(DAE.ICONST(i2)),exp)::rest)
    equation
      // an index subscript
      if intEq(i1,i2) then
        exps = {replaceSubExp(exp,subIn)};
        restSubs = {};
      else
        (exps,restSubs) = getReplSubExps(subIn,rest);
      end if;
    then (exps,restSubs);

  // get index out of range
  case(DAE.INDEX(DAE.ICONST(i1)),(DAE.SLICE(DAE.RANGE(start=DAE.ICONST(start1), stop=DAE.ICONST(stop1))),exp)::rest)
    equation
      // an index subscript
      if intGe(i1,start1) and intLe(i1,stop1) then
        exps = {replaceSubExp(exp,subIn)};
        restSubs = {};
      else
        (exps,restSubs) = getReplSubExps(subIn,rest);
      end if;
    then (exps,restSubs);

  // get range out of range
  case(DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start1), stop=DAE.ICONST(stop1))),(DAE.INDEX(DAE.RANGE(start=DAE.ICONST(start2), stop=DAE.ICONST(stop2))),exp)::rest)
    equation
     true = intEq(start1,start2) and intEq(stop1,stop2);
     //the range fits perfectly
     //exps = {replaceSubExp(exp,subIn)};
     exps = {exp};
     restSubs = {};
    then (exps,{});

  case(_,{})
    equation
    then ({},{subIn});
  end matchcontinue;
end getReplSubExps;


public function replaceSubExp"replaces a subscript in a cref exp"
  input DAE.Exp expIn;
  input DAE.Subscript subIn;
  output DAE.Exp expOut;
algorithm
  expOut := matchcontinue(expIn,subIn)
    local
      DAE.ComponentRef cref;
      DAE.Operator op;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref, ty=ty),_)
    equation
      cref = Vectorization.replaceFirstSubsInCref(cref,{subIn});
    then (DAE.CREF(cref,ty));
  case(DAE.UNARY(operator=op, exp=DAE.CREF(componentRef=cref, ty=ty)),_)
    equation
      cref = Vectorization.replaceFirstSubsInCref(cref,{subIn});
    then (DAE.UNARY(op,DAE.CREF(cref,ty)));
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
      DAE.Exp e1, e2, iter, start, stop;
      DAE.ComponentRef cref;
      list<DAE.Exp> es1, es2;
      list<DAE.ComponentRef> allCrefs1, allCrefs2, noReplCrefs1, noReplCrefs2;
      DAE.ElementSource source;
      BackendDAE.EquationAttributes attr;
    case(BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr),_)
      equation
        print("replace in equation: "+BackendDump.equationString(eqIn)+"\n");
        e1 = replaceExp(e1, replIn);
        e2 = replaceExp(e2, replIn);
      then {BackendDAE.EQUATION(exp=e1, scalar=e2, source=source, attr=attr)};

    case(BackendDAE.FOR_EQUATION(iter=iter, start=start, stop=stop, left=e1, right=e2, source=source, attr=attr),_)
      algorithm
        e1 := replaceIteratedExp(e1,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop),replIn);
        e2 := replaceIteratedExp(e2,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop),replIn);
        //print("replaced e1 "+ExpressionDump.printExpStr(e1)+"\n");
        //print("replaced e2 "+ExpressionDump.printExpStr(e2)+"\n");
        /*
        allCrefs1 := Expression.extractCrefsFromExp(e1);
        allCrefs2 := Expression.extractCrefsFromExp(e2);
        print("ALL CREFS "+stringDelimitList(List.map(listAppend(allCrefs1,allCrefs2),ComponentReference.printComponentRefStr),", ")+"\n");
        for cref in listAppend(allCrefs1,allCrefs2) loop
          cref := replaceIteratorWithRangeInCref(cref,iter,DAE.RANGE(Expression.typeof(start),start,NONE(),stop));
          print("GET THE REPL FOR "+ComponentReference.printComponentRefStr(cref)+"\n");
          (es1,noReplCrefs1) := getReplacement(cref,replIn);
          print("GOT EXPS "+stringDelimitList(List.map(es1,ExpressionDump.printExpStr),", ")+"\n");
          print("GOT noReplCrefs1 "+stringDelimitList(List.map(noReplCrefs1,ComponentReference.printComponentRefStr),", ")+"\n");
          if not listEmpty(noReplCrefs1) or listLength(es1)>1 then print("ERROR!!! CHECK THIS1\n");dumpReplacements(replIn); end if;
        end for;*/
      then {BackendDAE.FOR_EQUATION(iter,start,stop,e1,e2,source,attr)};

    else
    equation
      then {eqIn};
  end matchcontinue;
end replaceEquation;

public function replaceIteratedExp
  input DAE.Exp expIn;
  input DAE.Exp iter;
  input DAE.Exp range;
  input ArrayVarRepl replIn;
  output DAE.Exp expOut;
algorithm
  expOut := matchcontinue(expIn,iter,range,replIn)
    local
      Absyn.Path path;
      DAE.CallAttributes attr;
      DAE.ComponentRef cref,crefNoSubs;
      DAE.Exp e1,e2,exp;
      DAE.Operator op;
      DAE.Subscript sub;
      list<DAE.Exp> crefExps, expLst;
      list<DAE.Subscript> subs;
      list<DAE.ComponentRef> noRepCrefs1;
      HashTable.HashTable arrayHT;
      list<tuple<DAE.Subscript,DAE.Exp>> subExps;
      array<list<tuple<DAE.Subscript,DAE.Exp>>> arrayExps;

  case(DAE.CREF(componentRef=cref),_,_,REPLACEMENTS(arrayHT=arrayHT,arrayExps=arrayExps))
    equation
      //(crefExps,noRepCrefs1) = getReplacement(cref,replIn);
      if ComponentReference.crefHaveSubs(cref) then
        // its an array cref
        //print("replace itereated cref\n");
        crefNoSubs = ComponentReference.crefStripSubs(cref);
        if BaseHashTable.hasKey(crefNoSubs,arrayHT) then
          // is in replacements
            subExps = arrayGet(arrayExps,BaseHashTable.get(crefNoSubs,arrayHT));
            (crefExps,subs) = getReplSubExps(DAE.INDEX(range),subExps);
            //print("crefExps "+stringDelimitList(List.map(crefExps,ExpressionDump.printExpStr),";")+"\n");
            //print("noRepCrefs1 "+stringDelimitList(List.map(noRepCrefs1,ComponentReference.printComponentRefStr),";")+"\n");
            if listEmpty(subs) and listLength(crefExps)==1 then
              exp = listHead(crefExps);
            else exp = expIn;
            end if;
        else exp = expIn;
        end if;
      else exp = expIn;
      end if;
    then exp;

  case(DAE.BINARY(exp1=e1,operator=op,exp2=e2),_,_,_)
    equation
      e1 = replaceIteratedExp(e1,iter,range,replIn);
      e2 = replaceIteratedExp(e2,iter,range,replIn);
    then DAE.BINARY(e1,op,e2);

   case(DAE.CALL(path=path,expLst=expLst,attr=attr),_,_,_)
    equation
      expLst = List.map3(expLst,replaceIteratedExp,iter,range,replIn);
    then DAE.CALL(path,expLst,attr);

  else
    then expIn;
  end matchcontinue;
end replaceIteratedExp;


public function replaceExp
  input DAE.Exp inExp;
  input ArrayVarRepl replIn;
  output DAE.Exp expOut;
algorithm
  (expOut) := matchcontinue(inExp,replIn)
    local
      Integer index;
      Absyn.Path path;
      DAE.CallAttributes attr;
      DAE.ComponentRef cref;
      DAE.Exp e1,e2,e3;
      DAE.Operator op;
      list<DAE.Exp> crefExps, expLst;
      list<DAE.ComponentRef> noRepCrefs1,noRepCrefs2;
      Option<tuple<DAE.Exp,Integer,Integer>> optionExpisASUB;
  case(DAE.CREF(componentRef=cref),_)
    equation
      (crefExps,noRepCrefs1) = getReplacement(cref,replIn);
        print("crefExps"+stringDelimitList(List.map(crefExps,ExpressionDump.printExpStr),";")+"\n");
        print("noRepCrefs1"+stringDelimitList(List.map(noRepCrefs1,ComponentReference.printComponentRefStr),";")+"\n");
      e1 = listHead(crefExps);
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

  case(DAE.RELATION(exp1=e1, operator=op, exp2=e2, index=index, optionExpisASUB=optionExpisASUB),_)
    equation
      e1 = replaceExp(e1,replIn);
      e2 = replaceExp(e2,replIn);
      e1 = ExpressionSimplify.simplify(DAE.RELATION(e1,op,e2,index,optionExpisASUB));
    then e1;

  case(DAE.IFEXP(expCond=e1, expThen=e2, expElse=e3),_)
    equation
      e1 = replaceExp(e1,replIn);
      e2 = replaceExp(e2,replIn);
      e3 = replaceExp(e3,replIn);
      e1 = ExpressionSimplify.simplify(DAE.IFEXP(e1,e2,e3));
    then e1;

  case(DAE.CALL(path=path, expLst=expLst, attr=attr),_)
    equation
      expLst = List.map1(expLst,replaceExp,replIn);
      e1 = DAE.CALL(path,expLst,attr);
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

public function replaceIteratorWithRangeInCrefInExp
  input DAE.Exp eIn;
  input tuple<DAE.Exp,DAE.Exp> tplIn; //iter,range
  output DAE.Exp eOut;
  output tuple<DAE.Exp,DAE.Exp> tplOut; //iter,range
algorithm
  (eOut,tplOut) := matchcontinue(eIn,tplIn)
    local
      DAE.ComponentRef cref;
      DAE.Exp iter, range, exp;
      DAE.Operator op;
      DAE.Type ty;
  case(DAE.CREF(componentRef=cref, ty=ty),(iter,range))
    equation
      cref = replaceIteratorWithRangeInCref(cref,iter,range);
    then (DAE.CREF(cref,ty),tplIn);
  case(DAE.UNARY(operator=op,exp=exp),(iter,range))
    equation
      (exp,_) = replaceIteratorWithRangeInCrefInExp(exp,(iter,range));
    then (exp,tplIn);
  else
    then (eIn,tplIn);
  end matchcontinue;
end replaceIteratorWithRangeInCrefInExp;

public function replaceIteratorWithRangeInCref"replaces an iterator subscript with a range expression in a componenter reference"
  input DAE.ComponentRef crefIn;
  input DAE.Exp iter;
  input DAE.Exp range;
  output DAE.ComponentRef crefOut;
algorithm
  crefOut := match(crefIn,iter,range)
    local
      DAE.Ident ident;
      DAE.Type ty;
      list<DAE.Subscript> subs;
      DAE.ComponentRef cref1;
  case(DAE.CREF_QUAL(ident,ty,subs,cref1),_,_)
    equation
      subs = List.map2(subs,replaceIteratorWithRangeInSub,iter,range);
      cref1 = replaceIteratorWithRangeInCref(cref1,iter,range);
  then DAE.CREF_QUAL(ident,ty,subs,cref1);

  case(DAE.CREF_IDENT(ident,ty,subs),_,_)
    equation
      subs = List.map2(subs,replaceIteratorWithRangeInSub,iter,range);
  then DAE.CREF_IDENT(ident,ty,subs);

  else
    then crefIn;
  end match;
end replaceIteratorWithRangeInCref;


protected function replaceIteratorWithRangeInSub"replaces an iterator subscript with a range expression in a subscript"
  input DAE.Subscript subIn;
  input DAE.Exp iter;
  input DAE.Exp range;
  output DAE.Subscript subOut;
algorithm
  subOut := matchcontinue(subIn,iter,range)
    local
      DAE.Exp iter0, exp;
      DAE.Operator op;
    case(DAE.INDEX(exp=iter0),_,_)
      equation
        true = Expression.expEqual(iter0,iter);
      then DAE.INDEX(range);
    case(DAE.INDEX(DAE.BINARY(iter0,op,exp)),_,_)
      equation
        true = Expression.expEqual(iter0,iter);
        (exp,_) = ExpressionSimplify.simplify(DAE.BINARY(range,op,exp));
      then DAE.INDEX(exp);
    case(DAE.INDEX(DAE.BINARY(exp,op,iter0)),_,_)
      equation
        true = Expression.expEqual(iter0,iter);
        (exp,_) = ExpressionSimplify.simplify(DAE.BINARY(range,op,exp));
      then DAE.INDEX(exp);
    else
      then subIn;
  end matchcontinue;
end replaceIteratorWithRangeInSub;


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
