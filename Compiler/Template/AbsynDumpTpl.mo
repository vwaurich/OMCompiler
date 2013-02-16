encapsulated package AbsynDumpTpl
"
  file:        AbsynDumpTpl.mo
  package:     AbsynDumpTpl
  description: Generated by Susan.
"

public import Tpl;

public import Absyn;
public import Dump;

public function dumpPath
  input Tpl.Text in_txt;
  input Absyn.Path in_a_path;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_path)
    local
      Tpl.Text txt;
      Absyn.Ident i_name;
      Absyn.Path i_path;

    case ( txt,
           Absyn.FULLYQUALIFIED(path = i_path) )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = dumpPath(txt, i_path);
      then txt;

    case ( txt,
           Absyn.QUALIFIED(name = i_name, path = i_path) )
      equation
        txt = Tpl.writeStr(txt, i_name);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = dumpPath(txt, i_path);
      then txt;

    case ( txt,
           Absyn.IDENT(name = i_name) )
      equation
        txt = Tpl.writeStr(txt, i_name);
      then txt;

    case ( txt,
           _ )
      equation
        txt = errorMsg(txt, "SCodeDump.dumpPath: Unknown path.");
      then txt;
  end match;
end dumpPath;

public function dumpPathNoQual
  input Tpl.Text in_txt;
  input Absyn.Path in_a_path;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_path)
    local
      Tpl.Text txt;
      Absyn.Path i_path;

    case ( txt,
           Absyn.FULLYQUALIFIED(path = i_path) )
      equation
        txt = dumpPath(txt, i_path);
      then txt;

    case ( txt,
           i_path )
      equation
        txt = dumpPath(txt, i_path);
      then txt;
  end match;
end dumpPathNoQual;

protected function lm_6
  input Tpl.Text in_txt;
  input list<Absyn.TypeSpec> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.TypeSpec> rest;
      Absyn.TypeSpec i_ty;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_ty :: rest )
      equation
        txt = dumpTypeSpec(txt, i_ty);
        txt = Tpl.nextIter(txt);
        txt = lm_6(txt, rest);
      then txt;
  end match;
end lm_6;

public function dumpTypeSpec
  input Tpl.Text in_txt;
  input Absyn.TypeSpec in_a_typeSpec;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_typeSpec)
    local
      Tpl.Text txt;
      list<Absyn.TypeSpec> i_typeSpecs;
      Option<Absyn.ArrayDim> i_arrayDim;
      Absyn.Path i_path;
      Tpl.Text l_ty__str;
      Tpl.Text l_arraydim__str;
      Tpl.Text l_path__str;

    case ( txt,
           Absyn.TPATH(path = i_path, arrayDim = i_arrayDim) )
      equation
        l_path__str = dumpPath(Tpl.emptyTxt, i_path);
        l_arraydim__str = dumpArrayDimOpt(Tpl.emptyTxt, i_arrayDim);
        txt = Tpl.writeText(txt, l_path__str);
        txt = Tpl.writeText(txt, l_arraydim__str);
      then txt;

    case ( txt,
           Absyn.TCOMPLEX(path = i_path, typeSpecs = i_typeSpecs, arrayDim = i_arrayDim) )
      equation
        l_path__str = dumpPath(Tpl.emptyTxt, i_path);
        l_ty__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_ty__str = lm_6(l_ty__str, i_typeSpecs);
        l_ty__str = Tpl.popIter(l_ty__str);
        l_arraydim__str = dumpArrayDimOpt(Tpl.emptyTxt, i_arrayDim);
        txt = Tpl.writeText(txt, l_path__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("<"));
        txt = Tpl.writeText(txt, l_ty__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"));
        txt = Tpl.writeText(txt, l_arraydim__str);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpTypeSpec;

public function dumpArrayDimOpt
  input Tpl.Text in_txt;
  input Option<Absyn.ArrayDim> in_a_arraydim;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_arraydim)
    local
      Tpl.Text txt;
      Absyn.ArrayDim i_ad;

    case ( txt,
           SOME(i_ad) )
      equation
        txt = dumpSubscripts(txt, i_ad);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpArrayDimOpt;

protected function lm_9
  input Tpl.Text in_txt;
  input list<Absyn.Subscript> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Subscript> rest;
      Absyn.Subscript i_s;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_s :: rest )
      equation
        txt = dumpSubscript(txt, i_s);
        txt = Tpl.nextIter(txt);
        txt = lm_9(txt, rest);
      then txt;
  end match;
end lm_9;

public function dumpSubscripts
  input Tpl.Text in_txt;
  input list<Absyn.Subscript> in_a_subscripts;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_subscripts)
    local
      Tpl.Text txt;
      list<Absyn.Subscript> i_subscripts;
      Tpl.Text l_sub__str;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_subscripts )
      equation
        l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_sub__str = lm_9(l_sub__str, i_subscripts);
        l_sub__str = Tpl.popIter(l_sub__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("["));
        txt = Tpl.writeText(txt, l_sub__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"));
      then txt;
  end match;
end dumpSubscripts;

public function dumpSubscript
  input Tpl.Text in_txt;
  input Absyn.Subscript in_a_subscript;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_subscript)
    local
      Tpl.Text txt;
      Absyn.Exp i_subscript;

    case ( txt,
           Absyn.NOSUB() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"));
      then txt;

    case ( txt,
           Absyn.SUBSCRIPT(subscript = i_subscript) )
      equation
        txt = dumpExp(txt, i_subscript);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpSubscript;

protected function lm_12
  input Tpl.Text in_txt;
  input list<Absyn.Exp> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Exp> rest;
      Absyn.Exp i_e;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_e :: rest )
      equation
        txt = dumpExp(txt, i_e);
        txt = Tpl.nextIter(txt);
        txt = lm_12(txt, rest);
      then txt;
  end match;
end lm_12;

protected function lm_13
  input Tpl.Text in_txt;
  input list<Absyn.Exp> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Exp> rest;
      Absyn.Exp i_e;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_e :: rest )
      equation
        txt = dumpExp(txt, i_e);
        txt = Tpl.nextIter(txt);
        txt = lm_13(txt, rest);
      then txt;
  end match;
end lm_13;

protected function lm_14
  input Tpl.Text in_txt;
  input list<list<Absyn.Exp>> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<list<Absyn.Exp>> rest;
      list<Absyn.Exp> i_row;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_row :: rest )
      equation
        txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        txt = lm_13(txt, i_row);
        txt = Tpl.popIter(txt);
        txt = Tpl.nextIter(txt);
        txt = lm_14(txt, rest);
      then txt;
  end match;
end lm_14;

protected function lm_15
  input Tpl.Text in_txt;
  input list<Absyn.Exp> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Exp> rest;
      Absyn.Exp i_e;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_e :: rest )
      equation
        txt = dumpExp(txt, i_e);
        txt = Tpl.nextIter(txt);
        txt = lm_15(txt, rest);
      then txt;
  end match;
end lm_15;

protected function lm_16
  input Tpl.Text in_txt;
  input list<Absyn.Exp> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Exp> rest;
      Absyn.Exp i_e;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_e :: rest )
      equation
        txt = dumpExp(txt, i_e);
        txt = Tpl.nextIter(txt);
        txt = lm_16(txt, rest);
      then txt;
  end match;
end lm_16;

public function dumpExp
  input Tpl.Text in_txt;
  input Absyn.Exp in_a_exp;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_exp)
    local
      Tpl.Text txt;
      list<Absyn.Exp> i_exps;
      Absyn.Exp i_rest;
      Absyn.Exp i_head;
      list<Absyn.Exp> i_expressions;
      Absyn.Exp i_stop;
      Absyn.Exp i_step;
      Absyn.Exp i_start;
      list<list<Absyn.Exp>> i_matrix;
      list<Absyn.Exp> i_arrayExp;
      Absyn.FunctionArgs i_functionArgs;
      Absyn.ComponentRef i_function__;
      Absyn.Exp i_exp;
      Absyn.Operator i_op;
      Absyn.Exp i_exp2;
      Absyn.Exp i_e;
      Absyn.Exp i_exp1;
      Boolean i_value_3;
      String i_value_2;
      Absyn.ComponentRef i_componentRef;
      Real i_value_1;
      Integer i_value;
      Tpl.Text l_list__str;
      Tpl.Text l_rest__str;
      Tpl.Text l_head__str;
      Tpl.Text l_tuple__str;
      Tpl.Text l_stop__str;
      Tpl.Text l_step__str;
      Tpl.Text l_start__str;
      Tpl.Text l_matrix__str;
      Tpl.Text l_array__str;
      Tpl.Text l_args__str;
      Tpl.Text l_func__str;
      Tpl.Text l_exp__str;
      Tpl.Text l_op__str;
      Tpl.Text l_lhs__str;
      Tpl.Text l_rhs__str;

    case ( txt,
           Absyn.INTEGER(value = i_value) )
      equation
        txt = Tpl.writeStr(txt, intString(i_value));
      then txt;

    case ( txt,
           Absyn.REAL(value = i_value_1) )
      equation
        txt = Tpl.writeStr(txt, realString(i_value_1));
      then txt;

    case ( txt,
           Absyn.CREF(componentRef = i_componentRef) )
      equation
        txt = dumpCref(txt, i_componentRef);
      then txt;

    case ( txt,
           Absyn.STRING(value = i_value_2) )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("\""));
        txt = Tpl.writeStr(txt, i_value_2);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("\""));
      then txt;

    case ( txt,
           Absyn.BOOL(value = i_value_3) )
      equation
        txt = Tpl.writeStr(txt, Tpl.booleanString(i_value_3));
      then txt;

    case ( txt,
           (i_e as Absyn.BINARY(exp1 = i_exp1, exp2 = i_exp2, op = i_op)) )
      equation
        l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e);
        l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e);
        l_op__str = dumpOperator(Tpl.emptyTxt, i_op);
        txt = Tpl.writeText(txt, l_rhs__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_op__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_lhs__str);
      then txt;

    case ( txt,
           (i_e as Absyn.UNARY(exp = i_exp, op = i_op)) )
      equation
        l_exp__str = dumpOperand(Tpl.emptyTxt, i_exp, i_e);
        l_op__str = dumpOperator(Tpl.emptyTxt, i_op);
        txt = Tpl.writeText(txt, l_op__str);
        txt = Tpl.writeText(txt, l_exp__str);
      then txt;

    case ( txt,
           (i_e as Absyn.LBINARY(exp1 = i_exp1, exp2 = i_exp2, op = i_op)) )
      equation
        l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e);
        l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e);
        l_op__str = dumpOperator(Tpl.emptyTxt, i_op);
        txt = Tpl.writeText(txt, l_rhs__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_op__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_lhs__str);
      then txt;

    case ( txt,
           (i_e as Absyn.LUNARY(exp = i_exp, op = i_op)) )
      equation
        l_exp__str = dumpOperand(Tpl.emptyTxt, i_exp, i_e);
        l_op__str = dumpOperator(Tpl.emptyTxt, i_op);
        txt = Tpl.writeText(txt, l_op__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_exp__str);
      then txt;

    case ( txt,
           (i_e as Absyn.RELATION(exp1 = i_exp1, exp2 = i_exp2, op = i_op)) )
      equation
        l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e);
        l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e);
        l_op__str = dumpOperator(Tpl.emptyTxt, i_op);
        txt = Tpl.writeText(txt, l_rhs__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_op__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_lhs__str);
      then txt;

    case ( txt,
           (i_exp as Absyn.IFEXP(ifExp = _)) )
      equation
        txt = dumpIfExp(txt, i_exp);
      then txt;

    case ( txt,
           Absyn.CALL(function_ = i_function__, functionArgs = i_functionArgs) )
      equation
        l_func__str = dumpCref(Tpl.emptyTxt, i_function__);
        l_args__str = dumpFunctionArgs(Tpl.emptyTxt, i_functionArgs);
        txt = Tpl.writeText(txt, l_func__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
        txt = Tpl.writeText(txt, l_args__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"));
      then txt;

    case ( txt,
           Absyn.ARRAY(arrayExp = i_arrayExp) )
      equation
        l_array__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_array__str = lm_12(l_array__str, i_arrayExp);
        l_array__str = Tpl.popIter(l_array__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("{"));
        txt = Tpl.writeText(txt, l_array__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("}"));
      then txt;

    case ( txt,
           Absyn.MATRIX(matrix = i_matrix) )
      equation
        l_matrix__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING("; ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_matrix__str = lm_14(l_matrix__str, i_matrix);
        l_matrix__str = Tpl.popIter(l_matrix__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("["));
        txt = Tpl.writeText(txt, l_matrix__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"));
      then txt;

    case ( txt,
           (i_e as Absyn.RANGE(step = SOME(i_step), start = i_start, stop = i_stop)) )
      equation
        l_start__str = dumpOperand(Tpl.emptyTxt, i_start, i_e);
        l_step__str = dumpOperand(Tpl.emptyTxt, i_step, i_e);
        l_stop__str = dumpOperand(Tpl.emptyTxt, i_stop, i_e);
        txt = Tpl.writeText(txt, l_start__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"));
        txt = Tpl.writeText(txt, l_step__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"));
        txt = Tpl.writeText(txt, l_stop__str);
      then txt;

    case ( txt,
           (i_e as Absyn.RANGE(step = NONE(), start = i_start, stop = i_stop)) )
      equation
        l_start__str = dumpOperand(Tpl.emptyTxt, i_start, i_e);
        l_stop__str = dumpOperand(Tpl.emptyTxt, i_stop, i_e);
        txt = Tpl.writeText(txt, l_start__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"));
        txt = Tpl.writeText(txt, l_stop__str);
      then txt;

    case ( txt,
           Absyn.TUPLE(expressions = i_expressions) )
      equation
        l_tuple__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_tuple__str = lm_15(l_tuple__str, i_expressions);
        l_tuple__str = Tpl.popIter(l_tuple__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
        txt = Tpl.writeText(txt, l_tuple__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"));
      then txt;

    case ( txt,
           Absyn.END() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("end"));
      then txt;

    case ( txt,
           Absyn.AS(id = _) )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("as"));
      then txt;

    case ( txt,
           Absyn.CONS(head = i_head, rest = i_rest) )
      equation
        l_head__str = dumpExp(Tpl.emptyTxt, i_head);
        l_rest__str = dumpExp(Tpl.emptyTxt, i_rest);
        txt = Tpl.writeText(txt, l_head__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" :: "));
        txt = Tpl.writeText(txt, l_rest__str);
      then txt;

    case ( txt,
           (i_exp as Absyn.MATCHEXP(matchTy = _)) )
      equation
        txt = dumpMatchExp(txt, i_exp);
      then txt;

    case ( txt,
           Absyn.LIST(exps = i_exps) )
      equation
        l_list__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_list__str = lm_16(l_list__str, i_exps);
        l_list__str = Tpl.popIter(l_list__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("{"));
        txt = Tpl.writeText(txt, l_list__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("}"));
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpExp;

protected function fun_18
  input Tpl.Text in_txt;
  input Boolean in_mArg;
  input Tpl.Text in_a_op__str;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_mArg, in_a_op__str)
    local
      Tpl.Text txt;
      Tpl.Text a_op__str;

    case ( txt,
           false,
           a_op__str )
      equation
        txt = Tpl.writeText(txt, a_op__str);
      then txt;

    case ( txt,
           _,
           a_op__str )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
        txt = Tpl.writeText(txt, a_op__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"));
      then txt;
  end match;
end fun_18;

public function dumpOperand
  input Tpl.Text txt;
  input Absyn.Exp a_operand;
  input Absyn.Exp a_operation;

  output Tpl.Text out_txt;
protected
  Boolean ret_3;
  Integer ret_2;
  Integer ret_1;
  Tpl.Text l_op__str;
algorithm
  l_op__str := dumpExp(Tpl.emptyTxt, a_operand);
  ret_1 := Dump.expPriority(a_operation);
  ret_2 := Dump.expPriority(a_operand);
  ret_3 := intLt(ret_1, ret_2);
  out_txt := fun_18(txt, ret_3, l_op__str);
end dumpOperand;

public function dumpIfExp
  input Tpl.Text in_txt;
  input Absyn.Exp in_a_if__exp;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_if__exp)
    local
      Tpl.Text txt;
      list<tuple<Absyn.Exp, Absyn.Exp>> i_elseIfBranch;
      Absyn.Exp i_elseBranch;
      Absyn.Exp i_trueBranch;
      Absyn.Exp i_ifExp;
      Tpl.Text l_else__if__str;
      Tpl.Text l_else__branch__str;
      Tpl.Text l_true__branch__str;
      Tpl.Text l_cond__str;

    case ( txt,
           Absyn.IFEXP(ifExp = i_ifExp, trueBranch = i_trueBranch, elseBranch = i_elseBranch, elseIfBranch = i_elseIfBranch) )
      equation
        l_cond__str = dumpExp(Tpl.emptyTxt, i_ifExp);
        l_true__branch__str = dumpExp(Tpl.emptyTxt, i_trueBranch);
        l_else__branch__str = dumpExp(Tpl.emptyTxt, i_elseBranch);
        l_else__if__str = dumpElseIfExp(Tpl.emptyTxt, i_elseIfBranch);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("if "));
        txt = Tpl.writeText(txt, l_cond__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" then "));
        txt = Tpl.writeText(txt, l_true__branch__str);
        txt = Tpl.writeText(txt, l_else__if__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" else "));
        txt = Tpl.writeText(txt, l_else__branch__str);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpIfExp;

protected function lm_21
  input Tpl.Text in_txt;
  input list<tuple<Absyn.Exp, Absyn.Exp>> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<tuple<Absyn.Exp, Absyn.Exp>> rest;
      Absyn.Exp i_branch;
      Absyn.Exp i_cond;
      Tpl.Text l_branch__str;
      Tpl.Text l_cond__str;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           (i_cond, i_branch) :: rest )
      equation
        l_cond__str = dumpExp(Tpl.emptyTxt, i_cond);
        l_branch__str = dumpExp(Tpl.emptyTxt, i_branch);
        txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("elseif "));
        txt = Tpl.writeText(txt, l_cond__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" then "));
        txt = Tpl.writeText(txt, l_branch__str);
        txt = Tpl.popBlock(txt);
        txt = Tpl.nextIter(txt);
        txt = lm_21(txt, rest);
      then txt;
  end match;
end lm_21;

public function dumpElseIfExp
  input Tpl.Text txt;
  input list<tuple<Absyn.Exp, Absyn.Exp>> a_else__if;

  output Tpl.Text out_txt;
algorithm
  out_txt := Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
  out_txt := lm_21(out_txt, a_else__if);
  out_txt := Tpl.popIter(out_txt);
end dumpElseIfExp;

public function dumpMatchExp
  input Tpl.Text txt;
  input Absyn.Exp a_match__exp;

  output Tpl.Text out_txt;
algorithm
  out_txt := Tpl.writeTok(txt, Tpl.ST_STRING("MATCH_EXP"));
end dumpMatchExp;

public function dumpOperator
  input Tpl.Text in_txt;
  input Absyn.Operator in_a_op;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_op)
    local
      Tpl.Text txt;

    case ( txt,
           Absyn.ADD() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"));
      then txt;

    case ( txt,
           Absyn.SUB() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"));
      then txt;

    case ( txt,
           Absyn.MUL() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"));
      then txt;

    case ( txt,
           Absyn.DIV() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("/"));
      then txt;

    case ( txt,
           Absyn.POW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("^"));
      then txt;

    case ( txt,
           Absyn.UPLUS() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"));
      then txt;

    case ( txt,
           Absyn.UMINUS() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"));
      then txt;

    case ( txt,
           Absyn.ADD_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".+"));
      then txt;

    case ( txt,
           Absyn.SUB_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".-"));
      then txt;

    case ( txt,
           Absyn.MUL_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".*"));
      then txt;

    case ( txt,
           Absyn.DIV_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("./"));
      then txt;

    case ( txt,
           Absyn.POW_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^"));
      then txt;

    case ( txt,
           Absyn.UPLUS_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".+"));
      then txt;

    case ( txt,
           Absyn.UMINUS_EW() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(".-"));
      then txt;

    case ( txt,
           Absyn.AND() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("and"));
      then txt;

    case ( txt,
           Absyn.OR() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("or"));
      then txt;

    case ( txt,
           Absyn.NOT() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("not"));
      then txt;

    case ( txt,
           Absyn.LESS() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("<"));
      then txt;

    case ( txt,
           Absyn.LESSEQ() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("<="));
      then txt;

    case ( txt,
           Absyn.GREATER() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"));
      then txt;

    case ( txt,
           Absyn.GREATEREQ() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(">="));
      then txt;

    case ( txt,
           Absyn.EQUAL() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("=="));
      then txt;

    case ( txt,
           Absyn.NEQUAL() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("<>"));
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpOperator;

public function dumpCref
  input Tpl.Text in_txt;
  input Absyn.ComponentRef in_a_cref;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_cref)
    local
      Tpl.Text txt;
      Absyn.ComponentRef i_cref;
      Absyn.ComponentRef i_componentRef;
      list<Absyn.Subscript> i_subscripts;
      Absyn.Ident i_name;

    case ( txt,
           Absyn.CREF_QUAL(name = i_name, subscripts = i_subscripts, componentRef = i_componentRef) )
      equation
        txt = Tpl.writeStr(txt, i_name);
        txt = dumpSubscripts(txt, i_subscripts);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = dumpCref(txt, i_componentRef);
      then txt;

    case ( txt,
           Absyn.CREF_IDENT(name = i_name, subscripts = i_subscripts) )
      equation
        txt = Tpl.writeStr(txt, i_name);
        txt = dumpSubscripts(txt, i_subscripts);
      then txt;

    case ( txt,
           Absyn.CREF_FULLYQUALIFIED(componentRef = i_componentRef) )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = dumpCref(txt, i_componentRef);
      then txt;

    case ( txt,
           Absyn.WILD() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("_"));
      then txt;

    case ( txt,
           Absyn.ALLWILD() )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__"));
      then txt;

    case ( txt,
           (i_cref as Absyn.CREF_INVALID(componentRef = _)) )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("INVALID("));
        txt = dumpCref(txt, i_cref);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpCref;

protected function lm_26
  input Tpl.Text in_txt;
  input list<Absyn.Exp> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.Exp> rest;
      Absyn.Exp i_arg;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_arg :: rest )
      equation
        txt = dumpExp(txt, i_arg);
        txt = Tpl.nextIter(txt);
        txt = lm_26(txt, rest);
      then txt;
  end match;
end lm_26;

protected function lm_27
  input Tpl.Text in_txt;
  input list<Absyn.NamedArg> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<Absyn.NamedArg> rest;
      Absyn.NamedArg i_narg;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_narg :: rest )
      equation
        txt = dumpNamedArg(txt, i_narg);
        txt = Tpl.nextIter(txt);
        txt = lm_27(txt, rest);
      then txt;
  end match;
end lm_27;

protected function fun_28
  input Tpl.Text in_txt;
  input list<Absyn.NamedArg> in_a_argNames;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_argNames)
    local
      Tpl.Text txt;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           _ )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "));
      then txt;
  end match;
end fun_28;

protected function fun_29
  input Tpl.Text in_txt;
  input Tpl.Text in_a_args__str;
  input list<Absyn.NamedArg> in_a_argNames;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_args__str, in_a_argNames)
    local
      Tpl.Text txt;
      list<Absyn.NamedArg> a_argNames;

    case ( txt,
           Tpl.MEM_TEXT(tokens = {}),
           _ )
      then txt;

    case ( txt,
           _,
           a_argNames )
      equation
        txt = fun_28(txt, a_argNames);
      then txt;
  end match;
end fun_29;

protected function lm_30
  input Tpl.Text in_txt;
  input Absyn.ForIterators in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      Absyn.ForIterators rest;
      Absyn.ForIterator i_i;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_i :: rest )
      equation
        txt = dumpForIterator(txt, i_i);
        txt = Tpl.nextIter(txt);
        txt = lm_30(txt, rest);
      then txt;
  end match;
end lm_30;

public function dumpFunctionArgs
  input Tpl.Text in_txt;
  input Absyn.FunctionArgs in_a_args;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_args)
    local
      Tpl.Text txt;
      Absyn.ForIterators i_iterators;
      Absyn.Exp i_exp;
      list<Absyn.NamedArg> i_argNames;
      list<Absyn.Exp> i_args;
      Tpl.Text l_iter__str;
      Tpl.Text l_exp__str;
      Tpl.Text l_separator;
      Tpl.Text l_namedargs__str;
      Tpl.Text l_args__str;

    case ( txt,
           Absyn.FUNCTIONARGS(args = i_args, argNames = i_argNames) )
      equation
        l_args__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_args__str = lm_26(l_args__str, i_args);
        l_args__str = Tpl.popIter(l_args__str);
        l_namedargs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_namedargs__str = lm_27(l_namedargs__str, i_argNames);
        l_namedargs__str = Tpl.popIter(l_namedargs__str);
        l_separator = fun_29(Tpl.emptyTxt, l_args__str, i_argNames);
        txt = Tpl.writeText(txt, l_args__str);
        txt = Tpl.writeText(txt, l_separator);
        txt = Tpl.writeText(txt, l_namedargs__str);
      then txt;

    case ( txt,
           Absyn.FOR_ITER_FARG(exp = i_exp, iterators = i_iterators) )
      equation
        l_exp__str = dumpExp(Tpl.emptyTxt, i_exp);
        l_iter__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_iter__str = lm_30(l_iter__str, i_iterators);
        l_iter__str = Tpl.popIter(l_iter__str);
        txt = Tpl.writeText(txt, l_exp__str);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" for "));
        txt = Tpl.writeText(txt, l_iter__str);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpFunctionArgs;

public function dumpNamedArg
  input Tpl.Text in_txt;
  input Absyn.NamedArg in_a_narg;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_narg)
    local
      Tpl.Text txt;
      Absyn.Exp i_argValue;
      Absyn.Ident i_argName;

    case ( txt,
           Absyn.NAMEDARG(argName = i_argName, argValue = i_argValue) )
      equation
        txt = Tpl.writeStr(txt, i_argName);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" = "));
        txt = dumpExp(txt, i_argValue);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpNamedArg;

protected function fun_33
  input Tpl.Text in_txt;
  input Option<Absyn.Exp> in_a_range;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_range)
    local
      Tpl.Text txt;
      Absyn.Exp i_r;

    case ( txt,
           SOME(i_r) )
      equation
        txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("in "));
        txt = dumpExp(txt, i_r);
        txt = Tpl.popBlock(txt);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end fun_33;

protected function fun_34
  input Tpl.Text in_txt;
  input Option<Absyn.Exp> in_a_guardExp;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_guardExp)
    local
      Tpl.Text txt;
      Absyn.Exp i_g;

    case ( txt,
           SOME(i_g) )
      equation
        txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("guard "));
        txt = dumpExp(txt, i_g);
        txt = Tpl.popBlock(txt);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end fun_34;

public function dumpForIterator
  input Tpl.Text in_txt;
  input Absyn.ForIterator in_a_iterator;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_iterator)
    local
      Tpl.Text txt;
      String i_name;
      Option<Absyn.Exp> i_guardExp;
      Option<Absyn.Exp> i_range;
      Tpl.Text l_guard__str;
      Tpl.Text l_range__str;

    case ( txt,
           Absyn.ITERATOR(range = i_range, guardExp = i_guardExp, name = i_name) )
      equation
        l_range__str = fun_33(Tpl.emptyTxt, i_range);
        l_guard__str = fun_34(Tpl.emptyTxt, i_guardExp);
        txt = Tpl.writeStr(txt, i_name);
        txt = Tpl.writeText(txt, l_range__str);
        txt = Tpl.writeText(txt, l_guard__str);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end dumpForIterator;

public function errorMsg
  input Tpl.Text txt;
  input String a_errMessage;

  output Tpl.Text out_txt;
algorithm
  Tpl.addTemplateError(a_errMessage);
  out_txt := Tpl.writeStr(txt, a_errMessage);
end errorMsg;

end AbsynDumpTpl;