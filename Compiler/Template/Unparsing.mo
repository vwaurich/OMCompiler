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
encapsulated package Unparsing
"
  file:        Unparsing.mo
  package:     Unparsing
  description: Generated by Susan.
"

public import Tpl;

public import SimCode;
public import SimCodeUtil;
public import BackendDAE;
public import System;
public import Absyn;
public import DAE;
public import ClassInf;
public import SCode;
public import SCodeDump;
public import Util;
public import List;
public import ComponentReference;
public import Expression;
public import ExpressionDump;
public import Config;
public import Flags;
public import Settings;
public import Patternm;
public import Error;
public import Values;
public import ValuesUtil;
public import BackendQSS;
public import BackendVariable;
public import DAEDump;
public import Algorithm;
public import DAEUtil;
public import Types;
public import FMI;
public import HpcOmSimCode;
public import HpcOmScheduler;

protected function lm_32
  input Tpl.Text in_txt;
  input SCode.Program in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      SCode.Program rest;
      SCode.Element i_cl;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           i_cl :: rest )
      equation
        txt = classExternalHeader(txt, i_cl, "");
        txt = lm_32(txt, rest);
      then txt;
  end match;
end lm_32;

public function programExternalHeader
  input Tpl.Text txt;
  input SCode.Program a_program;

  output Tpl.Text out_txt;
algorithm
  out_txt := Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                   "/* Automatically generated header for external MetaModelica functions */\n",
                                   "#ifdef __cplusplus\n",
                                   "extern \"C\" {\n",
                                   "#endif\n"
                               }, true));
  out_txt := lm_32(out_txt, a_program);
  out_txt := Tpl.softNewLine(out_txt);
  out_txt := Tpl.writeTok(out_txt, Tpl.ST_STRING_LIST({
                                       "#ifdef __cplusplus\n",
                                       "}\n",
                                       "#endif\n",
                                       "\n"
                                   }, true));
end programExternalHeader;

protected function lm_34
  input Tpl.Text in_txt;
  input list<SCode.Element> in_items;
  input SCode.Ident in_a_c_name;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items, in_a_c_name)
    local
      Tpl.Text txt;
      list<SCode.Element> rest;
      SCode.Ident a_c_name;
      SCode.Element i_elt;

    case ( txt,
           {},
           _ )
      then txt;

    case ( txt,
           i_elt :: rest,
           a_c_name )
      equation
        txt = elementExternalHeader(txt, i_elt, a_c_name);
        txt = lm_34(txt, rest, a_c_name);
      then txt;
  end match;
end lm_34;

protected function fun_35
  input Tpl.Text in_txt;
  input SCode.Element in_a_cl;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_cl)
    local
      Tpl.Text txt;
      SCode.Ident i_c_name;
      list<SCode.Element> i_p_elementLst;

    case ( txt,
           SCode.CLASS(classDef = SCode.PARTS(elementLst = i_p_elementLst), name = i_c_name) )
      equation
        txt = lm_34(txt, i_p_elementLst, i_c_name);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end fun_35;

public function classExternalHeader
  input Tpl.Text txt;
  input SCode.Element a_cl;
  input String a_pack;

  output Tpl.Text out_txt;
algorithm
  out_txt := fun_35(txt, a_cl);
end classExternalHeader;

public function pathString
  input Tpl.Text in_txt;
  input Absyn.Path in_a_path;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_path)
    local
      Tpl.Text txt;
      Absyn.Path i_path;
      Absyn.Ident i_name_1;
      String i_name;

    case ( txt,
           Absyn.IDENT(name = i_name) )
      equation
        txt = Tpl.writeStr(txt, i_name);
      then txt;

    case ( txt,
           Absyn.QUALIFIED(name = i_name_1, path = i_path) )
      equation
        txt = Tpl.writeStr(txt, i_name_1);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = pathString(txt, i_path);
      then txt;

    case ( txt,
           Absyn.FULLYQUALIFIED(path = i_path) )
      equation
        txt = pathString(txt, i_path);
      then txt;

    case ( txt,
           _ )
      then txt;
  end match;
end pathString;

public function metaHelperBoxStart
  input Tpl.Text in_txt;
  input Integer in_a_numVariables;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_numVariables)
    local
      Tpl.Text txt;
      Integer i_numVariables;

    case ( txt,
           (i_numVariables as 0) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 1) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 2) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 3) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 4) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 5) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 6) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 7) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 8) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           (i_numVariables as 9) )
      equation
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
      then txt;

    case ( txt,
           i_numVariables )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
        txt = Tpl.writeStr(txt, intString(i_numVariables));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "));
      then txt;
  end match;
end metaHelperBoxStart;

protected function lm_39
  input Tpl.Text in_txt;
  input list<SCode.Element> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<SCode.Element> rest;
      SCode.Ident i_name;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           SCode.COMPONENT(name = i_name) :: rest )
      equation
        txt = Tpl.writeStr(txt, i_name);
        txt = Tpl.nextIter(txt);
        txt = lm_39(txt, rest);
      then txt;

    case ( txt,
           _ :: rest )
      equation
        txt = lm_39(txt, rest);
      then txt;
  end match;
end lm_39;

protected function lm_40
  input Tpl.Text in_txt;
  input list<SCode.Element> in_items;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_items)
    local
      Tpl.Text txt;
      list<SCode.Element> rest;
      SCode.Ident i_name;

    case ( txt,
           {} )
      then txt;

    case ( txt,
           SCode.COMPONENT(name = i_name) :: rest )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("\""));
        txt = Tpl.writeStr(txt, i_name);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("\""));
        txt = Tpl.nextIter(txt);
        txt = lm_40(txt, rest);
      then txt;

    case ( txt,
           _ :: rest )
      equation
        txt = lm_40(txt, rest);
      then txt;
  end match;
end lm_40;

protected function fun_41
  input Tpl.Text in_txt;
  input String in_mArg;
  input Tpl.Text in_a_fieldsStr;
  input Tpl.Text in_a_nElts;
  input Tpl.Text in_a_omcname;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_mArg, in_a_fieldsStr, in_a_nElts, in_a_omcname)
    local
      Tpl.Text txt;
      Tpl.Text a_fieldsStr;
      Tpl.Text a_nElts;
      Tpl.Text a_omcname;

    case ( txt,
           "0",
           _,
           _,
           a_omcname )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("ADD_METARECORD_DEFINITIONS const char* "));
        txt = Tpl.writeText(txt, a_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__desc__fields[1] = {\"no fields\"};"));
      then txt;

    case ( txt,
           _,
           a_fieldsStr,
           a_nElts,
           a_omcname )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("ADD_METARECORD_DEFINITIONS const char* "));
        txt = Tpl.writeText(txt, a_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__desc__fields["));
        txt = Tpl.writeText(txt, a_nElts);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("] = {"));
        txt = Tpl.writeText(txt, a_fieldsStr);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("};"));
      then txt;
  end match;
end fun_41;

protected function fun_42
  input Tpl.Text in_txt;
  input list<SCode.Element> in_a_p_elementLst;
  input Tpl.Text in_a_fields;
  input Tpl.Text in_a_omcname;
  input Tpl.Text in_a_ctor;
  input Tpl.Text in_a_fullname;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_p_elementLst, in_a_fields, in_a_omcname, in_a_ctor, in_a_fullname)
    local
      Tpl.Text txt;
      Tpl.Text a_fields;
      Tpl.Text a_omcname;
      Tpl.Text a_ctor;
      Tpl.Text a_fullname;
      list<SCode.Element> i_p_elementLst;
      Integer ret_1;
      Integer ret_0;

    case ( txt,
           {},
           _,
           a_omcname,
           a_ctor,
           a_fullname )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("static const MMC_DEFSTRUCTLIT("));
        txt = Tpl.writeText(txt, a_fullname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__struct,1,"));
        txt = Tpl.writeText(txt, a_ctor);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(") {&"));
        txt = Tpl.writeText(txt, a_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "__desc}};\n",
                                    "static void *"
                                }, false));
        txt = Tpl.writeText(txt, a_fullname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" = MMC_REFSTRUCTLIT("));
        txt = Tpl.writeText(txt, a_fullname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__struct);"));
        txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE());
      then txt;

    case ( txt,
           i_p_elementLst,
           a_fields,
           a_omcname,
           a_ctor,
           a_fullname )
      equation
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("#define "));
        txt = Tpl.writeText(txt, a_fullname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("("));
        txt = Tpl.writeText(txt, a_fields);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(") (mmc_mk_box"));
        ret_0 = listLength(i_p_elementLst);
        ret_1 = intAdd(1, ret_0);
        txt = metaHelperBoxStart(txt, ret_1);
        txt = Tpl.writeText(txt, a_ctor);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(",&"));
        txt = Tpl.writeText(txt, a_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("__desc,"));
        txt = Tpl.writeText(txt, a_fields);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("))"));
        txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE());
      then txt;
  end match;
end fun_42;

public function elementExternalHeader
  input Tpl.Text in_txt;
  input SCode.Element in_a_elt;
  input String in_a_pack;

  output Tpl.Text out_txt;
algorithm
  out_txt :=
  match(in_txt, in_a_elt, in_a_pack)
    local
      Tpl.Text txt;
      String a_pack;
      SCode.Element i_elt;
      Integer i_r_index;
      SCode.Ident i_c_name;
      Absyn.Path i_r_name;
      list<SCode.Element> i_p_elementLst;
      String str_11;
      Tpl.Text l_fieldsDescription;
      Integer ret_9;
      Tpl.Text l_ctor;
      String ret_7;
      Tpl.Text l_fullname;
      Integer ret_5;
      Tpl.Text l_nElts;
      String ret_3;
      Tpl.Text l_omcname;
      Tpl.Text l_fieldsStr;
      Tpl.Text l_fields;

    case ( txt,
           SCode.CLASS(restriction = SCode.R_METARECORD(name = i_r_name, index = i_r_index), classDef = SCode.PARTS(elementLst = i_p_elementLst), name = i_c_name),
           a_pack )
      equation
        l_fields = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(",")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_fields = lm_39(l_fields, i_p_elementLst);
        l_fields = Tpl.popIter(l_fields);
        l_fieldsStr = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(",")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()));
        l_fieldsStr = lm_40(l_fieldsStr, i_p_elementLst);
        l_fieldsStr = Tpl.popIter(l_fieldsStr);
        l_omcname = Tpl.writeStr(Tpl.emptyTxt, a_pack);
        l_omcname = Tpl.writeTok(l_omcname, Tpl.ST_STRING("_"));
        l_omcname = pathString(l_omcname, i_r_name);
        l_omcname = Tpl.writeTok(l_omcname, Tpl.ST_STRING("_"));
        ret_3 = System.stringReplace(i_c_name, "_", "__");
        l_omcname = Tpl.writeStr(l_omcname, ret_3);
        ret_5 = listLength(i_p_elementLst);
        l_nElts = Tpl.writeStr(Tpl.emptyTxt, intString(ret_5));
        l_fullname = Tpl.writeStr(Tpl.emptyTxt, a_pack);
        l_fullname = Tpl.writeTok(l_fullname, Tpl.ST_STRING("__"));
        ret_7 = System.stringReplace(i_c_name, "_", "_5f");
        l_fullname = Tpl.writeStr(l_fullname, ret_7);
        ret_9 = intAdd(3, i_r_index);
        l_ctor = Tpl.writeStr(Tpl.emptyTxt, intString(ret_9));
        str_11 = Tpl.textString(l_nElts);
        l_fieldsDescription = fun_41(Tpl.emptyTxt, str_11, l_fieldsStr, l_nElts, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "#ifdef ADD_METARECORD_DEFINITIONS\n",
                                    "#ifndef "
                                }, false));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "__desc_added\n",
                                    "#define "
                                }, false));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_LINE("__desc_added\n"));
        txt = Tpl.writeText(txt, l_fieldsDescription);
        txt = Tpl.softNewLine(txt);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("ADD_METARECORD_DEFINITIONS struct record_description "));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_LINE("__desc = {\n"));
        txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2));
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("\""));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "\",\n",
                                    "\""
                                }, false));
        txt = Tpl.writeStr(txt, a_pack);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = pathString(txt, i_r_name);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("."));
        txt = Tpl.writeStr(txt, i_c_name);
        txt = Tpl.writeTok(txt, Tpl.ST_LINE("\",\n"));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_LINE("__desc__fields\n"));
        txt = Tpl.popBlock(txt);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "};\n",
                                    "#endif\n",
                                    "#else /* Only use the file as a header */\n",
                                    "extern struct record_description "
                                }, false));
        txt = Tpl.writeText(txt, l_omcname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST({
                                    "__desc;\n",
                                    "#endif\n",
                                    "#define "
                                }, false));
        txt = Tpl.writeText(txt, l_fullname);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING("_3dBOX"));
        txt = Tpl.writeText(txt, l_nElts);
        txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "));
        txt = Tpl.writeText(txt, l_ctor);
        txt = Tpl.softNewLine(txt);
        txt = fun_42(txt, i_p_elementLst, l_fields, l_omcname, l_ctor, l_fullname);
      then txt;

    case ( txt,
           (i_elt as SCode.CLASS(name = _)),
           a_pack )
      equation
        txt = classExternalHeader(txt, i_elt, a_pack);
      then txt;

    case ( txt,
           _,
           _ )
      then txt;
  end match;
end elementExternalHeader;

end Unparsing;