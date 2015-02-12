// This file defines templates for transforming Modelica/MetaModelica code to FMU
// code. They are used in the code generator phase of the compiler to write
// target code.
//
// There are one root template intended to be called from the code generator:
// translateModel. These template do not return any
// result but instead write the result to files. All other templates return
// text and are used by the root templates (most of them indirectly).
//
// To future maintainers of this file:
//
// - A line like this
//     # var = "" /*BUFD*/
//   declares a text buffer that you can later append text to. It can also be
//   passed to other templates that in turn can append text to it. In the new
//   version of Susan it should be written like this instead:
//     let &var = buffer ""
//
// - A line like this
//     ..., Text var /*BUFP*/, ...
//   declares that a template takes a text buffer as input parameter. In the
//   new version of Susan it should be written like this instead:
//     ..., Text &var, ...
//
// - A line like this:
//     ..., var /*BUFC*/, ...
//   passes a text buffer to a template. In the new version of Susan it should
//   be written like this instead:
//     ..., &var, ...
//
// - Style guidelines:
//
//   - Try (hard) to limit each row to 80 characters
//
//   - Code for a template should be indented with 2 spaces
//
//     - Exception to this rule is if you have only a single case, then that
//       single case can be written using no indentation
//
//       This single case can be seen as a clarification of the input to the
//       template
//
//   - Code after a case should be indented with 2 spaces if not written on the
//     same line

package CodegenFMU

import interface SimCodeTV;
import CodegenUtil.*;
import CodegenC.*; //unqualified import, no need the CodegenC is optional when calling a template; or mandatory when the same named template exists in this package (name hiding)


template translateModel(SimCode simCode, String FMUVersion)
 "Generates C code and Makefile for compiling a FMU of a
  Modelica model."
::=
match simCode
case sc as SIMCODE(modelInfo=modelInfo as MODELINFO(__)) then
  let guid = getUUIDStr()
  let target  = simulationCodeTarget()
  let &dummy = buffer ""
  let()= textFile(simulationLiteralsFile(fileNamePrefix, literals), '<%fileNamePrefix%>_literals.h')
  let()= textFile(simulationFunctionsHeaderFile(fileNamePrefix, modelInfo.functions, recordDecls), '<%fileNamePrefix%>_functions.h')
  let()= textFile(simulationFunctionsFile(fileNamePrefix, modelInfo.functions, dummy), '<%fileNamePrefix%>_functions.c')
  let()= textFile(externalFunctionIncludes(sc.externalFunctionIncludes), '<%fileNamePrefix%>_includes.h')
  let()= textFile(recordsFile(fileNamePrefix, recordDecls), '<%fileNamePrefix%>_records.c')
  let()= textFile(simulationHeaderFile(simCode,guid), '<%fileNamePrefix%>_model.h')

  let _ = generateSimulationFiles(simCode,guid,fileNamePrefix)

  let()= textFile(simulationInitFile(simCode,guid), '<%fileNamePrefix%>_init.xml')
  let x = covertTextFileToCLiteral('<%fileNamePrefix%>_init.xml','<%fileNamePrefix%>_init.c')
  let()= textFile(fmumodel_identifierFile(simCode,guid,FMUVersion), '<%fileNamePrefix%>_FMU.c')
  let()= textFile(fmuModelDescriptionFile(simCode,guid,FMUVersion), 'modelDescription.xml')
  let()= textFile(fmudeffile(simCode,FMUVersion), '<%fileNamePrefix%>.def')
  let()= textFile(fmuMakefile(target,simCode,FMUVersion), '<%fileNamePrefix%>_FMU.makefile')
  "" // Return empty result since result written to files directly
end translateModel;

template fmuModelDescriptionFile(SimCode simCode, String guid, String FMUVersion)
 "Generates code for ModelDescription file for FMU target."
::=
match simCode
case SIMCODE(__) then
  <<
  <?xml version="1.0" encoding="UTF-8"?>
  <%
  if isFMIVersion20(FMUVersion) then fmi2ModelDescription(simCode,guid)
  else fmiModelDescription(simCode,guid)
  %>
  >>
end fmuModelDescriptionFile;

// Code for generating modelDescription.xml file for FMI 2.0 ModelExchange.
template fmi2ModelDescription(SimCode simCode, String guid)
 "Generates code for ModelDescription file for FMU target."
::=
//  <%UnitDefinitions(simCode)%>
//  <%VendorAnnotations(simCode)%>
match simCode
case SIMCODE(__) then
  <<
  <fmiModelDescription
    <%fmi2ModelDescriptionAttributes(simCode,guid)%>>
    <%ModelExchange(simCode)%>
    <%TypeDefinitions(modelInfo, "2.0")%>
    <LogCategories>
      <Category name="logEvents" />
      <Category name="logSingularLinearSystems" />
      <Category name="logNonlinearSystems" />
      <Category name="logDynamicStateSelection" />
      <Category name="logStatusWarning" />
      <Category name="logStatusDiscard" />
      <Category name="logStatusError" />
      <Category name="logStatusFatal" />
      <Category name="logStatusPending" />
      <Category name="logAll" />
      <Category name="logFmi2Call" />
    </LogCategories>
    <%DefaultExperiment(simulationSettingsOpt)%>
    <%ModelVariables(modelInfo, "2.0")%>
    <%ModelStructure(simCode, jacobianMatrixes)%>
  </fmiModelDescription>
  >>
end fmi2ModelDescription;

template fmi2ModelDescriptionAttributes(SimCode simCode, String guid)
 "Generates code for ModelDescription file for FMU target."
::=
match simCode
case SIMCODE(modelInfo = MODELINFO(varInfo = vi as VARINFO(__), vars = SIMVARS(stateVars = listStates))) then
  let fmiVersion = '2.0'
  let modelName = dotPath(modelInfo.name)
  let description = modelInfo.description
  let generationTool= 'OpenModelica Compiler <%getVersionNr()%>'
  let generationDateAndTime = xsdateTime(getCurrentDateTime())
  let variableNamingConvention = 'structured'
  let numberOfEventIndicators = vi.numZeroCrossings
  <<
  fmiVersion="<%fmiVersion%>"
  modelName="<%modelName%>"
  guid="{<%guid%>}"
  description="<%description%>"
  generationTool="<%generationTool%>"
  generationDateAndTime="<%generationDateAndTime%>"
  variableNamingConvention="<%variableNamingConvention%>"
  numberOfEventIndicators="<%numberOfEventIndicators%>"
  >>
end fmi2ModelDescriptionAttributes;

template ModelExchange(SimCode simCode)
 "Generates ModelExchange code for ModelDescription file for FMU target."
::=
match simCode
case SIMCODE(__) then
  let modelIdentifier = modelNamePrefix(simCode)
  <<
  <ModelExchange
    modelIdentifier="<%modelIdentifier%>">
  </ModelExchange>
  >>
end ModelExchange;

template ScalarVariableAttribute2(SimVar simVar)
 "Generates code for ScalarVariable Attribute file for FMU 2.0 target."
::=
match simVar
  case SIMVAR(__) then
  let valueReference = '<%System.tmpTick()%>'
  let description = if comment then 'description="<%Util.escapeModelicaStringToXmlString(comment)%>"'
  let variability = getVariability2(varKind, type_)
  let caus = getCausality2(causality, varKind, isValueChangeable)
  let initial = getInitialType(varKind, initialValue, causality, isValueChangeable)
  <<
  name="<%System.stringReplace(crefStrNoUnderscore(name),"$", "_D_")%>"
  valueReference="<%valueReference%>"
  <%description%>
  variability="<%variability%>"
  causality="<%caus%>"
  initial="<%initial%>"
  >>
end ScalarVariableAttribute2;

template getVariability2(VarKind varKind, DAE.Type type_)
 "Returns the variability Attribute of ScalarVariable."
::=
match varKind
  case DISCRETE(__) then "discrete"
  case PARAM(__) then "fixed"
  /*case PARAM(__) then "tunable"*/  /*TODO! Don't know how tunable variables are represented in OpenModelica.*/
  case CONST(__) then "constant"
  else
  match type_
    case T_REAL(__) then "continuous"
    else "discrete"
end getVariability2;

template getCausality2(Causality c, VarKind varKind, Boolean isValueChangeable)
 "Returns the Causality Attribute of ScalarVariable."
::=
match c
  case NONECAUS(__) then getCausality2Helper(varKind, isValueChangeable)
  case INTERNAL(__) then getCausality2Helper(varKind, isValueChangeable)
  case OUTPUT(__) then "output"
  case INPUT(__) then "input"
  /*TODO! Handle "independent" causality.*/
  else "local"
end getCausality2;

template getCausality2Helper(VarKind varKind, Boolean isValueChangeable)
::=
match varKind
  case PARAM(__) then if isValueChangeable then "parameter" else "calculatedParameter"
  else "local"
end getCausality2Helper;

template getInitialType(VarKind varKind, Option<DAE.Exp> initialValue, Causality c, Boolean isValueChangeable)
 "Returns the Initial Attribute of ScalarVariable."
::=
match c
  case INPUT(__) then "approx"
  else
  match initialValue
    case SOME(exp) then
    match varKind
      case STATE_DER(__) then "calculated"
      case PARAM(__) then if isValueChangeable then "exact" else "calculated"
      else "approx"
    else "calculated"
end getInitialType;

template ScalarVariableType2(SimVar simvar, list<SimVar> stateVars)
 "Generates code for ScalarVariable Type file for FMU 2.0 target.
  - Don't generate the units for now since it is wrong. If you generate a unit attribute here then we must add the UnitDefinitions tag section also.
 "
::=
match simvar
case SIMVAR(__) then
  match type_
    case T_REAL(__) then '<Real<%ScalarVariableTypeCommonAttribute2(simvar, stateVars)%>/>'
    case T_INTEGER(__) then '<Integer<%ScalarVariableTypeCommonAttribute2(simvar, stateVars)%>/>'
    case T_BOOL(__) then '<Boolean<%ScalarVariableTypeCommonAttribute2(simvar, stateVars)%>/>'
    case T_STRING(__) then '<String<%ScalarVariableTypeCommonAttribute2(simvar, stateVars)%>/>'
    case T_ENUMERATION(__) then '<Enumeration declaredType="<%Absyn.pathString2NoLeadingDot(path, ".")%>"<%ScalarVariableTypeCommonAttribute2(simvar, stateVars)%>/>'
    else 'UNKOWN_TYPE'
end ScalarVariableType2;

template ScalarVariableTypeCommonAttribute2(SimVar simvar, list<SimVar> stateVars)
 "Generates code for ScalarVariable Type file for FMU 2.0 target."
::=
match simvar
case SIMVAR(varKind = varKind, initialValue = initialValue, isValueChangeable = isValueChangeable, index = index) then
  match varKind
  case STATE_DER(__) then ' derivative="<%getStateSimVarIndexFromIndex(stateVars, index)%>"'
  else
    match varKind
    case PARAM(__) then if isValueChangeable then '<%StartString2(simvar)%><%MinString2(simvar)%><%MaxString2(simvar)%><%NominalString2(simvar)%>' else '<%MinString2(simvar)%><%MaxString2(simvar)%><%NominalString2(simvar)%>'
    else '<%StartString2(simvar)%><%MinString2(simvar)%><%MaxString2(simvar)%><%NominalString2(simvar)%>'
end ScalarVariableTypeCommonAttribute2;

template StartString2(SimVar simvar)
::=
match simvar
case SIMVAR(initialValue = initialValue) then
  match initialValue
    case SOME(e as ICONST(__)) then ' start="<%initValXml(e)%>"'
    case SOME(e as RCONST(__)) then ' start="<%initValXml(e)%>"'
    case SOME(e as SCONST(__)) then ' start="<%initValXml(e)%>"'
    case SOME(e as BCONST(__)) then ' start="<%initValXml(e)%>"'
    case SOME(e as ENUM_LITERAL(__)) then ' start="<%initValXml(e)%>"'
    else ''
end StartString2;

template MinString2(SimVar simvar)
::=
match simvar
case SIMVAR(minValue = minValue) then
  match minValue
    case SOME(e as ICONST(__)) then ' min="<%initValXml(e)%>"'
    case SOME(e as RCONST(__)) then ' min="<%initValXml(e)%>"'
    case SOME(e as SCONST(__)) then ' min="<%initValXml(e)%>"'
    case SOME(e as BCONST(__)) then ' min="<%initValXml(e)%>"'
    case SOME(e as ENUM_LITERAL(__)) then ' min="<%initValXml(e)%>"'
    else ''
end MinString2;

template MaxString2(SimVar simvar)
::=
match simvar
case SIMVAR(maxValue = maxValue) then
  match maxValue
    case SOME(e as ICONST(__)) then ' max="<%initValXml(e)%>"'
    case SOME(e as RCONST(__)) then ' max="<%initValXml(e)%>"'
    case SOME(e as SCONST(__)) then ' max="<%initValXml(e)%>"'
    case SOME(e as BCONST(__)) then ' max="<%initValXml(e)%>"'
    case SOME(e as ENUM_LITERAL(__)) then ' max="<%initValXml(e)%>"'
    else ''
end MaxString2;

template NominalString2(SimVar simvar)
::=
match simvar
case SIMVAR(nominalValue = nominalValue) then
  match nominalValue
    case SOME(e as RCONST(__)) then ' nominal="<%initValXml(e)%>"'
    else ''
end NominalString2;

// Code for generating modelDescription.xml file for FMI 1.0 ModelExchange.
template fmiModelDescription(SimCode simCode, String guid)
 "Generates code for ModelDescription file for FMU target."
::=
//  <%UnitDefinitions(simCode)%>
//  <%VendorAnnotations(simCode)%>
match simCode
case SIMCODE(__) then
  <<
  <fmiModelDescription
    <%fmiModelDescriptionAttributes(simCode,guid)%>>
    <%TypeDefinitions(modelInfo, "1.0")%>
    <%DefaultExperiment(simulationSettingsOpt)%>
    <%ModelVariables(modelInfo, "1.0")%>
  </fmiModelDescription>
  >>
end fmiModelDescription;

template fmiModelDescriptionAttributes(SimCode simCode, String guid)
 "Generates code for ModelDescription file for FMU target."
::=
match simCode
case SIMCODE(modelInfo = MODELINFO(varInfo = vi as VARINFO(__), vars = SIMVARS(stateVars = listStates))) then
  let fmiVersion = '1.0'
  let modelName = dotPath(modelInfo.name)
  let modelIdentifier = modelNamePrefix(simCode)
  let description = modelInfo.description
  let generationTool= 'OpenModelica Compiler <%getVersionNr()%>'
  let generationDateAndTime = xsdateTime(getCurrentDateTime())
  let variableNamingConvention = 'structured'
  let numberOfContinuousStates = if intEq(vi.numStateVars,1) then statesnumwithDummy(listStates) else  vi.numStateVars
  let numberOfEventIndicators = vi.numZeroCrossings
  <<
  fmiVersion="<%fmiVersion%>"
  modelName="<%modelName%>"
  modelIdentifier="<%modelIdentifier%>"
  guid="{<%guid%>}"
  description="<%description%>"
  generationTool="<%generationTool%>"
  generationDateAndTime="<%generationDateAndTime%>"
  variableNamingConvention="<%variableNamingConvention%>"
  numberOfContinuousStates="<%numberOfContinuousStates%>"
  numberOfEventIndicators="<%numberOfEventIndicators%>"
  >>
end fmiModelDescriptionAttributes;

template statesnumwithDummy(list<SimVar> vars)
" return number of states without dummy vars"
::=
 (vars |> var =>  match var case SIMVAR(__) then if stringEq(crefStr(name),"$dummy") then '0' else '1' ;separator="\n")
end statesnumwithDummy;

template xsdateTime(DateTime dt)
 "YYYY-MM-DDThh:mm:ssZ"
::=
  match dt
  case DATETIME(__) then '<%year%>-<%twodigit(mon)%>-<%twodigit(mday)%>T<%twodigit(hour)%>:<%twodigit(min)%>:<%twodigit(sec)%>Z'
end xsdateTime;

template UnitDefinitions(SimCode simCode)
 "Generates code for UnitDefinitions file for FMU target."
::=
match simCode
case SIMCODE(__) then
  <<
  <UnitDefinitions>
  </UnitDefinitions>
  >>
end UnitDefinitions;

template TypeDefinitions(ModelInfo modelInfo, String FMUVersion)
 "Generates code for TypeDefinitions for FMU target."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  <TypeDefinitions>
    <%SimCodeUtil.getEnumerationTypes(vars) |> var =>
      TypeDefinition(var,FMUVersion)
    ;separator="\n"%>
  </TypeDefinitions>
  >>
end TypeDefinitions;

template TypeDefinition(SimVar simVar, String FMUVersion)
::=
match simVar
case SIMVAR(__) then
  <<
  <%TypeDefinitionType(type_,FMUVersion)%>
  >>
end TypeDefinition;

template TypeDefinitionType(DAE.Type type_, String FMUVersion)
 "Generates code for TypeDefinitions Type file for FMU target."
::=
match type_
  case T_ENUMERATION(__) then
  if isFMIVersion20(FMUVersion) then
  <<
  <SimpleType name="<%Absyn.pathString2NoLeadingDot(path, ".")%>">
    <Enumeration>
      <%names |> name hasindex i0 fromindex 1 => '<Item name="<%name%>" value="<%i0%>"/>' ;separator="\n"%>
    </Enumeration>
  </SimpleType>
  >>
  else
  <<
  <Type name="<%Absyn.pathString2NoLeadingDot(path, ".")%>">
    <EnumerationType>
      <%names |> name => '<Item name="<%name%>"/>' ;separator="\n"%>
    </EnumerationType>
  </Type>
  >>
end TypeDefinitionType;

template DefaultExperiment(Option<SimulationSettings> simulationSettingsOpt)
 "Generates code for DefaultExperiment file for FMU target."
::=
match simulationSettingsOpt
  case SOME(v) then
    <<
    <DefaultExperiment <%DefaultExperimentAttribute(v)%>/>
    >>
end DefaultExperiment;

template DefaultExperimentAttribute(SimulationSettings simulationSettings)
 "Generates code for DefaultExperiment Attribute file for FMU target."
::=
match simulationSettings
  case SIMULATION_SETTINGS(__) then
    <<
    startTime="<%startTime%>" stopTime="<%stopTime%>" tolerance="<%tolerance%>"
    >>
end DefaultExperimentAttribute;

template VendorAnnotations(SimCode simCode)
 "Generates code for VendorAnnotations file for FMU target."
::=
match simCode
case SIMCODE(__) then
  <<
  <VendorAnnotations>
  </VendorAnnotations>
  >>
end VendorAnnotations;

template ModelVariables(ModelInfo modelInfo, String FMUVersion)
 "Generates code for ModelVariables file for FMU target."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(stateVars=stateVars)) then
  <<
  <ModelVariables>
  <%System.tmpTickReset(0)%>
  <%vars.stateVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.derivativeVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.algVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.discreteAlgVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.paramVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.aliasVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.intAlgVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.intParamVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.intAliasVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.boolAlgVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.boolParamVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.boolAliasVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.stringAlgVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.stringParamVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%vars.stringAliasVars |> var =>
    ScalarVariable(stateVars, var, FMUVersion)
  ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%externalFunctions(modelInfo)%>
  </ModelVariables>
  >>
end ModelVariables;

template ScalarVariable(list<SimVar> stateVars, SimVar simVar, String FMUVersion)
 "Generates code for ScalarVariable file for FMU target."
::=
match simVar
case SIMVAR(__) then
  if stringEq(crefStr(name),"$dummy") then
  <<>>
  else if stringEq(crefStr(name),"der($dummy)") then
  <<>>
  else if isFMIVersion20(FMUVersion) then
  <<
  <!-- Index of variable = "<%getVariableIndex(simVar)%>" -->
  <ScalarVariable
    <%ScalarVariableAttribute2(simVar)%>>
    <%ScalarVariableType2(simVar, stateVars)%>
  </ScalarVariable>
  >>
  else
  <<
  <ScalarVariable
    <%ScalarVariableAttribute(simVar)%>>
    <%ScalarVariableType(type_,unit,displayUnit,initialValue,isFixed)%>
  </ScalarVariable>
  >>
end ScalarVariable;

template ScalarVariableAttribute(SimVar simVar)
 "Generates code for ScalarVariable Attribute file for FMU target."
::=
match simVar
  case SIMVAR(__) then
  let valueReference = '<%System.tmpTick()%>'
  let variability = getVariability(varKind)
  let description = if comment then 'description="<%Util.escapeModelicaStringToXmlString(comment)%>"'
  let alias = getAliasVar(aliasvar)
  let caus = getCausality(causality)
  <<
  name="<%System.stringReplace(crefStrNoUnderscore(name),"$", "_D_")%>"
  valueReference="<%valueReference%>"
  <%description%>
  variability="<%variability%>"
  causality="<%caus%>"
  alias="<%alias%>"
  >>
end ScalarVariableAttribute;

template getCausality(Causality c)
 "Returns the Causality Attribute of ScalarVariable."
::=
match c
  case NONECAUS(__) then "none"
  case INTERNAL(__) then "internal"
  case OUTPUT(__) then "output"
  case INPUT(__) then "input"
end getCausality;

template getVariability(VarKind varKind)
 "Returns the variability Attribute of ScalarVariable."
::=
match varKind
  case DISCRETE(__) then "discrete"
  case PARAM(__) then "parameter"
  case CONST(__) then "constant"
  else "continuous"
end getVariability;

template getAliasVar(AliasVariable aliasvar)
 "Returns the alias Attribute of ScalarVariable."
::=
match aliasvar
  case NOALIAS(__) then "noAlias"
  /* We don't handle the alias and negatedAlias properly. If a variable is alias it must get the valueReference of the aliased variable. */
  /*case ALIAS(__) then "alias"
  case NEGATEDALIAS(__) then "negatedAlias"
  */
  else "noAlias"
end getAliasVar;

template ScalarVariableType(DAE.Type type_, String unit, String displayUnit, Option<DAE.Exp> initialValue, Boolean isFixed)
 "Generates code for ScalarVariable Type file for FMU target."
::=
match type_
  case T_INTEGER(__) then '<Integer<%ScalarVariableTypeCommonAttribute(initialValue,isFixed)%>/>'
  /* Don't generate the units for now since it is wrong. If you generate a unit attribute here then we must add the UnitDefinitions tag section also. */
  case T_REAL(__) then '<Real<%ScalarVariableTypeCommonAttribute(initialValue,isFixed)/*%> <%ScalarVariableTypeRealAttribute(unit,displayUnit)*/%>/>'
  case T_BOOL(__) then '<Boolean<%ScalarVariableTypeCommonAttribute(initialValue,isFixed)%>/>'
  case T_STRING(__) then '<String<%StringVariableTypeCommonAttribute(initialValue,isFixed)%>/>'
  case T_ENUMERATION(__) then '<Enumeration declaredType="<%Absyn.pathString2NoLeadingDot(path, ".")%>"<%ScalarVariableTypeCommonAttribute(initialValue,isFixed)%>/>'
  else 'UNKOWN_TYPE'
end ScalarVariableType;

template StartString(DAE.Exp exp, Boolean isFixed)
::=
match exp
  case ICONST(__) then ' start="<%initValXml(exp)%>" fixed="<%isFixed%>"'
  case RCONST(__) then ' start="<%initValXml(exp)%>" fixed="<%isFixed%>"'
  case SCONST(__) then ' start="<%initValXml(exp)%>" fixed="<%isFixed%>"'
  case BCONST(__) then ' start="<%initValXml(exp)%>" fixed="<%isFixed%>"'
  case ENUM_LITERAL(__) then ' start="<%initValXml(exp)%>" fixed="<%isFixed%>"'
  else ''
end StartString;

template ScalarVariableTypeCommonAttribute(Option<DAE.Exp> initialValue, Boolean isFixed)
 "Generates code for ScalarVariable Type file for FMU target."
::=
match initialValue
  case SOME(exp) then '<%StartString(exp, isFixed)%>'
end ScalarVariableTypeCommonAttribute;

template StringVariableTypeCommonAttribute(Option<DAE.Exp> initialValue, Boolean isFixed)
 "Generates code for ScalarVariable Type file for FMU target."
::=
match initialValue
  case SOME(exp) then ' start=<%initVal(exp)%> fixed="<%isFixed%>"'
end StringVariableTypeCommonAttribute;

template ScalarVariableTypeRealAttribute(String unit, String displayUnit)
 "Generates code for ScalarVariable Type Real file for FMU target."
::=
  let unit_ = if unit then 'unit="<%unit%>"'
  let displayUnit_ = if displayUnit then 'displayUnit="<%displayUnit%>"'
  <<
  <%unit_%> <%displayUnit_%>
  >>
end ScalarVariableTypeRealAttribute;

template externalFunctions(ModelInfo modelInfo)
 "Generates external function definitions."
::=
match modelInfo
case MODELINFO(__) then
  (functions |> fn => externalFunction(fn) ; separator="\n")
end externalFunctions;

template externalFunction(Function fn)
 "Generates external function definitions."
::=
  match fn
    case EXTERNAL_FUNCTION(dynamicLoad=true) then
      let fname = extFunctionName(extName, language)
      <<
      <ExternalFunction
        name="<%fname%>"
        valueReference="<%System.tmpTick()%>"/>
      >>
end externalFunction;

template ModelStructure(SimCode simCode, list<JacobianMatrix> jacobianMatrixes)
 "Generates Model Structure."
::=
  <<
  <ModelStructure>
    <%ModelStructureHelper(getFMIModelStructure(simCode, jacobianMatrixes))%>
  </ModelStructure>
  >>
end ModelStructure;

template ModelStructureHelper(FmiModelStructure fmiModelStructure)
 "Helper function to ModelStructure."
::=
match fmiModelStructure
case FMIMODELSTRUCTURE(__) then
  <<
  <%ModelStructureOutputs(fmiOutputs)%>
  <%ModelStructureDerivatives(fmiDerivatives)%>
  <%ModelStructureInitialUnknowns(fmiInitialUnknowns)%>
  >>
end ModelStructureHelper;

template ModelStructureOutputs(FmiOutputs fmiOutputs)
 "Generates Model Structure Outputs."
::=
match fmiOutputs
case FMIOUTPUTS(__) then
  <<
  <Outputs>
    <%ModelStructureUnknowns(fmiUnknownsList)%>
  </Outputs>
  >>
end ModelStructureOutputs;

template ModelStructureDerivatives(FmiDerivatives fmiDerivatives)
 "Generates Model Structure Derivatives."
::=
match fmiDerivatives
case FMIDERIVATIVES(__) then
  <<
  <Derivatives>
    <%ModelStructureUnknowns(fmiUnknownsList)%>
  </Derivatives>
  >>
end ModelStructureDerivatives;

template ModelStructureInitialUnknowns(FmiInitialUnknowns fmiInitialUnknowns)
 "Generates Model Structure InitialUnknowns."
::=
match fmiInitialUnknowns
case FMIINITIALUNKNOWNS(__) then
  <<
  <InitialUnknowns>
    <%ModelStructureUnknowns(fmiUnknownsList)%>
  </InitialUnknowns>
  >>
end ModelStructureInitialUnknowns;

template ModelStructureUnknowns(list<FmiUnknown> fmiUnknownsList)
 "Generates Model Structure Unknowns"
::=
  <<
  <%fmiUnknownsList |> fmiUnknown => FmiUnknownAttributes(fmiUnknown) ;separator="\n"%>
  >>
end ModelStructureUnknowns;

template FmiUnknownAttributes(FmiUnknown fmiUnknown)
 "Generates Model Structure Unknown attributes"
::=
match fmiUnknown
case FMIUNKNOWN(__) then
  <<
  <Unknown index="<%index%>"<%FmiUnknownDependencies(dependencies)%><%FmiUnknownDependenciesKind(dependenciesKind)%> />
  >>
end FmiUnknownAttributes;

template FmiUnknownDependencies(list<Integer> dependencies)
::=
  if intGt(listLength(dependencies), 0) then
  <<
   dependencies="<%dependencies |> dependency => dependency ;separator=" "%>"
  >>
end FmiUnknownDependencies;

template FmiUnknownDependenciesKind(list<String> dependenciesKind)
::=
  if intGt(listLength(dependenciesKind), 0) then
  <<
   dependenciesKind="<%dependenciesKind |> dependencyKind => dependencyKind ;separator=" "%>"
  >>
end FmiUnknownDependenciesKind;

template fmumodel_identifierFile(SimCode simCode, String guid, String FMUVersion)
 "Generates code for ModelDescription file for FMU target."
::=
match simCode
case SIMCODE(__) then
  <<

  // define class name and unique id
  #define MODEL_IDENTIFIER <%modelNamePrefix(simCode)%>
  #define MODEL_GUID "{<%guid%>}"

  // include fmu header files, typedefs and macros
  #include <stdio.h>
  #include <string.h>
  #include <assert.h>
  #include "openmodelica.h"
  #include "openmodelica_func.h"
  #include "simulation_data.h"
  #include "util/omc_error.h"
  #include "<%fileNamePrefix%>_functions.h"
  #include "<%fileNamePrefix%>_literals.h"
  #include "simulation/solver/initialization/initialization.h"
  #include "simulation/solver/events.h"
  <%if isFMIVersion20(FMUVersion) then
  '#include "fmu2_model_interface.h"'
  else
  '#include "fmu1_model_interface.h"'%>

  #ifdef __cplusplus
  extern "C" {
  #endif

  void setStartValues(ModelInstance *comp);
  void setDefaultStartValues(ModelInstance *comp);
  <%if isFMIVersion20(FMUVersion) then
  <<
  void eventUpdate(ModelInstance* comp, fmi2EventInfo* eventInfo);
  fmi2Real getReal(ModelInstance* comp, const fmi2ValueReference vr);
  fmi2Status setReal(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Real value);
  fmi2Integer getInteger(ModelInstance* comp, const fmi2ValueReference vr);
  fmi2Status setInteger(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Integer value);
  fmi2Boolean getBoolean(ModelInstance* comp, const fmi2ValueReference vr);
  fmi2Status setBoolean(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Boolean value);
  fmi2String getString(ModelInstance* comp, const fmi2ValueReference vr);
  fmi2Status setString(ModelInstance* comp, const fmi2ValueReference vr, fmi2String value);
  fmi2Status setExternalFunction(ModelInstance* c, const fmi2ValueReference vr, const void* value);
  >>
  else
  <<
  void eventUpdate(ModelInstance* comp, fmiEventInfo* eventInfo);
  fmiReal getReal(ModelInstance* comp, const fmiValueReference vr);
  fmiStatus setReal(ModelInstance* comp, const fmiValueReference vr, const fmiReal value);
  fmiInteger getInteger(ModelInstance* comp, const fmiValueReference vr);
  fmiStatus setInteger(ModelInstance* comp, const fmiValueReference vr, const fmiInteger value);
  fmiBoolean getBoolean(ModelInstance* comp, const fmiValueReference vr);
  fmiStatus setBoolean(ModelInstance* comp, const fmiValueReference vr, const fmiBoolean value);
  fmiString getString(ModelInstance* comp, const fmiValueReference vr);
  fmiStatus setString(ModelInstance* comp, const fmiValueReference vr, fmiString value);
  fmiStatus setExternalFunction(ModelInstance* c, const fmiValueReference vr, const void* value);
  >>
  %>

  <%ModelDefineData(modelInfo)%>

  // implementation of the Model Exchange functions
  <%if isFMIVersion20(FMUVersion) then
  '  extern void <%symbolName(modelNamePrefix(simCode),"setupDataStruc")%>(DATA *data);
  #define fmu2_model_interface_setupDataStruc <%symbolName(modelNamePrefix(simCode),"setupDataStruc")%>
  #include "fmu2_model_interface.c"'
  else
  '  extern void <%symbolName(modelNamePrefix(simCode),"setupDataStruc")%>(DATA *data);
  #define fmu1_model_interface_setupDataStruc <%symbolName(modelNamePrefix(simCode),"setupDataStruc")%>
  #include "fmu1_model_interface.c"'%>

  <%setDefaultStartValues(modelInfo)%>
  <%setStartValues(modelInfo)%>
  <%if isFMIVersion20(FMUVersion) then
  <<
    <%eventUpdateFunction2(simCode)%>
    <%getRealFunction2(modelInfo)%>
    <%setRealFunction2(modelInfo)%>
    <%getIntegerFunction2(modelInfo)%>
    <%setIntegerFunction2(modelInfo)%>
    <%getBooleanFunction2(modelInfo)%>
    <%setBooleanFunction2(modelInfo)%>
    <%getStringFunction2(modelInfo)%>
    <%setStringFunction2(modelInfo)%>
    <%setExternalFunction2(modelInfo)%>
  >>
  else
  <<
    <%eventUpdateFunction(simCode)%>
    <%getRealFunction(modelInfo)%>
    <%setRealFunction(modelInfo)%>
    <%getIntegerFunction(modelInfo)%>
    <%setIntegerFunction(modelInfo)%>
    <%getBooleanFunction(modelInfo)%>
    <%setBooleanFunction(modelInfo)%>
    <%getStringFunction(modelInfo)%>
    <%setStringFunction(modelInfo)%>
    <%setExternalFunction(modelInfo)%>
  >>
  %>

  #ifdef __cplusplus
  }
  #endif

  >>
end fmumodel_identifierFile;

template ModelDefineData(ModelInfo modelInfo)
 "Generates global data in simulation file."
::=
match modelInfo
case MODELINFO(varInfo=VARINFO(__), vars=SIMVARS(stateVars = listStates)) then
let numberOfReals = intAdd(intMul(varInfo.numStateVars,2),intAdd(varInfo.numDiscreteReal, intAdd(varInfo.numAlgVars,intAdd(varInfo.numParams,varInfo.numAlgAliasVars))))
let numberOfIntegers = intAdd(varInfo.numIntAlgVars,intAdd(varInfo.numIntParams,varInfo.numIntAliasVars))
let numberOfStrings = intAdd(varInfo.numStringAlgVars,intAdd(varInfo.numStringParamVars,varInfo.numStringAliasVars))
let numberOfBooleans = intAdd(varInfo.numBoolAlgVars,intAdd(varInfo.numBoolParams,varInfo.numBoolAliasVars))
  <<
  // define model size
  #define NUMBER_OF_STATES <%if intEq(varInfo.numStateVars,1) then statesnumwithDummy(listStates) else  varInfo.numStateVars%>
  #define NUMBER_OF_EVENT_INDICATORS <%varInfo.numZeroCrossings%>
  #define NUMBER_OF_REALS <%numberOfReals%>
  #define NUMBER_OF_INTEGERS <%numberOfIntegers%>
  #define NUMBER_OF_STRINGS <%numberOfStrings%>
  #define NUMBER_OF_BOOLEANS <%numberOfBooleans%>
  #define NUMBER_OF_EXTERNALFUNCTIONS <%countDynamicExternalFunctions(functions)%>

  // define variable data for model
  <%System.tmpTickReset(0)%>
  <%vars.stateVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.derivativeVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.algVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.discreteAlgVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.paramVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.aliasVars |> var => DefineVariables(var) ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.intAlgVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.intParamVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.intAliasVars |> var => DefineVariables(var) ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.boolAlgVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.boolParamVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.boolAliasVars |> var => DefineVariables(var) ;separator="\n"%>
  <%System.tmpTickReset(0)%>
  <%vars.stringAlgVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.stringParamVars |> var => DefineVariables(var) ;separator="\n"%>
  <%vars.stringAliasVars |> var => DefineVariables(var) ;separator="\n"%>


  // define initial state vector as vector of value references
  #define STATES { <%vars.stateVars |> SIMVAR(__) => if stringEq(crefStr(name),"$dummy") then '' else '<%cref(name)%>_'  ;separator=", "%> }
  #define STATESDERIVATIVES { <%vars.derivativeVars |> SIMVAR(__) => if stringEq(crefStr(name),"der($dummy)") then '' else '<%cref(name)%>_'  ;separator=", "%> }

  <%System.tmpTickReset(0)%>
  <%(functions |> fn => defineExternalFunction(fn) ; separator="\n")%>
  >>
end ModelDefineData;

template dervativeNameCStyle(ComponentRef cr)
 "Generates the name of a derivative in c style, replaces ( with _"
::=
  match cr
  case CREF_QUAL(ident = "$DER") then 'der_<%crefStr(componentRef)%>_'
end dervativeNameCStyle;

template DefineVariables(SimVar simVar)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
  let description = if comment then '// "<%comment%>"'
  if stringEq(crefStr(name),"$dummy") then
  <<>>
  else if stringEq(crefStr(name),"der($dummy)") then
  <<>>
  else
  <<
  #define <%cref(name)%>_ <%System.tmpTick()%> <%description%>
  >>
end DefineVariables;

template defineExternalFunction(Function fn)
 "Generates external function definitions."
::=
  match fn
    case EXTERNAL_FUNCTION(dynamicLoad=true) then
      let fname = extFunctionName(extName, language)
      <<
      #define $P<%fname%> <%System.tmpTick()%>
      >>
end defineExternalFunction;


template setDefaultStartValues(ModelInfo modelInfo)
 "Generates code in c file for function setStartValues() which will set start values for all variables."
::=
match modelInfo
case MODELINFO(varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars),vars=SIMVARS(__)) then
  <<
  // Set values for all variables that define a start value
  void setDefaultStartValues(ModelInstance *comp) {

  <%vars.stateVars |> var => initValsDefault(var,"realVars",0) ;separator="\n"%>
  <%vars.derivativeVars |> var => initValsDefault(var,"realVars",numStateVars) ;separator="\n"%>
  <%vars.algVars |> var => initValsDefault(var,"realVars",intMul(2,numStateVars)) ;separator="\n"%>
  <%vars.discreteAlgVars |> var => initValsDefault(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
  <%vars.intAlgVars |> var => initValsDefault(var,"integerVars",0) ;separator="\n"%>
  <%vars.boolAlgVars |> var => initValsDefault(var,"booleanVars",0) ;separator="\n"%>
  <%vars.stringAlgVars |> var => initValsDefault(var,"stringVars",0) ;separator="\n"%>
  <%vars.paramVars |> var => initParamsDefault(var,"realParameter") ;separator="\n"%>
  <%vars.intParamVars |> var => initParamsDefault(var,"integerParameter") ;separator="\n"%>
  <%vars.boolParamVars |> var => initParamsDefault(var,"booleanParameter") ;separator="\n"%>
  <%vars.stringParamVars |> var => initParamsDefault(var,"stringParameter") ;separator="\n"%>
  }
  >>
end setDefaultStartValues;

template setStartValues(ModelInfo modelInfo)
 "Generates code in c file for function setStartValues() which will set start values for all variables."
::=
match modelInfo
case MODELINFO(varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars),vars=SIMVARS(__)) then
  <<
  // Set values for all variables that define a start value
  void setStartValues(ModelInstance *comp) {

  <%vars.stateVars |> var => initVals(var,"realVars",0) ;separator="\n"%>
  <%vars.derivativeVars |> var => initVals(var,"realVars",numStateVars) ;separator="\n"%>
  <%vars.algVars |> var => initVals(var,"realVars",intMul(2,numStateVars)) ;separator="\n"%>
  <%vars.discreteAlgVars |> var => initVals(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
  <%vars.intAlgVars |> var => initVals(var,"integerVars",0) ;separator="\n"%>
  <%vars.boolAlgVars |> var => initVals(var,"booleanVars",0) ;separator="\n"%>
  <%vars.stringAlgVars |> var => initVals(var,"stringVars",0) ;separator="\n"%>
  <%vars.paramVars |> var => initParams(var,"realParameter") ;separator="\n"%>
  <%vars.intParamVars |> var => initParams(var,"integerParameter") ;separator="\n"%>
  <%vars.boolParamVars |> var => initParams(var,"booleanParameter") ;separator="\n"%>
  <%vars.stringParamVars |> var => initParams(var,"stringParameter") ;separator="\n"%>
  }
  >>
end setStartValues;

template initializeFunction(list<SimEqSystem> allEquations)
  "Generates initialize function for c file."
::=
  let &varDecls = buffer "" /*BUFD*/
  let eqPart = ""/* (allEquations |> eq as SES_SIMPLE_ASSIGN(__) =>
      equation_(eq, contextOther, &varDecls)
    ;separator="\n") */
  <<
  // Used to set the first time event, if any.
  void initialize(ModelInstance* comp, fmiEventInfo* eventInfo) {

    <%varDecls%>

    <%eqPart%>
    <%allEquations |> SES_SIMPLE_ASSIGN(__) =>
      'if (sim_verbose) { printf("Setting variable start value: %s(start=%f)\n", "<%cref(cref)%>", <%cref(cref)%>); }'
    ;separator="\n"%>

  }
  >>
end initializeFunction;


template initVals(SimVar var, String arrayName, Integer offset) ::=
  match var
    case SIMVAR(__) then
    if stringEq(crefStr(name),"$dummy") then
    <<>>
    else if stringEq(crefStr(name),"der($dummy)") then
    <<>>
    else
    let str = 'comp->fmuData->modelData.<%arrayName%>Data[<%intAdd(index,offset)%>].attribute.start'
    <<
      <%str%> =  comp->fmuData->localData[0]-><%arrayName%>[<%intAdd(index,offset)%>];
    >>
end initVals;

template initParams(SimVar var, String arrayName) ::=
  match var
    case SIMVAR(__) then
    let str = 'comp->fmuData->modelData.<%arrayName%>Data[<%index%>].attribute.start'
      '<%str%> = comp->fmuData->simulationInfo.<%arrayName%>[<%index%>];'
end initParams;

template initValsDefault(SimVar var, String arrayName, Integer offset) ::=
  match var
    case SIMVAR(index=index, type_=type_) then
    let str = 'comp->fmuData->modelData.<%arrayName%>Data[<%intAdd(index,offset)%>].attribute.start'
    match initialValue
      case SOME(v as ICONST(__))
      case SOME(v as RCONST(__))
      case SOME(v as SCONST(__))
      case SOME(v as BCONST(__))
      case SOME(v as ENUM_LITERAL(__)) then
      '<%str%> = <%initVal(v)%>;'
      else
        match type_
          case T_INTEGER(__)
          case T_REAL(__)
          case T_ENUMERATION(__)
          case T_BOOL(__) then '<%str%> = 0;'
          case T_STRING(__) then '<%str%> = "";'
          else 'UNKOWN_TYPE'
end initValsDefault;

template initParamsDefault(SimVar var, String arrayName) ::=
  match var
    case SIMVAR(__) then
    let str = 'comp->fmuData->modelData.<%arrayName%>Data[<%index%>].attribute.start'
    match initialValue
      case SOME(v) then
      '<%str%> = <%initVal(v)%>;'
end initParamsDefault;

template initVal(Exp initialValue)
::=
  match initialValue
  case ICONST(__) then integer
  case RCONST(__) then real
  case SCONST(__) then '"<%Util.escapeModelicaStringToXmlString(string)%>"'
  case BCONST(__) then if bool then "1" else "0"
  case ENUM_LITERAL(__) then '<%index%>'
  else "*ERROR* initial value of unknown type"
end initVal;

template eventUpdateFunction(SimCode simCode)
 "Generates event update function for c file."
::=
match simCode
case SIMCODE(__) then
  <<
  // Used to set the next time event, if any.
  void eventUpdate(ModelInstance* comp, fmiEventInfo* eventInfo) {
  }

  >>
end eventUpdateFunction;

template getRealFunction(ModelInfo modelInfo)
 "Generates getReal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__),varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars)) then
  <<
  fmiReal getReal(ModelInstance* comp, const fmiValueReference vr) {
    switch (vr) {
        <%vars.stateVars |> var => SwitchVars(var, "realVars", 0) ;separator="\n"%>
        <%vars.derivativeVars |> var => SwitchVars(var, "realVars", numStateVars) ;separator="\n"%>
        <%vars.algVars |> var => SwitchVars(var, "realVars", intMul(2,numStateVars)) ;separator="\n"%>
        <%vars.discreteAlgVars |> var => SwitchVars(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
        <%vars.paramVars |> var => SwitchParameters(var, "realParameter") ;separator="\n"%>
        <%vars.aliasVars |> var => SwitchAliasVars(var, "Real","-") ;separator="\n"%>
        default:
            return 0;
    }
  }

  >>
end getRealFunction;

template setRealFunction(ModelInfo modelInfo)
 "Generates setReal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__),varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars)) then
  <<
  fmiStatus setReal(ModelInstance* comp, const fmiValueReference vr, const fmiReal value) {
    switch (vr) {
        <%vars.stateVars |> var => SwitchVarsSet(var, "realVars", 0) ;separator="\n"%>
        <%vars.derivativeVars |> var => SwitchVarsSet(var, "realVars", numStateVars) ;separator="\n"%>
        <%vars.algVars |> var => SwitchVarsSet(var, "realVars", intMul(2,numStateVars)) ;separator="\n"%>
        <%vars.discreteAlgVars |> var => SwitchVarsSet(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
        <%vars.paramVars |> var => SwitchParametersSet(var, "realParameter") ;separator="\n"%>
        <%vars.aliasVars |> var => SwitchAliasVarsSet(var, "Real", "-") ;separator="\n"%>
        default:
            return fmiError;
    }
    return fmiOK;
  }

  >>
end setRealFunction;

template getIntegerFunction(ModelInfo modelInfo)
 "Generates getInteger function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiInteger getInteger(ModelInstance* comp, const fmiValueReference vr) {
    switch (vr) {
        <%vars.intAlgVars |> var => SwitchVars(var, "integerVars", 0) ;separator="\n"%>
        <%vars.intParamVars |> var => SwitchParameters(var, "integerParameter") ;separator="\n"%>
        <%vars.intAliasVars |> var => SwitchAliasVars(var, "Integer", "-") ;separator="\n"%>
        default:
            return 0;
    }
  }
  >>
end getIntegerFunction;

template setIntegerFunction(ModelInfo modelInfo)
 "Generates setInteger function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiStatus setInteger(ModelInstance* comp, const fmiValueReference vr, const fmiInteger value) {
    switch (vr) {
        <%vars.intAlgVars |> var => SwitchVarsSet(var, "integerVars", 0) ;separator="\n"%>
        <%vars.intParamVars |> var => SwitchParametersSet(var, "integerParameter") ;separator="\n"%>
        <%vars.intAliasVars |> var => SwitchAliasVarsSet(var, "Integer", "-") ;separator="\n"%>
        default:
            return fmiError;
    }
    return fmiOK;
  }
  >>
end setIntegerFunction;

template getBooleanFunction(ModelInfo modelInfo)
 "Generates getBoolean function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiBoolean getBoolean(ModelInstance* comp, const fmiValueReference vr) {
    switch (vr) {
        <%vars.boolAlgVars |> var => SwitchVars(var, "booleanVars", 0) ;separator="\n"%>
        <%vars.boolParamVars |> var => SwitchParameters(var, "booleanParameter") ;separator="\n"%>
        <%vars.boolAliasVars |> var => SwitchAliasVars(var, "Boolean", "!") ;separator="\n"%>
        default:
            return fmiFalse;
    }
  }

  >>
end getBooleanFunction;

template setBooleanFunction(ModelInfo modelInfo)
 "Generates setBoolean function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiStatus setBoolean(ModelInstance* comp, const fmiValueReference vr, const fmiBoolean value) {
    switch (vr) {
        <%vars.boolAlgVars |> var => SwitchVarsSet(var, "booleanVars", 0) ;separator="\n"%>
        <%vars.boolParamVars |> var => SwitchParametersSet(var, "booleanParameter") ;separator="\n"%>
        <%vars.boolAliasVars |> var => SwitchAliasVarsSet(var, "Boolean", "!") ;separator="\n"%>
        default:
            return fmiError;
    }
    return fmiOK;
  }

  >>
end setBooleanFunction;

template getStringFunction(ModelInfo modelInfo)
 "Generates getString function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiString getString(ModelInstance* comp, const fmiValueReference vr) {
    switch (vr) {
        <%vars.stringAlgVars |> var => SwitchVars(var, "stringVars", 0) ;separator="\n"%>
        <%vars.stringParamVars |> var => SwitchParameters(var, "stringParameter") ;separator="\n"%>
        <%vars.stringAliasVars |> var => SwitchAliasVars(var, "string", "") ;separator="\n"%>
        default:
            return "";
    }
  }

  >>
end getStringFunction;

template setStringFunction(ModelInfo modelInfo)
 "Generates setString function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmiStatus setString(ModelInstance* comp, const fmiValueReference vr, fmiString value) {
    switch (vr) {
        <%vars.stringAlgVars |> var => SwitchVarsSet(var, "stringVars", 0) ;separator="\n"%>
        <%vars.stringParamVars |> var => SwitchParametersSet(var, "stringParameter") ;separator="\n"%>
        <%vars.stringAliasVars |> var => SwitchAliasVarsSet(var, "String", "") ;separator="\n"%>
        default:
            return fmiError;
    }
    return fmiOK;
  }

  >>
end setStringFunction;

template setExternalFunction(ModelInfo modelInfo)
 "Generates setExternal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  let externalFuncs = setExternalFunctionsSwitch(functions)
  <<
  fmiStatus setExternalFunction(ModelInstance* c, const fmiValueReference vr, const void* value){
    switch (vr) {
        <%externalFuncs%>
        default:
            return fmiError;
    }
    return fmiOK;
  }

  >>
end setExternalFunction;

template eventUpdateFunction2(SimCode simCode)
 "Generates event update function for c file."
::=
match simCode
case SIMCODE(__) then
  <<
  // Used to set the next time event, if any.
  void eventUpdate(ModelInstance* comp, fmi2EventInfo* eventInfo) {
  }

  >>
end eventUpdateFunction2;

template getRealFunction2(ModelInfo modelInfo)
 "Generates getReal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__),varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars)) then
  <<
  fmi2Real getReal(ModelInstance* comp, const fmi2ValueReference vr) {
    switch (vr) {
        <%vars.stateVars |> var => SwitchVars(var, "realVars", 0) ;separator="\n"%>
        <%vars.derivativeVars |> var => SwitchVars(var, "realVars", numStateVars) ;separator="\n"%>
        <%vars.algVars |> var => SwitchVars(var, "realVars", intMul(2,numStateVars)) ;separator="\n"%>
        <%vars.discreteAlgVars |> var => SwitchVars(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
        <%vars.paramVars |> var => SwitchParameters(var, "realParameter") ;separator="\n"%>
        <%vars.aliasVars |> var => SwitchAliasVars(var, "Real","-") ;separator="\n"%>
        default:
            return 0;
    }
  }

  >>
end getRealFunction2;

template setRealFunction2(ModelInfo modelInfo)
 "Generates setReal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__),varInfo=VARINFO(numStateVars=numStateVars, numAlgVars= numAlgVars)) then
  <<
  fmi2Status setReal(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Real value) {
    switch (vr) {
        <%vars.stateVars |> var => SwitchVarsSet(var, "realVars", 0) ;separator="\n"%>
        <%vars.derivativeVars |> var => SwitchVarsSet(var, "realVars", numStateVars) ;separator="\n"%>
        <%vars.algVars |> var => SwitchVarsSet(var, "realVars", intMul(2,numStateVars)) ;separator="\n"%>
        <%vars.discreteAlgVars |> var => SwitchVarsSet(var, "realVars", intAdd(intMul(2,numStateVars), numAlgVars)) ;separator="\n"%>
        <%vars.paramVars |> var => SwitchParametersSet(var, "realParameter") ;separator="\n"%>
        <%vars.aliasVars |> var => SwitchAliasVarsSet(var, "Real", "-") ;separator="\n"%>
        default:
            return fmi2Error;
    }
    return fmi2OK;
  }

  >>
end setRealFunction2;

template getIntegerFunction2(ModelInfo modelInfo)
 "Generates setInteger function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2Integer getInteger(ModelInstance* comp, const fmi2ValueReference vr) {
    switch (vr) {
        <%vars.intAlgVars |> var => SwitchVars(var, "integerVars", 0) ;separator="\n"%>
        <%vars.intParamVars |> var => SwitchParameters(var, "integerParameter") ;separator="\n"%>
        <%vars.intAliasVars |> var => SwitchAliasVars(var, "Integer", "-") ;separator="\n"%>
        default:
            return 0;
    }
  }
  >>
end getIntegerFunction2;

template setIntegerFunction2(ModelInfo modelInfo)
 "Generates getInteger function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2Status setInteger(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Integer value) {
    switch (vr) {
        <%vars.intAlgVars |> var => SwitchVarsSet(var, "integerVars", 0) ;separator="\n"%>
        <%vars.intParamVars |> var => SwitchParametersSet(var, "integerParameter") ;separator="\n"%>
        <%vars.intAliasVars |> var => SwitchAliasVarsSet(var, "Integer", "-") ;separator="\n"%>
        default:
            return fmi2Error;
    }
    return fmi2OK;
  }
  >>
end setIntegerFunction2;

template getBooleanFunction2(ModelInfo modelInfo)
 "Generates setBoolean function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2Boolean getBoolean(ModelInstance* comp, const fmi2ValueReference vr) {
    switch (vr) {
        <%vars.boolAlgVars |> var => SwitchVars(var, "booleanVars", 0) ;separator="\n"%>
        <%vars.boolParamVars |> var => SwitchParameters(var, "booleanParameter") ;separator="\n"%>
        <%vars.boolAliasVars |> var => SwitchAliasVars(var, "Boolean", "!") ;separator="\n"%>
        default:
            return fmi2False;
    }
  }

  >>
end getBooleanFunction2;

template setBooleanFunction2(ModelInfo modelInfo)
 "Generates getBoolean function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2Status setBoolean(ModelInstance* comp, const fmi2ValueReference vr, const fmi2Boolean value) {
    switch (vr) {
        <%vars.boolAlgVars |> var => SwitchVarsSet(var, "booleanVars", 0) ;separator="\n"%>
        <%vars.boolParamVars |> var => SwitchParametersSet(var, "booleanParameter") ;separator="\n"%>
        <%vars.boolAliasVars |> var => SwitchAliasVarsSet(var, "Boolean", "!") ;separator="\n"%>
        default:
            return fmi2Error;
    }
    return fmi2OK;
  }

  >>
end setBooleanFunction2;

template getStringFunction2(ModelInfo modelInfo)
 "Generates getString function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2String getString(ModelInstance* comp, const fmi2ValueReference vr) {
    switch (vr) {
        <%vars.stringAlgVars |> var => SwitchVars(var, "stringVars", 0) ;separator="\n"%>
        <%vars.stringParamVars |> var => SwitchParameters(var, "stringParameter") ;separator="\n"%>
        <%vars.stringAliasVars |> var => SwitchAliasVars(var, "string", "") ;separator="\n"%>
        default:
            return "";
    }
  }

  >>
end getStringFunction2;

template setStringFunction2(ModelInfo modelInfo)
 "Generates setString function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  <<
  fmi2Status setString(ModelInstance* comp, const fmi2ValueReference vr, fmi2String value) {
    switch (vr) {
        <%vars.stringAlgVars |> var => SwitchVarsSet(var, "stringVars", 0) ;separator="\n"%>
        <%vars.stringParamVars |> var => SwitchParametersSet(var, "stringParameter") ;separator="\n"%>
        <%vars.stringAliasVars |> var => SwitchAliasVarsSet(var, "String", "") ;separator="\n"%>
        default:
            return fmi2Error;
    }
    return fmi2OK;
  }

  >>
end setStringFunction2;

template setExternalFunction2(ModelInfo modelInfo)
 "Generates setExternal function for c file."
::=
match modelInfo
case MODELINFO(vars=SIMVARS(__)) then
  let externalFuncs = setExternalFunctionsSwitch(functions)
  <<
  fmi2Status setExternalFunction(ModelInstance* c, const fmi2ValueReference vr, const void* value){
    switch (vr) {
        <%externalFuncs%>
        default:
            return fmi2Error;
    }
    return fmi2OK;
  }

  >>
end setExternalFunction2;

template setExternalFunctionsSwitch(list<Function> functions)
 "Generates external function definitions."
::=
  (functions |> fn => setExternalFunctionSwitch(fn) ; separator="\n")
end setExternalFunctionsSwitch;

template setExternalFunctionSwitch(Function fn)
 "Generates external function definitions."
::=
  match fn
    case EXTERNAL_FUNCTION(dynamicLoad=true) then
      let fname = extFunctionName(extName, language)
      <<
      case $P<%fname%> : ptr_<%fname%>=(ptrT_<%fname%>)value; break;
      >>
end setExternalFunctionSwitch;

template SwitchVars(SimVar simVar, String arrayName, Integer offset)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
  let description = if comment then '// "<%comment%>"'
  if stringEq(crefStr(name),"$dummy") then
  <<>>
  else if stringEq(crefStr(name),"der($dummy)") then
  <<>>
  else
  <<
  case <%cref(name)%>_ : return comp->fmuData->localData[0]-><%arrayName%>[<%intAdd(index,offset)%>]; break;
  >>
end SwitchVars;

template SwitchParameters(SimVar simVar, String arrayName)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
  let description = if comment then '// "<%comment%>"'
  <<
  case <%cref(name)%>_ : return comp->fmuData->simulationInfo.<%arrayName%>[<%index%>]; break;
  >>
end SwitchParameters;


template SwitchAliasVars(SimVar simVar, String arrayName, String negate)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
    let description = if comment then '// "<%comment%>"'
    let crefName = '<%cref(name)%>_'
      match aliasvar
        case ALIAS(__) then
        if stringEq(crefStr(varName),"time") then
        <<
        case <%crefName%> : return comp->fmuData->localData[0]->timeValue; break;
        >>
        else
        <<
        case <%crefName%> : return get<%arrayName%>(comp, <%cref(varName)%>_); break;
        >>
        case NEGATEDALIAS(__) then
        if stringEq(crefStr(varName),"time") then
        <<
        case <%crefName%> : return comp->fmuData->localData[0]->timeValue; break;
        >>
        else
        <<
        case <%crefName%> : return (<%negate%> get<%arrayName%>(comp, <%cref(varName)%>_)); break;
        >>
     end match
end SwitchAliasVars;


template SwitchVarsSet(SimVar simVar, String arrayName, Integer offset)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
  let description = if comment then '// "<%comment%>"'
  if stringEq(crefStr(name),"$dummy") then
  <<>>
  else if stringEq(crefStr(name),"der($dummy)") then
  <<>>
  else
  <<
  case <%cref(name)%>_ : comp->fmuData->localData[0]-><%arrayName%>[<%intAdd(index,offset)%>]=value; break;
  >>
end SwitchVarsSet;

template SwitchParametersSet(SimVar simVar, String arrayName)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
  let description = if comment then '// "<%comment%>"'
  <<
  case <%cref(name)%>_ : comp->fmuData->simulationInfo.<%arrayName%>[<%index%>]=value; break;
  >>
end SwitchParametersSet;


template SwitchAliasVarsSet(SimVar simVar, String arrayName, String negate)
 "Generates code for defining variables in c file for FMU target. "
::=
match simVar
  case SIMVAR(__) then
    let description = if comment then '// "<%comment%>"'
    let crefName = '<%cref(name)%>_'
      match aliasvar
        case ALIAS(__) then
        if stringEq(crefStr(varName),"time") then
        <<
        >>
        else
        <<
        case <%crefName%> : return set<%arrayName%>(comp, <%cref(varName)%>_, value); break;
        >>
        case NEGATEDALIAS(__) then
        if stringEq(crefStr(varName),"time") then
        <<
        >>
        else
        <<
        case <%crefName%> : return set<%arrayName%>(comp, <%cref(varName)%>_, (<%negate%> value)); break;
        >>
     end match
end SwitchAliasVarsSet;


template getPlatformString2(String modelNamePrefix, String platform, String fileNamePrefix, String dirExtra, String libsPos1, String libsPos2, String omhome)
 "returns compilation commands for the platform. "
::=
let fmudirname = '<%fileNamePrefix%>.fmutmp'
match platform
  case "win32" then
  <<
  <%fileNamePrefix%>_FMU: $(MAINOBJ) <%fileNamePrefix%>_functions.h <%fileNamePrefix%>_literals.h $(OFILES)
  <%\t%>$(CXX) -shared -I. -o <%modelNamePrefix%>$(DLLEXT) $(MAINOBJ) $(OFILES) $(CPPFLAGS) <%dirExtra%> <%libsPos1%> <%libsPos2%> $(CFLAGS) $(LDFLAGS) -Wl,-Bstatic -lf2c -Wl,-Bdynamic -llis -Wl,--kill-at

  <%\t%>mkdir.exe -p <%fmudirname%>
  <%\t%>mkdir.exe -p <%fmudirname%>/binaries
  <%\t%>mkdir.exe -p <%fmudirname%>/binaries/<%platform%>
  <%\t%>mkdir.exe -p <%fmudirname%>/sources

  <%\t%>dlltool -d <%fileNamePrefix%>.def --dllname <%fileNamePrefix%>$(DLLEXT) --output-lib <%fileNamePrefix%>.lib --kill-at
  <%\t%>cp <%fileNamePrefix%>$(DLLEXT) <%fmudirname%>/binaries/<%platform%>/
  <%\t%>cp <%fileNamePrefix%>.lib <%fmudirname%>/binaries/<%platform%>/
  <%\t%>cp $(GENERATEDFILES) modelDescription.xml <%fmudirname%>/sources/
  <%\t%>cp modelDescription.xml <%fmudirname%>/modelDescription.xml
  <%\t%>cp <%omhome%>/bin/libexpat.dll <%fmudirname%>/binaries/<%platform%>/
  <%\t%>cp <%omhome%>/bin/pthreadGC2.dll <%fmudirname%>/binaries/<%platform%>/
  <%\t%>cp <%omhome%>/bin/libgfortran-3.dll <%fmudirname%>/binaries/<%platform%>/
  <%\t%>cd <%fmudirname%>&& rm -f ../<%fileNamePrefix%>.fmu&& zip -r ../<%fileNamePrefix%>.fmu *
  <%\t%>rm -rf <%fmudirname%>
  <%\t%>rm -f <%fileNamePrefix%>.def <%fileNamePrefix%>.o <%fileNamePrefix%>.so <%fileNamePrefix%>_*.o
  >>
  else
  <<
  <%fileNamePrefix%>_FMU: $(MAINOBJ) <%fileNamePrefix%>_functions.h <%fileNamePrefix%>_literals.h $(OFILES)
  <%\t%>$(CXX) -shared -I. -o <%modelNamePrefix%>$(DLLEXT) $(MAINOBJ) $(OFILES) $(CPPFLAGS) <%dirExtra%> <%libsPos1%> <%libsPos2%> $(CFLAGS) $(LDFLAGS) -llis

  <%\t%>mkdir -p <%fmudirname%>
  <%\t%>mkdir -p <%fmudirname%>/binaries

  <%\t%>mkdir -p <%fmudirname%>/binaries/$(PLATFORM)
  <%\t%>mkdir -p <%fmudirname%>/sources

  <%\t%>cp <%fileNamePrefix%>$(DLLEXT) <%fmudirname%>/binaries/$(PLATFORM)/
  <%\t%>cp <%fileNamePrefix%>_FMU.libs <%fmudirname%>/binaries/$(PLATFORM)/
  <%\t%>cp $(GENERATEDFILES) modelDescription.xml <%fmudirname%>/sources/
  <%\t%>cp modelDescription.xml <%fmudirname%>/modelDescription.xml
  <%\t%>cd <%fmudirname%>; rm -f ../<%fileNamePrefix%>.fmu && zip -r ../<%fileNamePrefix%>.fmu *
  <%\t%>rm -rf <%fmudirname%>
  <%\t%>rm -f <%fileNamePrefix%>.def <%fileNamePrefix%>.o <%fileNamePrefix%>.so <%fileNamePrefix%>_*.o

  >>
end getPlatformString2;

template fmuMakefile(String target, SimCode simCode, String FMUVersion)
 "Generates the contents of the makefile for the simulation case. Copy libexpat & correct linux fmu"
::=
match target
case "msvc" then
match simCode
case SIMCODE(modelInfo=MODELINFO(__), makefileParams=MAKEFILE_PARAMS(__), simulationSettingsOpt = sopt) then
  let dirExtra = if modelInfo.directory then '-L"<%modelInfo.directory%>"' //else ""
  let libsStr = (makefileParams.libs |> lib => lib ;separator=" ")
  let libsPos1 = if not dirExtra then libsStr //else ""
  let libsPos2 = if dirExtra then libsStr // else ""
  let fmudirname = '<%fileNamePrefix%>.fmutmp'
  let extraCflags = match sopt case SOME(s as SIMULATION_SETTINGS(__)) then
    '<%match s.method
       case "inline-euler" then "-D_OMC_INLINE_EULER"
       case "inline-rungekutta" then "-D_OMC_INLINE_RK"%>'
  let compilecmds = getPlatformString2(modelNamePrefix(simCode), makefileParams.platform, fileNamePrefix, dirExtra, libsPos1, libsPos2, makefileParams.omhome)
  <<
  # Makefile generated by OpenModelica

  # Simulations use -O3 by default
  SIM_OR_DYNLOAD_OPT_LEVEL=
  MODELICAUSERCFLAGS=
  CXX=cl
  EXEEXT=.exe
  DLLEXT=.dll
  FMUEXT=.fmu
  PLATLINUX = linux32
  PLATWIN32 = win32

  # /Od - Optimization disabled
  # /EHa enable C++ EH (w/ SEH exceptions)
  # /fp:except - consider floating-point exceptions when generating code
  # /arch:SSE2 - enable use of instructions available with SSE2 enabled CPUs
  # /I - Include Directories
  # /DNOMINMAX - Define NOMINMAX (does what it says)
  # /TP - Use C++ Compiler
  CFLAGS=/Od /ZI /EHa /fp:except /I"<%makefileParams.omhome%>/include/omc/c" /I"<%makefileParams.omhome%>/include/omc/msvc/" <%if isFMIVersion20(FMUVersion) then '/I"<%makefileParams.omhome%>/include/omc/c/fmi2"' else '/I"<%makefileParams.omhome%>/include/omc/c/fmi1"'%> /I. /DNOMINMAX /TP /DNO_INTERACTIVE_DEPENDENCY

  # /ZI enable Edit and Continue debug info
  CDFLAGS = /ZI

  # /MD - link with MSVCRT.LIB
  # /link - [linker options and libraries]
  # /LIBPATH: - Directories where libs can be found
  LDFLAGS=/MD /link /dll /debug /pdb:"<%fileNamePrefix%>.pdb" /LIBPATH:"<%makefileParams.omhome%>/lib/omc/msvc/" /LIBPATH:"<%makefileParams.omhome%>/lib/omc/msvc/release/" <%dirExtra%> <%libsPos1%> <%libsPos2%> f2c.lib initialization.lib libexpat.lib math-support.lib meta.lib results.lib simulation.lib solver.lib sundials_kinsol.lib sundials_nvecserial.lib util.lib lapack_win32_MT.lib lis.lib  gc-lib.lib user32.lib pthreadVC2.lib wsock32.lib cminpack.lib umfpack.lib amd.lib

  # /MDd link with MSVCRTD.LIB debug lib
  # lib names should not be appended with a d just switch to lib/omc/msvc/debug


  FILEPREFIX=<%fileNamePrefix%>
  MAINFILE=<%fileNamePrefix%>_FMU.c
  MAINOBJ=<%fileNamePrefix%>_FMU.obj
  CFILES=<%fileNamePrefix%>.c <%fileNamePrefix%>_functions.c <%fileNamePrefix%>_records.c \
  <%fileNamePrefix%>_01exo.c <%fileNamePrefix%>_02nls.c <%fileNamePrefix%>_03lsy.c <%fileNamePrefix%>_04set.c <%fileNamePrefix%>_05evt.c <%fileNamePrefix%>_06inz.c <%fileNamePrefix%>_07dly.c \
  <%fileNamePrefix%>_08bnd.c <%fileNamePrefix%>_09alg.c <%fileNamePrefix%>_10asr.c <%fileNamePrefix%>_11mix.c <%fileNamePrefix%>_12jac.c <%fileNamePrefix%>_13opt.c <%fileNamePrefix%>_14lnz.c
  OFILES=$(CFILES:.c=.obj)
  GENERATEDFILES=$(MAINFILE) <%fileNamePrefix%>_FMU.makefile <%fileNamePrefix%>_literals.h <%fileNamePrefix%>_model.h <%fileNamePrefix%>_includes.h <%fileNamePrefix%>_functions.h  <%fileNamePrefix%>_11mix.h <%fileNamePrefix%>_12jac.h <%fileNamePrefix%>_13opt.h <%fileNamePrefix%>_init.c <%fileNamePrefix%>_info.c $(CFILES) <%fileNamePrefix%>_FMU.libs

  $(FILEPREFIX)$(FMUEXT): $(FILEPREFIX)$(DLLEXT) modelDescription.xml
      if not exist <%fmudirname%>\binaries\$(PLATWIN32) mkdir <%fmudirname%>\binaries\$(PLATWIN32)
      if not exist <%fmudirname%>\sources mkdir <%fmudirname%>\sources

      copy <%fileNamePrefix%>.dll <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%fileNamePrefix%>.lib <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%fileNamePrefix%>.pdb <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%fileNamePrefix%>.c <%fmudirname%>\sources\<%fileNamePrefix%>.c
      copy <%fileNamePrefix%>_model.h <%fmudirname%>\sources\<%fileNamePrefix%>_model.h
      copy <%fileNamePrefix%>_FMU.c <%fmudirname%>\sources\<%fileNamePrefix%>_FMU.c
      copy <%fileNamePrefix%>_info.c <%fmudirname%>\sources\<%fileNamePrefix%>_info.c
      copy <%fileNamePrefix%>_init.c <%fmudirname%>\sources\<%fileNamePrefix%>_init.c
      copy <%fileNamePrefix%>_functions.c <%fmudirname%>\sources\<%fileNamePrefix%>_functions.c
      copy <%fileNamePrefix%>_functions.h <%fmudirname%>\sources\<%fileNamePrefix%>_functions.h
      copy <%fileNamePrefix%>_records.c <%fmudirname%>\sources\<%fileNamePrefix%>_records.c
      copy modelDescription.xml <%fmudirname%>\modelDescription.xml
      copy <%stringReplace(makefileParams.omhome,"/","\\")%>\bin\SUNDIALS_KINSOL.DLL <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%stringReplace(makefileParams.omhome,"/","\\")%>\bin\SUNDIALS_NVECSERIAL.DLL <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%stringReplace(makefileParams.omhome,"/","\\")%>\bin\LAPACK_WIN32_MT.DLL <%fmudirname%>\binaries\$(PLATWIN32)
      copy <%stringReplace(makefileParams.omhome,"/","\\")%>\bin\pthreadVC2.dll <%fmudirname%>\binaries\$(PLATWIN32)
      cd <%fmudirname%>
      "zip.exe" -r ../<%fileNamePrefix%>.fmu *
      cd ..
      rm -rf <%fmudirname%>

  $(FILEPREFIX)$(DLLEXT): $(MAINOBJ) $(CFILES)
      $(CXX) /Fe$(FILEPREFIX)$(DLLEXT) $(MAINFILE) $(FILEPREFIX)_FMU.c $(CFILES) $(CFLAGS) $(LDFLAGS)
  >>
end match
case "gcc" then
match simCode
case SIMCODE(modelInfo=MODELINFO(__), makefileParams=MAKEFILE_PARAMS(__), simulationSettingsOpt = sopt) then
  let dirExtra = if modelInfo.directory then '-L"<%modelInfo.directory%>"' //else ""
  let libsStr = (makefileParams.libs |> lib => lib ;separator=" ")
  let libsPos1 = if not dirExtra then libsStr //else ""
  let libsPos2 = if dirExtra then libsStr // else ""
  let extraCflags = match sopt case SOME(s as SIMULATION_SETTINGS(__)) then
    '<%match s.method
       case "inline-euler" then "-D_OMC_INLINE_EULER"
       case "inline-rungekutta" then "-D_OMC_INLINE_RK"%>'
  let compilecmds = getPlatformString2(modelNamePrefix(simCode), makefileParams.platform, fileNamePrefix, dirExtra, libsPos1, libsPos2, makefileParams.omhome)
  let platformstr = match makefileParams.platform case "i386-pc-linux" then 'linux32' case "x86_64-linux" case "x86_64-pc-linux" then 'linux64' else '<%makefileParams.platform%>'
  <<
  # Makefile generated by OpenModelica

  # Simulation of the fmu with dymola does not work
  # with inline-small-functions
  SIM_OR_DYNLOAD_OPT_LEVEL=-O #-O2  -fno-inline-small-functions
  CC=<%makefileParams.ccompiler%>
  CXX=<%makefileParams.cxxcompiler%>
  LINK=<%makefileParams.linker%>
  EXEEXT=<%makefileParams.exeext%>
  DLLEXT=<%makefileParams.dllext%>
  CFLAGS_BASED_ON_INIT_FILE=<%extraCflags%>
  PLATFORM = <%platformstr%>
  PLAT34 = <%makefileParams.platform%>
  CFLAGS=$(CFLAGS_BASED_ON_INIT_FILE) <%makefileParams.cflags%> <%match sopt case SOME(s as SIMULATION_SETTINGS(__)) then s.cflags /* From the simulate() command */%>
  CPPFLAGS=-I"<%makefileParams.omhome%>/include/omc/c" <%if isFMIVersion20(FMUVersion) then '-I"<%makefileParams.omhome%>/include/omc/c/fmi2"' else '-I"<%makefileParams.omhome%>/include/omc/c/fmi1"'%> -I. <%makefileParams.includes ; separator=" "%>
  LDFLAGS=-L"<%makefileParams.omhome%>/lib/omc" -Wl,-rpath,'<%makefileParams.omhome%>/lib/omc' -lSimulationRuntimeC <%makefileParams.ldflags%> <%makefileParams.runtimelibs%> <%dirExtra%>
  PERL=perl
  MAINFILE=<%fileNamePrefix%>_FMU.c
  MAINOBJ=<%fileNamePrefix%>_FMU.o
  CFILES=<%fileNamePrefix%>.c <%fileNamePrefix%>_functions.c <%fileNamePrefix%>_records.c \
  <%fileNamePrefix%>_01exo.c <%fileNamePrefix%>_02nls.c <%fileNamePrefix%>_03lsy.c <%fileNamePrefix%>_04set.c <%fileNamePrefix%>_05evt.c <%fileNamePrefix%>_06inz.c <%fileNamePrefix%>_07dly.c \
  <%fileNamePrefix%>_08bnd.c <%fileNamePrefix%>_09alg.c <%fileNamePrefix%>_10asr.c <%fileNamePrefix%>_11mix.c <%fileNamePrefix%>_12jac.c <%fileNamePrefix%>_13opt.c <%fileNamePrefix%>_14lnz.c
  OFILES=$(CFILES:.c=.o)
  GENERATEDFILES=$(MAINFILE) <%fileNamePrefix%>_FMU.makefile <%fileNamePrefix%>_literals.h <%fileNamePrefix%>_model.h <%fileNamePrefix%>_includes.h <%fileNamePrefix%>_functions.h  <%fileNamePrefix%>_11mix.h <%fileNamePrefix%>_12jac.h <%fileNamePrefix%>_13opt.h <%fileNamePrefix%>_init.c <%fileNamePrefix%>_info.c $(CFILES) <%fileNamePrefix%>_FMU.libs

  # This is to make sure that <%fileNamePrefix%>_*.c are always compiled.
  .PHONY: $(CFILES)

  PHONY: <%fileNamePrefix%>_FMU
  <%compilecmds%>
  >>
end match
else
  error(sourceInfo(), 'target <%target%> is not handled!')
end fmuMakefile;

template fmudeffile(SimCode simCode, String FMUVersion)
 "Generates the def file of the fmu."
::=
match simCode
case SIMCODE(modelInfo=MODELINFO(__), makefileParams=MAKEFILE_PARAMS(__), simulationSettingsOpt = sopt) then
  if isFMIVersion20(FMUVersion) then
  <<
  EXPORTS
    ;***************************************************
    ;Common Functions
    ;****************************************************
    <%fileNamePrefix%>_fmiGetTypesPlatform @1
    <%fileNamePrefix%>_fmiGetVersion @2
    <%fileNamePrefix%>_fmiSetDebugLogging @3
    <%fileNamePrefix%>_fmiInstantiate @4
    <%fileNamePrefix%>_fmiFreeInstance @5
    <%fileNamePrefix%>_fmiSetupExperiment @6
    <%fileNamePrefix%>_fmiEnterInitializationMode @7
    <%fileNamePrefix%>_fmiExitInitializationMode @8
    <%fileNamePrefix%>_fmiTerminate @9
    <%fileNamePrefix%>_fmiReset @10
    <%fileNamePrefix%>_fmiGetReal @11
    <%fileNamePrefix%>_fmiGetInteger @12
    <%fileNamePrefix%>_fmiGetBoolean @13
    <%fileNamePrefix%>_fmiGetString @14
    <%fileNamePrefix%>_fmiSetReal @15
    <%fileNamePrefix%>_fmiSetInteger @16
    <%fileNamePrefix%>_fmiSetBoolean @17
    <%fileNamePrefix%>_fmiSetString @18
    <%fileNamePrefix%>_fmiGetFMUstate @19
    <%fileNamePrefix%>_fmiSetFMUstate @20
    <%fileNamePrefix%>_fmiFreeFMUstate @21
    <%fileNamePrefix%>_fmiSerializedFMUstateSize @22
    <%fileNamePrefix%>_fmiSerializeFMUstate @23
    <%fileNamePrefix%>_fmiDeSerializeFMUstate @24
    <%fileNamePrefix%>_fmiGetDirectionalDerivative @25
    ;***************************************************
    ;Functions for FMI for Model Exchange
    ;****************************************************
    <%fileNamePrefix%>_fmiEnterEventMode @26
    <%fileNamePrefix%>_fmiNewDiscreteStates @27
    <%fileNamePrefix%>_fmiEnterContinuousTimeMode @28
    <%fileNamePrefix%>_fmiCompletedIntegratorStep @29
    <%fileNamePrefix%>_fmiSetTime @30
    <%fileNamePrefix%>_fmiSetContinuousStates @31
    <%fileNamePrefix%>_fmiGetDerivatives @32
    <%fileNamePrefix%>_fmiGetEventIndicators @33
    <%fileNamePrefix%>_fmiGetContinuousStates @34
    <%fileNamePrefix%>_fmiGetNominalsOfContinuousStates @35
  >>
  else
  <<
  EXPORTS
    <%fileNamePrefix%>_fmiCompletedIntegratorStep @1
    <%fileNamePrefix%>_fmiEventUpdate @2
    <%fileNamePrefix%>_fmiFreeModelInstance @3
    <%fileNamePrefix%>_fmiGetBoolean @4
    <%fileNamePrefix%>_fmiGetContinuousStates @5
    <%fileNamePrefix%>_fmiGetDerivatives @6
    <%fileNamePrefix%>_fmiGetEventIndicators @7
    <%fileNamePrefix%>_fmiGetInteger @8
    <%fileNamePrefix%>_fmiGetModelTypesPlatform @9
    <%fileNamePrefix%>_fmiGetNominalContinuousStates @10
    <%fileNamePrefix%>_fmiGetReal @11
    <%fileNamePrefix%>_fmiGetStateValueReferences @12
    <%fileNamePrefix%>_fmiGetString @13
    <%fileNamePrefix%>_fmiGetVersion @14
    <%fileNamePrefix%>_fmiInitialize @15
    <%fileNamePrefix%>_fmiInstantiateModel @16
    <%fileNamePrefix%>_fmiSetBoolean @17
    <%fileNamePrefix%>_fmiSetContinuousStates @18
    <%fileNamePrefix%>_fmiSetDebugLogging @19
    <%fileNamePrefix%>_fmiSetExternalFunction @20
    <%fileNamePrefix%>_fmiSetInteger @21
    <%fileNamePrefix%>_fmiSetReal @22
    <%fileNamePrefix%>_fmiSetString @23
    <%fileNamePrefix%>_fmiSetTime @24
    <%fileNamePrefix%>_fmiTerminate @25
  >>
end fmudeffile;

template importFMUModelica(FmiImport fmi)
 "Generates the Modelica code depending on the FMU type."
::=
match fmi
case FMIIMPORT(__) then
  match fmiInfo
    case (INFO(fmiVersion = "1.0", fmiType = 0)) then
      importFMU1ModelExchange(fmi)
    case (INFO(fmiVersion = "1.0", fmiType = 1)) then
      importFMU1CoSimulationStandAlone(fmi)
    case (INFO(fmiVersion = "2.0", fmiType = 1)) then
      importFMU2ModelExchange(fmi)
end importFMUModelica;

template importFMU1ModelExchange(FmiImport fmi)
 "Generates Modelica code for FMI Model Exchange version 1.0"
::=
match fmi
case FMIIMPORT(fmiInfo=INFO(__),fmiExperimentAnnotation=EXPERIMENTANNOTATION(__)) then
  /* Get Real parameters and their value references */
  let realParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 1)
  let realParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 2)
  /* Get Integer parameters and their value references */
  let integerParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 1)
  let integerParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 2)
  /* Get Boolean parameters and their value references */
  let booleanParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 1)
  let booleanParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 2)
  /* Get String parameters and their value references */
  let stringParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 1)
  let stringParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 2)
  /* Get dependent Real parameters and their value references */
  let realDependentParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 1)
  let realDependentParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 2)
  /* Get dependent Integer parameters and their value references */
  let integerDependentParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 1)
  let integerDependentParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 2)
  /* Get dependent Boolean parameters and their value references */
  let booleanDependentParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 1)
  let booleanDependentParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 2)
  /* Get dependent String parameters and their value references */
  let stringDependentParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 1)
  let stringDependentParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 2)
  /* Get input Real varibales and their value references */
  let realInputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "input", false, 1)
  let realInputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 2)
  let realInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 3)
  /* Get input Integer varibales and their value references */
  let integerInputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "input", false, 1)
  let integerInputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 2)
  let integerInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 3)
  /* Get input Boolean varibales and their value references */
  let booleanInputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 1)
  let booleanInputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 2)
  let booleanInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 3)
  /* Get input String varibales and their value references */
  let stringInputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "input", false, 1)
  let stringStartVariablesNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 2)
  let stringInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 3)
  /* Get output Real varibales and their value references */
  let realOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "output", false, 1)
  let realOutputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "output", false, 2)
  /* Get output Integer varibales and their value references */
  let integerOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "output", false, 1)
  let integerOutputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "output", false, 2)
  /* Get output Boolean varibales and their value references */
  let booleanOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 1)
  let booleanOutputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 2)
  /* Get output String varibales and their value references */
  let stringOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "output", false, 1)
  let stringOutputVariablesNames = dumpVariables(fmiModelVariablesList, "string", "output", false, 2)
  <<
  model <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU<%if stringEq(fmiInfo.fmiDescription, "") then "" else " \""+fmiInfo.fmiDescription+"\""%>
    <%dumpFMITypeDefinitions(fmiTypeDefinitionsList)%>
    constant String fmuWorkingDir = "<%fmuWorkingDirectory%>";
    parameter Integer logLevel = <%fmiLogLevel%> "log level used during the loading of FMU" annotation (Dialog(tab="FMI", group="Enable logging"));
    parameter Boolean debugLogging = <%fmiDebugOutput%> "enables the FMU simulation logging" annotation (Dialog(tab="FMI", group="Enable logging"));
    <%dumpFMIModelVariablesList(fmiModelVariablesList, fmiTypeDefinitionsList, generateInputConnectors, generateOutputConnectors)%>
  protected
    FMI1ModelExchange fmi1me = FMI1ModelExchange(logLevel, fmuWorkingDir, "<%fmiInfo.fmiModelIdentifier%>", debugLogging);
    constant Integer numberOfContinuousStates = <%listLength(fmiInfo.fmiNumberOfContinuousStates)%>;
    Real fmi_x[numberOfContinuousStates] "States";
    Real fmi_x_new[numberOfContinuousStates](each fixed = true) "New States";
    constant Integer numberOfEventIndicators = <%listLength(fmiInfo.fmiNumberOfEventIndicators)%>;
    Real fmi_z[numberOfEventIndicators] "Events Indicators";
    Boolean fmi_z_positive[numberOfEventIndicators](each fixed = true);
    parameter Real flowStartTime(fixed=false);
    Real flowTime;
    parameter Real flowInitialized(fixed=false);
    parameter Real flowParamsStart(fixed=false);
    parameter Real flowInitInputs(fixed=false);
    Real flowStatesInputs;
    <%if not stringEq(realInputVariablesVRs, "") then "Real "+realInputVariablesReturnNames+";"%>
    <%if not stringEq(integerInputVariablesVRs, "") then "Integer "+integerInputVariablesReturnNames+";"%>
    <%if not stringEq(booleanInputVariablesVRs, "") then "Boolean "+booleanInputVariablesReturnNames+";"%>
    <%if not stringEq(stringInputVariablesVRs, "") then "String "+stringInputVariablesReturnNames+";"%>
    Boolean callEventUpdate;
    constant Boolean intermediateResults = false;
    Boolean newStatesAvailable(fixed = true);
    Real triggerDSSEvent;
    Real nextEventTime;
  initial equation
    flowStartTime = fmi1Functions.fmi1SetTime(fmi1me, time, 1);
    flowInitialized = fmi1Functions.fmi1Initialize(fmi1me, flowParamsStart+flowInitInputs+flowStartTime);
    <%if intGt(listLength(fmiInfo.fmiNumberOfContinuousStates), 0) then
    <<
    fmi_x = fmi1Functions.fmi1GetContinuousStates(fmi1me, numberOfContinuousStates, flowParamsStart+flowInitialized);
    >>
    %>
  initial algorithm
    flowParamsStart := 1;
    <%if not stringEq(realParametersVRs, "") then "flowParamsStart := fmi1Functions.fmi1SetRealParameter(fmi1me, {"+realParametersVRs+"}, {"+realParametersNames+"});"%>
    <%if not stringEq(integerParametersVRs, "") then "flowParamsStart := fmi1Functions.fmi1SetIntegerParameter(fmi1me, {"+integerParametersVRs+"}, {"+integerParametersNames+"});"%>
    <%if not stringEq(booleanParametersVRs, "") then "flowParamsStart := fmi1Functions.fmi1SetBooleanParameter(fmi1me, {"+booleanParametersVRs+"}, {"+booleanParametersNames+"});"%>
    <%if not stringEq(stringParametersVRs, "") then "flowParamsStart := fmi1Functions.fmi1SetStringParameter(fmi1me, {"+stringParametersVRs+"}, {"+stringParametersNames+"});"%>
    flowInitInputs:=1;
  initial equation
    <%if not stringEq(realDependentParametersVRs, "") then "{"+realDependentParametersNames+"} = fmi1Functions.fmi1GetReal(fmi1me, {"+realDependentParametersVRs+"}, flowInitialized);"%>
    <%if not stringEq(integerDependentParametersVRs, "") then "{"+integerDependentParametersNames+"} = fmi1Functions.fmi1GetInteger(fmi1me, {"+integerDependentParametersVRs+"}, flowInitialized);"%>
    <%if not stringEq(booleanDependentParametersVRs, "") then "{"+booleanDependentParametersNames+"} = fmi1Functions.fmi1GetBoolean(fmi1me, {"+booleanDependentParametersVRs+"}, flowInitialized);"%>
    <%if not stringEq(stringDependentParametersVRs, "") then "{"+stringDependentParametersNames+"} = fmi1Functions.fmi1GetString(fmi1me, {"+stringDependentParametersVRs+"}, flowInitialized);"%>
  equation
    flowTime = fmi1Functions.fmi1SetTime(fmi1me, time, flowInitialized);
    <%if not stringEq(realInputVariablesVRs, "") then "{"+realInputVariablesReturnNames+"} = fmi1Functions.fmi1SetReal(fmi1me, {"+realInputVariablesVRs+"}, {"+realInputVariablesNames+"});"%>
    <%if not stringEq(integerInputVariablesVRs, "") then "{"+integerInputVariablesReturnNames+"} = fmi1Functions.fmi1SetInteger(fmi1me, {"+integerInputVariablesVRs+"}, {"+integerInputVariablesNames+"});"%>
    <%if not stringEq(booleanInputVariablesVRs, "") then "{"+booleanInputVariablesReturnNames+"} = fmi1Functions.fmi1SetBoolean(fmi1me, {"+booleanInputVariablesVRs+"}, {"+booleanInputVariablesNames+"});"%>
    <%if not stringEq(stringInputVariablesVRs, "") then "{"+stringInputVariablesReturnNames+"} = fmi1Functions.fmi1SetString(fmi1me, {"+stringInputVariablesVRs+"}, {"+stringStartVariablesNames+"});"%>
    flowStatesInputs = fmi1Functions.fmi1SetContinuousStates(fmi1me, fmi_x, flowParamsStart + flowTime);
    der(fmi_x) = fmi1Functions.fmi1GetDerivatives(fmi1me, numberOfContinuousStates, flowStatesInputs);
    fmi_z  = fmi1Functions.fmi1GetEventIndicators(fmi1me, numberOfEventIndicators, flowStatesInputs);
    for i in 1:size(fmi_z,1) loop
      fmi_z_positive[i] = if not terminal() then fmi_z[i] > 0 else pre(fmi_z_positive[i]);
    end for;
    callEventUpdate = fmi1Functions.fmi1CompletedIntegratorStep(fmi1me, flowStatesInputs);
    triggerDSSEvent = noEvent(if callEventUpdate then flowStatesInputs+1.0 else flowStatesInputs-1.0);
    nextEventTime = fmi1Functions.fmi1nextEventTime(fmi1me, flowStatesInputs);
    <%if not boolAnd(stringEq(realOutputVariablesNames, ""), stringEq(realOutputVariablesVRs, "")) then "{"+realOutputVariablesNames+"} = fmi1Functions.fmi1GetReal(fmi1me, {"+realOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(integerOutputVariablesNames, ""), stringEq(integerOutputVariablesVRs, "")) then "{"+integerOutputVariablesNames+"} = fmi1Functions.fmi1GetInteger(fmi1me, {"+integerOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(booleanOutputVariablesNames, ""), stringEq(booleanOutputVariablesVRs, "")) then "{"+booleanOutputVariablesNames+"} = fmi1Functions.fmi1GetBoolean(fmi1me, {"+booleanOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(stringOutputVariablesNames, ""), stringEq(stringOutputVariablesVRs, "")) then "{"+stringOutputVariablesNames+"} = fmi1Functions.fmi1GetString(fmi1me, {"+stringOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%dumpOutputGetEnumerationVariables(fmiModelVariablesList, fmiTypeDefinitionsList, "fmi1Functions.fmi1GetInteger", "fmi1me")%>
  algorithm
  <%if intGt(listLength(fmiInfo.fmiNumberOfEventIndicators), 0) then
  <<
    when {(<%fmiInfo.fmiNumberOfEventIndicators |> eventIndicator =>  "change(fmi_z_positive["+eventIndicator+"])" ;separator=" or "%>) and not initial(),triggerDSSEvent > flowStatesInputs, nextEventTime < time, terminal()} then
  >>
  else
  <<
    when {not initial(), triggerDSSEvent > flowStatesInputs, nextEventTime < time, terminal()} then
  >>
  %>
      newStatesAvailable := fmi1Functions.fmi1EventUpdate(fmi1me, intermediateResults);
  <%if intGt(listLength(fmiInfo.fmiNumberOfContinuousStates), 0) then
  <<
      if newStatesAvailable then
        fmi_x_new := fmi1Functions.fmi1GetContinuousStates(fmi1me, numberOfContinuousStates, flowStatesInputs);
        <%fmiInfo.fmiNumberOfContinuousStates |> continuousStates =>  "reinit(fmi_x["+continuousStates+"], fmi_x_new["+continuousStates+"]);" ;separator="\n"%>
      end if;
  >>
  %>
    end when;
    annotation(experiment(StartTime=<%fmiExperimentAnnotation.fmiExperimentStartTime%>, StopTime=<%fmiExperimentAnnotation.fmiExperimentStopTime%>, Tolerance=<%fmiExperimentAnnotation.fmiExperimentTolerance%>));
    annotation (Icon(graphics={
        Rectangle(
          extent={{-100,100},{100,-100}},
          lineColor={0,0,0},
          fillColor={240,240,240},
          fillPattern=FillPattern.Solid,
          lineThickness=0.5),
        Text(
          extent={{-100,40},{100,0}},
          lineColor={0,0,0},
          textString="%name"),
        Text(
          extent={{-100,-50},{100,-90}},
          lineColor={0,0,0},
          textString="V1.0")}));
  protected
    class FMI1ModelExchange
      extends ExternalObject;
        function constructor
          input Integer logLevel;
          input String workingDirectory;
          input String instanceName;
          input Boolean debugLogging;
          output FMI1ModelExchange fmi1me;
          external "C" fmi1me = FMI1ModelExchangeConstructor_OMC(logLevel, workingDirectory, instanceName, debugLogging) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end constructor;

        function destructor
          input FMI1ModelExchange fmi1me;
          external "C" FMI1ModelExchangeDestructor_OMC(fmi1me) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end destructor;
    end FMI1ModelExchange;

    <%dumpFMITypeDefinitionsMappingFunctions(fmiTypeDefinitionsList)%>

    <%dumpFMITypeDefinitionsArrayMappingFunctions(fmiTypeDefinitionsList)%>

    package fmi1Functions
      function fmi1Initialize
        input FMI1ModelExchange fmi1me;
        input Real preInitialized;
        output Real postInitialized=preInitialized;
        external "C" fmi1Initialize_OMC(fmi1me) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1Initialize;

      function fmi1SetTime
        input FMI1ModelExchange fmi1me;
        input Real inTime;
        input Real inFlow;
        output Real outFlow = inFlow;
        external "C" fmi1SetTime_OMC(fmi1me, inTime) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetTime;

      function fmi1GetContinuousStates
        input FMI1ModelExchange fmi1me;
        input Integer numberOfContinuousStates;
        input Real inFlowParams;
        output Real fmi_x[numberOfContinuousStates];
        external "C" fmi1GetContinuousStates_OMC(fmi1me, numberOfContinuousStates, inFlowParams, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetContinuousStates;

      function fmi1SetContinuousStates
        input FMI1ModelExchange fmi1me;
        input Real fmi_x[:];
        input Real inFlowParams;
        output Real outFlowStates;
        external "C" outFlowStates = fmi1SetContinuousStates_OMC(fmi1me, size(fmi_x, 1), inFlowParams, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetContinuousStates;

      function fmi1GetDerivatives
        input FMI1ModelExchange fmi1me;
        input Integer numberOfContinuousStates;
        input Real inFlowStates;
        output Real fmi_x[numberOfContinuousStates];
        external "C" fmi1GetDerivatives_OMC(fmi1me, numberOfContinuousStates, inFlowStates, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetDerivatives;

      function fmi1GetEventIndicators
        input FMI1ModelExchange fmi1me;
        input Integer numberOfEventIndicators;
        input Real inFlowStates;
        output Real fmi_z[numberOfEventIndicators];
        external "C" fmi1GetEventIndicators_OMC(fmi1me, numberOfEventIndicators, inFlowStates, fmi_z) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetEventIndicators;

      function fmi1GetReal
        input FMI1ModelExchange fmi1me;
        input Real realValuesReferences[:];
        input Real inFlowStatesInput;
        output Real realValues[size(realValuesReferences, 1)];
        external "C" fmi1GetReal_OMC(fmi1me, size(realValuesReferences, 1), realValuesReferences, inFlowStatesInput, realValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetReal;

      function fmi1SetReal
        input FMI1ModelExchange fmi1me;
        input Real realValueReferences[:];
        input Real realValues[size(realValueReferences, 1)];
        output Real outValues[size(realValueReferences, 1)] = realValues;
        external "C" fmi1SetReal_OMC(fmi1me, size(realValueReferences, 1), realValueReferences, realValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetReal;

      function fmi1SetRealParameter
        input FMI1ModelExchange fmi1me;
        input Real realValueReferences[:];
        input Real realValues[size(realValueReferences, 1)];
        output Real out_Value = 1;
        external "C" fmi1SetReal_OMC(fmi1me, size(realValueReferences, 1), realValueReferences, realValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetRealParameter;

      function fmi1GetInteger
        input FMI1ModelExchange fmi1me;
        input Real integerValueReferences[:];
        input Real inFlowStatesInput;
        output Integer integerValues[size(integerValueReferences, 1)];
        external "C" fmi1GetInteger_OMC(fmi1me, size(integerValueReferences, 1), integerValueReferences, inFlowStatesInput, integerValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetInteger;

      function fmi1SetInteger
        input FMI1ModelExchange fmi1me;
        input Real integerValuesReferences[:];
        input Integer integerValues[size(integerValuesReferences, 1)];
        output Integer outValues[size(integerValuesReferences, 1)] = integerValues;
        external "C" fmi1SetInteger_OMC(fmi1me, size(integerValuesReferences, 1), integerValuesReferences, integerValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetInteger;

      function fmi1SetIntegerParameter
        input FMI1ModelExchange fmi1me;
        input Real integerValuesReferences[:];
        input Integer integerValues[size(integerValuesReferences, 1)];
        output Real out_Value = 1;
        external "C" fmi1SetInteger_OMC(fmi1me, size(integerValuesReferences, 1), integerValuesReferences, integerValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetIntegerParameter;

      function fmi1GetBoolean
        input FMI1ModelExchange fmi1me;
        input Real booleanValuesReferences[:];
        input Real inFlowStatesInput;
        output Boolean booleanValues[size(booleanValuesReferences, 1)];
        external "C" fmi1GetBoolean_OMC(fmi1me, size(booleanValuesReferences, 1), booleanValuesReferences, inFlowStatesInput, booleanValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetBoolean;

      function fmi1SetBoolean
        input FMI1ModelExchange fmi1me;
        input Real booleanValueReferences[:];
        input Boolean booleanValues[size(booleanValueReferences, 1)];
        output Boolean outValues[size(booleanValueReferences, 1)] = booleanValues;
        external "C" fmi1SetBoolean_OMC(fmi1me, size(booleanValueReferences, 1), booleanValueReferences, booleanValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetBoolean;

      function fmi1SetBooleanParameter
        input FMI1ModelExchange fmi1me;
        input Real booleanValueReferences[:];
        input Boolean booleanValues[size(booleanValueReferences, 1)];
        output Real out_Value = 1;
        external "C" fmi1SetBoolean_OMC(fmi1me, size(booleanValueReferences, 1), booleanValueReferences, booleanValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetBooleanParameter;

      function fmi1GetString
        input FMI1ModelExchange fmi1me;
        input Real stringValuesReferences[:];
        input Real inFlowStatesInput;
        output String stringValues[size(stringValuesReferences, 1)];
        external "C" fmi1GetString_OMC(fmi1me, size(stringValuesReferences, 1), stringValuesReferences, inFlowStatesInput, stringValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetString;

      function fmi1SetString
        input FMI1ModelExchange fmi1me;
        input Real stringValueReferences[:];
        input String stringValues[size(stringValueReferences, 1)];
        output String outValues[size(stringValueReferences, 1)] = stringValues;
        external "C" fmi1SetString_OMC(fmi1me, size(stringValueReferences, 1), stringValueReferences, stringValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetString;

      function fmi1SetStringParameter
        input FMI1ModelExchange fmi1me;
        input Real stringValueReferences[:];
        input String stringValues[size(stringValueReferences, 1)];
        output Real out_Value = 1;
        external "C" fmi1SetString_OMC(fmi1me, size(stringValueReferences, 1), stringValueReferences, stringValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetStringParameter;

      function fmi1EventUpdate
        input FMI1ModelExchange fmi1me;
        input Boolean intermediateResults;
        output Boolean outNewStatesAvailable;
        external "C" outNewStatesAvailable = fmi1EventUpdate_OMC(fmi1me, intermediateResults) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1EventUpdate;

      function fmi1nextEventTime
        input FMI1ModelExchange fmi1me;
        input Real inFlowStates;
        output Real outNewnextTime;
        external "C" outNewnextTime = fmi1nextEventTime_OMC(fmi1me, inFlowStates) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1nextEventTime;

      function fmi1CompletedIntegratorStep
        input FMI1ModelExchange fmi1me;
        input Real inFlowStates;
        output Boolean outCallEventUpdate;
        external "C" outCallEventUpdate = fmi1CompletedIntegratorStep_OMC(fmi1me, inFlowStates) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1CompletedIntegratorStep;
    end fmi1Functions;
  end <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU;
  >>
end importFMU1ModelExchange;

template importFMU2ModelExchange(FmiImport fmi)
 "Generates Modelica code for FMI Model Exchange version 2.0"
::=
match fmi
case FMIIMPORT(fmiInfo=INFO(__),fmiExperimentAnnotation=EXPERIMENTANNOTATION(__)) then
  /* Get Real parameters and their value references */
  let realParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 1)
  let realParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 2)
  /* Get Integer parameters and their value references */
  let integerParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 1)
  let integerParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 2)
  /* Get Boolean parameters and their value references */
  let booleanParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 1)
  let booleanParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 2)
  /* Get String parameters and their value references */
  let stringParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 1)
  let stringParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 2)
  /* Get dependent Real parameters and their value references */
  let realDependentParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 1)
  let realDependentParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 2)
  /* Get dependent Integer parameters and their value references */
  let integerDependentParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 1)
  let integerDependentParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 2)
  /* Get dependent Boolean parameters and their value references */
  let booleanDependentParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 1)
  let booleanDependentParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 2)
  /* Get dependent String parameters and their value references */
  let stringDependentParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 1)
  let stringDependentParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 2)
  /* Get input Real varibales and their value references */
  let realInputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "input", false, 1)
  let realInputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 2)
  let realInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 3)
  /* Get input Integer varibales and their value references */
  let integerInputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "input", false, 1)
  let integerInputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 2)
  let integerInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 3)
  /* Get input Boolean varibales and their value references */
  let booleanInputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 1)
  let booleanInputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 2)
  let booleanInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 3)
  /* Get input String varibales and their value references */
  let stringInputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "input", false, 1)
  let stringStartVariablesNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 2)
  let stringInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 3)
  /* Get output Real varibales and their value references */
  let realOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "output", false, 1)
  let realOutputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "output", false, 2)
  /* Get output Integer varibales and their value references */
  let integerOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "output", false, 1)
  let integerOutputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "output", false, 2)
  /* Get output Boolean varibales and their value references */
  let booleanOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 1)
  let booleanOutputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 2)
  /* Get output String varibales and their value references */
  let stringOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "output", false, 1)
  let stringOutputVariablesNames = dumpVariables(fmiModelVariablesList, "string", "output", false, 2)
  <<
  model <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU<%if stringEq(fmiInfo.fmiDescription, "") then "" else " \""+fmiInfo.fmiDescription+"\""%>
    constant String fmuFile = "<%fmuFileName%>";
    constant String fmuWorkingDir = "<%fmuWorkingDirectory%>";
    parameter Integer logLevel = <%fmiLogLevel%> "log level used during the loading of FMU" annotation (Dialog(tab="FMI", group="Enable logging"));
    parameter Boolean debugLogging = <%fmiDebugOutput%> "enables the FMU simulation logging" annotation (Dialog(tab="FMI", group="Enable logging"));
    FMI2ModelExchange fmi2me;
    <%dumpFMIModelVariablesList(fmiModelVariablesList, fmiTypeDefinitionsList, generateInputConnectors, generateOutputConnectors)%>
    constant Integer numberOfContinuousStates = <%listLength(fmiInfo.fmiNumberOfContinuousStates)%>;
    Real fmi_x[numberOfContinuousStates] "States";
    Real fmi_x_new[numberOfContinuousStates](each fixed=true) "New States";
    constant Integer numberOfEventIndicators = <%listLength(fmiInfo.fmiNumberOfEventIndicators)%>;
    Real fmi_z[numberOfEventIndicators] "Events Indicators";
    Boolean fmi_z_positive[numberOfEventIndicators](each fixed=true);
    Real flowTime;
    parameter Real flowParamsStart(fixed=false);
    Real flowStatesInputs;
    Boolean callEventUpdate;
    Boolean newStatesAvailable(fixed=true);
    Real triggerDSSEvent;
    Real nextEventTime;
    Boolean initantiateOnce(start=true, fixed=false) "Variable to instantiate the model only once";
  algorithm
    when initial() then
      if initantiateOnce then
        initantiateOnce := false;
        fmi2me := FMI2ModelExchange(logLevel, fmuWorkingDir, "<%fmiInfo.fmiModelIdentifier%>", debugLogging);
      end if;
    end when;
    flowTime := fmi2Functions.fmi2SetTime(fmi2me, time);
  initial algorithm
    flowParamsStart := fmi2Functions.fmi2EnterInitialization(fmi2me, flowTime);
    <%if intGt(listLength(fmiInfo.fmiNumberOfContinuousStates), 0) then
    <<fmi_x := fmi2Functions.fmi2GetContinuousStates(fmi2me, numberOfContinuousStates, flowTime);>>
    %>
  algorithm
    when not initial() then
      fmi2Functions.fmi2Functions.fmi2ExitInitialization(fmi2me);
    end when;
    <%if intGt(listLength(fmiInfo.fmiNumberOfContinuousStates), 0) then
    <<flowStatesInputs := fmi2Functions.fmi2SetContinuousStates(fmi2me, fmi_x, flowParamsStart + flowTime);>>
    else
    <<flowStatesInputs :=  flowParamsStart + flowTime;>>
    %>
  equation
    der(fmi_x) = fmi2Functions.fmi2GetDerivatives(fmi2me, numberOfContinuousStates, flowStatesInputs);
    fmi_z  = fmi2Functions.fmi2GetEventIndicators(fmi2me, numberOfEventIndicators, flowStatesInputs);
    for i in 1:size(fmi_z,1) loop
      fmi_z_positive[i] = if not terminal() then fmi_z[i] > 0 else pre(fmi_z_positive[i]);
    end for;

    triggerDSSEvent = noEvent(if callEventUpdate then flowStatesInputs+1.0 else flowStatesInputs-1.0);

  equation
    <%if not boolAnd(stringEq(realOutputVariablesNames, ""), stringEq(realOutputVariablesVRs, "")) then "{"+realOutputVariablesNames+"} = fmi2Functions.fmi2GetReal(fmi2me, {"+realOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(integerOutputVariablesNames, ""), stringEq(integerOutputVariablesVRs, "")) then "{"+integerOutputVariablesNames+"} = fmi2Functions.fmi2GetInteger(fmi2me, {"+integerOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(booleanOutputVariablesNames, ""), stringEq(booleanOutputVariablesVRs, "")) then "{"+booleanOutputVariablesNames+"} = fmi2Functions.fmi2GetBoolean(fmi2me, {"+booleanOutputVariablesVRs+"}, flowStatesInputs);"%>
    <%if not boolAnd(stringEq(stringOutputVariablesNames, ""), stringEq(stringOutputVariablesVRs, "")) then "{"+stringOutputVariablesNames+"} = fmi2Functions.fmi2GetString(fmi2me, {"+stringOutputVariablesVRs+"}, flowStatesInputs);"%>
   callEventUpdate = fmi2Functions.fmi2CompletedIntegratorStep(fmi2me, flowStatesInputs + flowTime);
  algorithm
  <%if intGt(listLength(fmiInfo.fmiNumberOfEventIndicators), 0) then
  <<
    when {(<%fmiInfo.fmiNumberOfEventIndicators |> eventIndicator =>  "change(fmi_z_positive["+eventIndicator+"])" ;separator=" or "%>) and not initial(),triggerDSSEvent > flowStatesInputs, pre(nextEventTime) < time, terminal()} then
  >>
  else
  <<
    when {not initial(), triggerDSSEvent > flowStatesInputs, pre(nextEventTime) < time, terminal()} then
  >>
  %>
      (newStatesAvailable) := fmi2Functions.fmi2EventUpdate(fmi2me, flowStatesInputs);
      nextEventTime := fmi2Functions.fmi2nextEventTime(fmi2me, flowStatesInputs);
  <%if intGt(listLength(fmiInfo.fmiNumberOfContinuousStates), 0) then
  <<
      if newStatesAvailable then
        fmi_x_new := fmi2Functions.fmi2GetContinuousStates(fmi2me, numberOfContinuousStates, flowStatesInputs);
        <%fmiInfo.fmiNumberOfContinuousStates |> continuousStates =>  "reinit(fmi_x["+continuousStates+"], fmi_x_new["+continuousStates+"]);" ;separator="\n"%>
      end if;
  >>
  %>
    end when;
    annotation(experiment(StartTime=<%fmiExperimentAnnotation.fmiExperimentStartTime%>, StopTime=<%fmiExperimentAnnotation.fmiExperimentStopTime%>, Tolerance=<%fmiExperimentAnnotation.fmiExperimentTolerance%>));
    annotation (Icon(graphics={
        Rectangle(
          extent={{-100,100},{100,-100}},
          lineColor={0,0,0},
          fillColor={240,240,240},
          fillPattern=FillPattern.Solid,
          lineThickness=0.5),
        Text(
          extent={{-100,40},{100,0}},
          lineColor={0,0,0},
          textString="%name"),
        Text(
          extent={{-100,-50},{100,-90}},
          lineColor={0,0,0},
          textString="V2.0")}));
  protected
    class FMI2ModelExchange
      extends ExternalObject;
        function constructor
          input Integer logLevel;
          input String workingDirectory;
          input String instanceName;
          input Boolean debugLogging;
          output FMI2ModelExchange fmi2me;
          external "C" fmi2me = FMI2ModelExchangeConstructor_OMC(logLevel, workingDirectory, instanceName, debugLogging) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end constructor;

        function destructor
          input FMI2ModelExchange fmi2me;
          external "C" FMI2ModelExchangeDestructor_OMC(fmi2me) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end destructor;
    end FMI2ModelExchange;

    package fmi2Functions
      function fmi2SetTime
        input FMI2ModelExchange fmi2me;
        input Real inTime;
        output Real status;
        external "C" status = fmi2SetTime_OMC(fmi2me, inTime) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetTime;

      function fmi2EnterInitialization
        input FMI2ModelExchange fmi2me;
        input Real inFlowVariable;
        output Real outFlowVariable = inFlowVariable;
        external "C" fmi2EnterInitializationModel_OMC(fmi2me) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2EnterInitialization;

      function fmi2ExitInitialization
        input FMI2ModelExchange fmi2me;
        external "C" fmi2ExitInitializationModel_OMC(fmi2me) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2ExitInitialization;

      function fmi2GetContinuousStates
        input FMI2ModelExchange fmi2me;
        input Integer numberOfContinuousStates;
        input Real inFlowParams;
        output Real fmi_x[numberOfContinuousStates];
        external "C" fmi2GetContinuousStates_OMC(fmi2me, numberOfContinuousStates, inFlowParams, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetContinuousStates;

      function fmi2SetContinuousStates
        input FMI2ModelExchange fmi2me;
        input Real fmi_x[:];
        input Real inFlowParams;
        output Real outFlowStates;
        external "C" outFlowStates = fmi2SetContinuousStates_OMC(fmi2me, size(fmi_x, 1), inFlowParams, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetContinuousStates;

      function fmi2GetDerivatives
        input FMI2ModelExchange fmi2me;
        input Integer numberOfContinuousStates;
        input Real inFlowStates;
        output Real fmi_x[numberOfContinuousStates];
        external "C" fmi2GetDerivatives_OMC(fmi2me, numberOfContinuousStates, inFlowStates, fmi_x) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetDerivatives;

      function fmi2GetEventIndicators
        input FMI2ModelExchange fmi2me;
        input Integer numberOfEventIndicators;
        input Real inFlowStates;
        output Real fmi_z[numberOfEventIndicators];
        external "C" fmi2GetEventIndicators_OMC(fmi2me, numberOfEventIndicators, inFlowStates, fmi_z) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetEventIndicators;

      function fmi2GetReal
        input FMI2ModelExchange fmi2me;
        input Real realValuesReferences[:];
        input Real inFlowStatesInput;
        output Real realValues[size(realValuesReferences, 1)];
        external "C" fmi2GetReal_OMC(fmi2me, size(realValuesReferences, 1), realValuesReferences, inFlowStatesInput, realValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetReal;

      function fmi2SetReal
        input FMI2ModelExchange fmi2me;
        input Real realValuesReferences[:];
        input Real realValues[size(realValuesReferences, 1)];
        external "C" fmi2SetReal_OMC(fmi2me, size(realValuesReferences, 1), realValuesReferences, realValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetReal;

      function fmi2GetInteger
        input FMI2ModelExchange fmi2me;
        input Real integerValuesReferences[:];
        input Real inFlowStatesInput;
        output Integer integerValues[size(integerValuesReferences, 1)];
        external "C" fmi2GetInteger_OMC(fmi2me, size(integerValuesReferences, 1), integerValuesReferences, inFlowStatesInput, integerValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetInteger;

      function fmi2SetInteger
        input FMI2ModelExchange fmi2me;
        input Real integerValuesReferences[:];
        input Integer integerValues[size(integerValuesReferences, 1)];
        external "C" fmi2SetInteger_OMC(fmi2me, size(integerValuesReferences, 1), integerValuesReferences, integerValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetInteger;

      function fmi2GetBoolean
        input FMI2ModelExchange fmi2me;
        input Real booleanValuesReferences[:];
        input Real inFlowStatesInput;
        output Boolean booleanValues[size(booleanValuesReferences, 1)];
        external "C" fmi2GetBoolean_OMC(fmi2me, size(booleanValuesReferences, 1), booleanValuesReferences, inFlowStatesInput, booleanValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetBoolean;

      function fmi2SetBoolean
        input FMI2ModelExchange fmi2me;
        input Real booleanValuesReferences[:];
        input Boolean booleanValues[size(booleanValuesReferences, 1)];
        external "C" fmi2SetBoolean_OMC(fmi2me, size(booleanValuesReferences, 1), booleanValuesReferences, booleanValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetBoolean;

      function fmi2GetString
        input FMI2ModelExchange fmi2me;
        input Real stringValuesReferences[:];
        input Real inFlowStatesInput;
        output String stringValues[size(stringValuesReferences, 1)];
        external "C" fmi2GetString_OMC(fmi2me, size(stringValuesReferences, 1), stringValuesReferences, inFlowStatesInput, stringValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2GetString;

      function fmi2SetString
        input FMI2ModelExchange fmi2me;
        input Real stringValuesReferences[:];
        input String stringValues[size(stringValuesReferences, 1)];
        external "C" fmi2SetString_OMC(fmi2me, size(stringValuesReferences, 1), stringValuesReferences, stringValues, 1) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2SetString;

      function fmi2EventUpdate
        input FMI2ModelExchange fmi2me;
        input Real inFlowStates;
        output Boolean outNewStatesAvailable;
        external "C" outNewStatesAvailable = fmi2EventUpdate_OMC(fmi2me, inFlowStates) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2EventUpdate;

      function fmi2nextEventTime
        input FMI2ModelExchange fmi2me;
        input Real inFlowStates;
        output Real outNewnextTime;
        external "C" outNewnextTime = fmi2nextEventTime_OMC(fmi2me, inFlowStates) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2nextEventTime;

      function fmi2CompletedIntegratorStep
        input FMI2ModelExchange fmi2me;
        input Real inFlowStates;
        output Boolean outCallEventUpdate;
        external "C" outCallEventUpdate = fmi2CompletedIntegratorStep_OMC(fmi2me, inFlowStates) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi2CompletedIntegratorStep;
    end fmi2Functions;
  end <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU;
  >>
end importFMU2ModelExchange;

template importFMU1CoSimulationStandAlone(FmiImport fmi)
 "Generates Modelica code for FMI Co-simulation stand alone version 1.0"
::=
match fmi
case FMIIMPORT(fmiInfo=INFO(__),fmiExperimentAnnotation=EXPERIMENTANNOTATION(__)) then
  /* Get Real parameters and their value references */
  let realParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 1)
  let realParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", false, 2)
  /* Get Integer parameters and their value references */
  let integerParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 1)
  let integerParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", false, 2)
  /* Get Boolean parameters and their value references */
  let booleanParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 1)
  let booleanParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", false, 2)
  /* Get String parameters and their value references */
  let stringParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 1)
  let stringParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", false, 2)
  /* Get dependent Real parameters and their value references */
  let realDependentParametersVRs = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 1)
  let realDependentParametersNames = dumpVariables(fmiModelVariablesList, "real", "parameter", true, 2)
  /* Get dependent Integer parameters and their value references */
  let integerDependentParametersVRs = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 1)
  let integerDependentParametersNames = dumpVariables(fmiModelVariablesList, "integer", "parameter", true, 2)
  /* Get dependent Boolean parameters and their value references */
  let booleanDependentParametersVRs = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 1)
  let booleanDependentParametersNames = dumpVariables(fmiModelVariablesList, "boolean", "parameter", true, 2)
  /* Get dependent String parameters and their value references */
  let stringDependentParametersVRs = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 1)
  let stringDependentParametersNames = dumpVariables(fmiModelVariablesList, "string", "parameter", true, 2)
  /* Get input Real varibales and their value references */
  let realInputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "input", false, 1)
  let realInputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 2)
  let realInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "real", "input", false, 3)
  /* Get input Integer varibales and their value references */
  let integerInputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "input", false, 1)
  let integerInputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 2)
  let integerInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "integer", "input", false, 3)
  /* Get input Boolean varibales and their value references */
  let booleanInputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 1)
  let booleanInputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 2)
  let booleanInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "boolean", "input", false, 3)
  /* Get input String varibales and their value references */
  let stringInputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "input", false, 1)
  let stringStartVariablesNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 2)
  let stringInputVariablesReturnNames = dumpVariables(fmiModelVariablesList, "string", "input", false, 3)
  /* Get output Real varibales and their value references */
  let realOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "real", "output", false, 1)
  let realOutputVariablesNames = dumpVariables(fmiModelVariablesList, "real", "output", false, 2)
  /* Get output Integer varibales and their value references */
  let integerOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "integer", "output", false, 1)
  let integerOutputVariablesNames = dumpVariables(fmiModelVariablesList, "integer", "output", false, 2)
  /* Get output Boolean varibales and their value references */
  let booleanOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 1)
  let booleanOutputVariablesNames = dumpVariables(fmiModelVariablesList, "boolean", "output", false, 2)
  /* Get output String varibales and their value references */
  let stringOutputVariablesVRs = dumpVariables(fmiModelVariablesList, "string", "output", false, 1)
  let stringOutputVariablesNames = dumpVariables(fmiModelVariablesList, "string", "output", false, 2)
  <<
  model <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU<%if stringEq(fmiInfo.fmiDescription, "") then "" else " \""+fmiInfo.fmiDescription+"\""%>
    <%dumpFMITypeDefinitions(fmiTypeDefinitionsList)%>
    constant String fmuLocation = "file://<%fmuWorkingDirectory%>/resources";
    constant String fmuWorkingDir = "<%fmuWorkingDirectory%>";
    parameter Integer logLevel = <%fmiLogLevel%> "log level used during the loading of FMU" annotation (Dialog(tab="FMI", group="Enable logging"));
    parameter Boolean debugLogging = <%fmiDebugOutput%> "enables the FMU simulation logging" annotation (Dialog(tab="FMI", group="Enable logging"));
    constant String mimeType = "";
    constant Real timeout = 0.0;
    constant Boolean visible = false;
    constant Boolean interactive = false;
    parameter Real startTime = <%fmiExperimentAnnotation.fmiExperimentStartTime%> "start time used to initialize the slave" annotation (Dialog(tab="FMI", group="Step time"));
    parameter Real stopTime = <%fmiExperimentAnnotation.fmiExperimentStopTime%> "stop time used to initialize the slave" annotation (Dialog(tab="FMI", group="Step time"));
    parameter Real numberOfSteps = 500 annotation (Dialog(tab="FMI", group="Step time"));
    parameter Real communicationStepSize = (stopTime-startTime)/numberOfSteps "step size used by fmiDoStep" annotation (Dialog(tab="FMI", group="Step time"));
    constant Boolean stopTimeDefined = true;
    <%dumpFMIModelVariablesList(fmiModelVariablesList, fmiTypeDefinitionsList, generateInputConnectors, generateOutputConnectors)%>
  protected
    FMI1CoSimulation fmi1cs = FMI1CoSimulation(logLevel, fmuWorkingDir, "<%fmiInfo.fmiModelIdentifier%>", debugLogging, fmuLocation, mimeType, timeout, visible, interactive, startTime, stopTimeDefined, stopTime);
    parameter Real flowInitialized(fixed=false);
    Real flowStep;
    <%if not stringEq(realInputVariablesVRs, "") then "Real "+realInputVariablesReturnNames+";"%>
    <%if not stringEq(integerInputVariablesVRs, "") then "Integer "+integerInputVariablesReturnNames+";"%>
    <%if not stringEq(booleanInputVariablesVRs, "") then "Boolean "+booleanInputVariablesReturnNames+";"%>
    <%if not stringEq(stringInputVariablesVRs, "") then "String "+stringInputVariablesReturnNames+";"%>
  initial equation
    flowInitialized = fmi1Functions.fmi1InitializeSlave(fmi1cs, 1);
  equation
    <%if not boolAnd(stringEq(realOutputVariablesNames, ""), stringEq(realOutputVariablesVRs, "")) then "{"+realOutputVariablesNames+"} = fmi1Functions.fmi1GetReal(fmi1cs, {"+realOutputVariablesVRs+"}, flowInitialized);"%>
    <%if not boolAnd(stringEq(integerOutputVariablesNames, ""), stringEq(integerOutputVariablesVRs, "")) then "{"+integerOutputVariablesNames+"} = fmi1Functions.fmi1GetInteger(fmi1cs, {"+integerOutputVariablesVRs+"}, flowInitialized);"%>
    <%if not boolAnd(stringEq(booleanOutputVariablesNames, ""), stringEq(booleanOutputVariablesVRs, "")) then "{"+booleanOutputVariablesNames+"} = fmi1Functions.fmi1GetBoolean(fmi1cs, {"+booleanOutputVariablesVRs+"}, flowInitialized);"%>
    <%if not boolAnd(stringEq(stringOutputVariablesNames, ""), stringEq(stringOutputVariablesVRs, "")) then "{"+stringOutputVariablesNames+"} = fmi1Functions.fmi1GetString(fmi1cs, {"+stringOutputVariablesVRs+"}, flowInitialized);"%>
    <%if not stringEq(realInputVariablesVRs, "") then "{"+realInputVariablesReturnNames+"} = fmi1Functions.fmi1SetReal(fmi1cs, {"+realInputVariablesVRs+"}, {"+realInputVariablesNames+"});"%>
    <%if not stringEq(integerInputVariablesVRs, "") then "{"+integerInputVariablesReturnNames+"} = fmi1Functions.fmi1SetInteger(fmi1cs, {"+integerInputVariablesVRs+"}, {"+integerInputVariablesNames+"});"%>
    <%if not stringEq(booleanInputVariablesVRs, "") then "{"+booleanInputVariablesReturnNames+"} = fmi1Functions.fmi1SetBoolean(fmi1cs, {"+booleanInputVariablesVRs+"}, {"+booleanInputVariablesNames+"});"%>
    <%if not stringEq(stringInputVariablesVRs, "") then "{"+stringInputVariablesReturnNames+"} = fmi1Functions.fmi1SetString(fmi1cs, {"+stringInputVariablesVRs+"}, {"+stringStartVariablesNames+"});"%>
    flowStep = fmi1Functions.fmi1DoStep(fmi1cs, time, communicationStepSize, true, flowInitialized);
    annotation(experiment(StartTime=<%fmiExperimentAnnotation.fmiExperimentStartTime%>, StopTime=<%fmiExperimentAnnotation.fmiExperimentStopTime%>, Tolerance=<%fmiExperimentAnnotation.fmiExperimentTolerance%>));
    annotation (Icon(graphics={
        Rectangle(
          extent={{-100,100},{100,-100}},
          lineColor={0,0,0},
          fillColor={240,240,240},
          fillPattern=FillPattern.Solid,
          lineThickness=0.5),
        Text(
          extent={{-100,40},{100,0}},
          lineColor={0,0,0},
          textString="%name"),
        Text(
          extent={{-100,-50},{100,-90}},
          lineColor={0,0,0},
          textString="V1.0")}));
  protected
    class FMI1CoSimulation
      extends ExternalObject;
        function constructor
          input Integer fmiLogLevel;
          input String workingDirectory;
          input String instanceName;
          input Boolean debugLogging;
          input String fmuLocation;
          input String mimeType;
          input Real timeOut;
          input Boolean visible;
          input Boolean interactive;
          input Real tStart;
          input Boolean stopTimeDefined;
          input Real tStop;
          output FMI1CoSimulation fmi1cs;
          external "C" fmi1cs = FMI1CoSimulationConstructor_OMC(fmiLogLevel, workingDirectory, instanceName, debugLogging, fmuLocation, mimeType, timeOut, visible, interactive, tStart, stopTimeDefined, tStop) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end constructor;

        function destructor
          input FMI1CoSimulation fmi1cs;
          external "C" FMI1CoSimulationDestructor_OMC(fmi1cs) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
        end destructor;
    end FMI1CoSimulation;

    <%dumpFMITypeDefinitionsMappingFunctions(fmiTypeDefinitionsList)%>

    <%dumpFMITypeDefinitionsArrayMappingFunctions(fmiTypeDefinitionsList)%>

    package fmi1Functions
      function fmi1InitializeSlave
        input FMI1CoSimulation fmi1cs;
        input Real preInitialized;
        output Real postInitialized=preInitialized;
        external "C" fmi1InitializeSlave_OMC(fmi1cs) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1InitializeSlave;

      function fmi1DoStep
        input FMI1CoSimulation fmi1cs;
        input Real currentCommunicationPoint;
        input Real communicationStepSize;
        input Boolean newStep;
        input Real preInitialized;
        output Real postInitialized=preInitialized;
        external "C" fmi1DoStep_OMC(fmi1cs, currentCommunicationPoint, communicationStepSize, newStep) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1DoStep;

      function fmi1GetReal
        input FMI1CoSimulation fmi1cs;
        input Real realValuesReferences[:];
        input Real inFlowStatesInput;
        output Real realValues[size(realValuesReferences, 1)];
        external "C" fmi1GetReal_OMC(fmi1cs, size(realValuesReferences, 1), realValuesReferences, inFlowStatesInput, realValues, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetReal;

      function fmi1SetReal
        input FMI1CoSimulation fmi1cs;
        input Real realValuesReferences[:];
        input Real realValues[size(realValuesReferences, 1)];
        output Real out_Values[size(realValuesReferences, 1)];
        external "C" fmi1SetReal_OMC(fmi1cs, size(realValuesReferences, 1), realValuesReferences, realValues, out_Values, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetReal;

      function fmi1GetInteger
        input FMI1CoSimulation fmi1cs;
        input Real integerValuesReferences[:];
        input Real inFlowStatesInput;
        output Integer integerValues[size(integerValuesReferences, 1)];
        external "C" fmi1GetInteger_OMC(fmi1cs, size(integerValuesReferences, 1), integerValuesReferences, inFlowStatesInput, integerValues, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetInteger;

      function fmi1SetInteger
        input FMI1CoSimulation fmi1cs;
        input Real integerValuesReferences[:];
        input Integer integerValues[size(integerValuesReferences, 1)];
        output Real out_Values[size(integerValuesReferences, 1)];
        external "C" fmi1SetInteger_OMC(fmi1cs, size(integerValuesReferences, 1), integerValuesReferences, integerValues, out_Values, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetInteger;

      function fmi1GetBoolean
        input FMI1CoSimulation fmi1cs;
        input Real booleanValuesReferences[:];
        input Real inFlowStatesInput;
        output Boolean booleanValues[size(booleanValuesReferences, 1)];
        external "C" fmi1GetBoolean_OMC(fmi1cs, size(booleanValuesReferences, 1), booleanValuesReferences, inFlowStatesInput, booleanValues, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetBoolean;

      function fmi1SetBoolean
        input FMI1CoSimulation fmi1cs;
        input Real booleanValuesReferences[:];
        input Boolean booleanValues[size(booleanValuesReferences, 1)];
        output Boolean out_Values[size(booleanValuesReferences, 1)];
        external "C" fmi1SetBoolean_OMC(fmi1cs, size(booleanValuesReferences, 1), booleanValuesReferences, booleanValues, out_Values, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetBoolean;

      function fmi1GetString
        input FMI1CoSimulation fmi1cs;
        input Real stringValuesReferences[:];
        input Real inFlowStatesInput;
        output String stringValues[size(stringValuesReferences, 1)];
        external "C" fmi1GetString_OMC(fmi1cs, size(stringValuesReferences, 1), stringValuesReferences, inFlowStatesInput, stringValues, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1GetString;

      function fmi1SetString
        input FMI1CoSimulation fmi1cs;
        input Real stringValuesReferences[:];
        input String stringValues[size(stringValuesReferences, 1)];
        output String out_Values[size(stringValuesReferences, 1)];
        external "C" fmi1SetString_OMC(fmi1cs, size(stringValuesReferences, 1), stringValuesReferences, stringValues, out_Values, 2) annotation(Library = {"OpenModelicaFMIRuntimeC", "fmilib"<%if stringEq(platform, "win32") then ", \"shlwapi\""%>});
      end fmi1SetString;
    end fmi1Functions;
  end <%fmiInfo.fmiModelIdentifier%>_<%getFMIType(fmiInfo)%>_FMU;
  >>
end importFMU1CoSimulationStandAlone;

template dumpFMITypeDefinitions(list<TypeDefinitions> fmiTypeDefinitionsList)
 "Generates the Type Definitions code."
::=
  <<
  <%fmiTypeDefinitionsList |> fmiTypeDefinition => dumpFMITypeDefinition(fmiTypeDefinition) ;separator="\n"%>
  >>
end dumpFMITypeDefinitions;

template dumpFMITypeDefinition(TypeDefinitions fmiTypeDefinition)
 "Generates the Type code."
::=
match fmiTypeDefinition
case ENUMERATIONTYPE(__) then
  <<
  type <%name%> = enumeration(
    <%dumpFMITypeDefinitionsItems(items)%>);
  >>
end dumpFMITypeDefinition;

template dumpFMITypeDefinitionsItems(list<EnumerationItem> items)
 "Generates the Enumeration Type items code."
::=
  <<
  <%items |> item => dumpFMITypeDefinitionsItem(item) ;separator=",\n"%>
  >>
end dumpFMITypeDefinitionsItems;

template dumpFMITypeDefinitionsItem(EnumerationItem item)
 "Generates the Enumeration Type item name."
::=
match item
case ENUMERATIONITEM(__) then
  <<
  <%name%>
  >>
end dumpFMITypeDefinitionsItem;

template dumpFMITypeDefinitionsMappingFunctions(list<TypeDefinitions> fmiTypeDefinitionsList)
 "Generates the mapping functions for all enumeration types."
::=
  <<
  <%fmiTypeDefinitionsList |> fmiTypeDefinition => dumpFMITypeDefinitionMappingFunction(fmiTypeDefinition) ;separator="\n"%>
  >>
end dumpFMITypeDefinitionsMappingFunctions;

template dumpFMITypeDefinitionMappingFunction(TypeDefinitions fmiTypeDefinition)
 "Generates the mapping function from integer to enumeration type."
::=
match fmiTypeDefinition
case ENUMERATIONTYPE(__) then
  <<
  function map_<%name%>_from_integer
    input Integer i;
    output <%name%> outType;
  algorithm
    <%items |> item hasindex i0 fromindex 1 => dumpFMITypeDefinitionMappingFunctionItems(item, name, i0) ;separator="\n"%>
    <%if intGt(listLength(items), 1) then "end if;"%>
  end map_<%name%>_from_integer;
  >>
end dumpFMITypeDefinitionMappingFunction;

template dumpFMITypeDefinitionMappingFunctionItems(EnumerationItem item, String typeName, Integer i)
 "Dumps the mapping function conditions. This is closely related to dumpFMITypeDefinitionMappingFunction."
::=
match item
case ENUMERATIONITEM(__) then
  if intEq(i, 1) then
  <<
  if i == <%i%> then outType := <%typeName%>.<%name%>;
  >>
  else
  <<
  elseif i == <%i%> then outType := <%typeName%>.<%name%>;
  >>
end dumpFMITypeDefinitionMappingFunctionItems;

template dumpFMITypeDefinitionsArrayMappingFunctions(list<TypeDefinitions> fmiTypeDefinitionsList)
 "Generates the array mapping functions for all enumeration types."
::=
  <<
  <%fmiTypeDefinitionsList |> fmiTypeDefinition => dumpFMITypeDefinitionsArrayMappingFunction(fmiTypeDefinition) ;separator="\n"%>
  >>
end dumpFMITypeDefinitionsArrayMappingFunctions;

template dumpFMITypeDefinitionsArrayMappingFunction(TypeDefinitions fmiTypeDefinition)
 "Generates the mapping function from integer to enumeration type."
::=
match fmiTypeDefinition
case ENUMERATIONTYPE(__) then
  <<
  function map_<%name%>_from_integers
    input Integer fromInt[size(fromInt, 1)];
    output <%name%> toEnum[size(fromInt, 1)];
  protected
    Integer n = size(fromInt, 1);
  algorithm
    for i in 1:n loop
      toEnum[i] := map_<%name%>_from_integer(fromInt[i]);
    end for;
  end map_<%name%>_from_integers;
  >>
end dumpFMITypeDefinitionsArrayMappingFunction;

template dumpFMIModelVariablesList(list<ModelVariables> fmiModelVariablesList, list<TypeDefinitions> fmiTypeDefinitionsList, Boolean generateInputConnectors, Boolean generateOutputConnectors)
 "Generates the Model Variables code."
::=
  <<
  <%fmiModelVariablesList |> fmiModelVariable => dumpFMIModelVariable(fmiModelVariable, fmiTypeDefinitionsList, generateInputConnectors, generateOutputConnectors) ;separator="\n"%>
  >>
end dumpFMIModelVariablesList;

template dumpFMIModelVariable(ModelVariables fmiModelVariable, list<TypeDefinitions> fmiTypeDefinitionsList, Boolean generateInputConnectors, Boolean generateOutputConnectors)
::=
match fmiModelVariable
case REALVARIABLE(__) then
  <<
  <%dumpFMIModelVariableVariability(variability)%><%dumpFMIModelVariableCausalityAndBaseType(causality, baseType, generateInputConnectors, generateOutputConnectors)%> <%name%><%dumpFMIRealModelVariableStartValue(variability, hasStartValue, startValue, isFixed)%><%dumpFMIModelVariableDescription(description)%><%dumpFMIModelVariablePlacementAnnotation(x1Placement, x2Placement, y1Placement, y2Placement, generateInputConnectors, generateOutputConnectors, causality)%>;
  >>
case INTEGERVARIABLE(__) then
  <<
  <%dumpFMIModelVariableVariability(variability)%><%dumpFMIModelVariableCausalityAndBaseType(causality, baseType, generateInputConnectors, generateOutputConnectors)%> <%name%><%dumpFMIIntegerModelVariableStartValue(variability, hasStartValue, startValue, isFixed)%><%dumpFMIModelVariableDescription(description)%><%dumpFMIModelVariablePlacementAnnotation(x1Placement, x2Placement, y1Placement, y2Placement, generateInputConnectors, generateOutputConnectors, causality)%>;
  >>
case BOOLEANVARIABLE(__) then
  <<
  <%dumpFMIModelVariableVariability(variability)%><%dumpFMIModelVariableCausalityAndBaseType(causality, baseType, generateInputConnectors, generateOutputConnectors)%> <%name%><%dumpFMIBooleanModelVariableStartValue(variability, hasStartValue, startValue, isFixed)%><%dumpFMIModelVariableDescription(description)%><%dumpFMIModelVariablePlacementAnnotation(x1Placement, x2Placement, y1Placement, y2Placement, generateInputConnectors, generateOutputConnectors, causality)%>;
  >>
case STRINGVARIABLE(__) then
  <<
  <%dumpFMIModelVariableVariability(variability)%><%dumpFMIModelVariableCausalityAndBaseType(causality, baseType, generateInputConnectors, generateOutputConnectors)%> <%name%><%dumpFMIStringModelVariableStartValue(variability, hasStartValue, startValue, isFixed)%><%dumpFMIModelVariableDescription(description)%><%dumpFMIModelVariablePlacementAnnotation(x1Placement, x2Placement, y1Placement, y2Placement, generateInputConnectors, generateOutputConnectors, causality)%>;
  >>
case ENUMERATIONVARIABLE(__) then
  <<
  <%dumpFMIModelVariableVariability(variability)%><%dumpFMIModelVariableCausalityAndBaseType(causality, baseType, generateInputConnectors, generateOutputConnectors)%> <%name%><%dumpFMIEnumerationModelVariableStartValue(fmiTypeDefinitionsList, baseType, hasStartValue, startValue, isFixed)%><%dumpFMIModelVariableDescription(description)%><%dumpFMIModelVariablePlacementAnnotation(x1Placement, x2Placement, y1Placement, y2Placement, generateInputConnectors, generateOutputConnectors, causality)%>;
  >>
end dumpFMIModelVariable;

template dumpFMIModelVariableVariability(String variability)
::=
  <<
  <%if stringEq(variability, "") then "" else variability+" "%>
  >>
end dumpFMIModelVariableVariability;

template dumpFMIModelVariableCausalityAndBaseType(String causality, String baseType, Boolean generateInputConnectors, Boolean generateOutputConnectors)
::=
  if boolAnd(generateInputConnectors, boolAnd(stringEq(causality, "input"),stringEq(baseType, "Real"))) then "Modelica.Blocks.Interfaces.RealInput"
  else if boolAnd(generateInputConnectors, boolAnd(stringEq(causality, "input"),stringEq(baseType, "Integer"))) then "Modelica.Blocks.Interfaces.IntegerInput"
  else if boolAnd(generateInputConnectors, boolAnd(stringEq(causality, "input"),stringEq(baseType, "Boolean"))) then "Modelica.Blocks.Interfaces.BooleanInput"
  else if boolAnd(generateOutputConnectors, boolAnd(stringEq(causality, "output"),stringEq(baseType, "Real"))) then "Modelica.Blocks.Interfaces.RealOutput"
  else if boolAnd(generateOutputConnectors, boolAnd(stringEq(causality, "output"),stringEq(baseType, "Integer"))) then "Modelica.Blocks.Interfaces.IntegerOutput"
  else if boolAnd(generateOutputConnectors, boolAnd(stringEq(causality, "output"),stringEq(baseType, "Boolean"))) then "Modelica.Blocks.Interfaces.BooleanOutput"
  else if stringEq(causality, "") then baseType else causality+" "+baseType
end dumpFMIModelVariableCausalityAndBaseType;

template dumpFMIModelVariableCausality(String causality)
::=
  <<
  <%if stringEq(causality, "") then "" else causality+" "%>
  >>
end dumpFMIModelVariableCausality;

template dumpFMIRealModelVariableStartValue(String variability, Boolean hasStartValue, Real startValue, Boolean isFixed)
::=
match variability
  case "parameter" then
    if boolAnd(hasStartValue,isFixed) then " = "+startValue
    else if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
    else if boolAnd(boolNot(hasStartValue),isFixed) then "(fixed=true)"
    else if boolAnd(boolNot(hasStartValue),boolNot(isFixed)) then "(fixed=false)"
  case "" then
    if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
end dumpFMIRealModelVariableStartValue;

template dumpFMIIntegerModelVariableStartValue(String variability, Boolean hasStartValue, Integer startValue, Boolean isFixed)
::=
match variability
  case "parameter" then
    if boolAnd(hasStartValue,isFixed) then " = "+startValue
    else if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
    else if boolAnd(boolNot(hasStartValue),isFixed) then "(fixed=true)"
    else if boolAnd(boolNot(hasStartValue),boolNot(isFixed)) then "(fixed=false)"
  case "" then
    if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
end dumpFMIIntegerModelVariableStartValue;

template dumpFMIBooleanModelVariableStartValue(String variability, Boolean hasStartValue, Boolean startValue, Boolean isFixed)
::=
match variability
  case "parameter" then
    if boolAnd(hasStartValue,isFixed) then " = "+startValue
    else if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
    else if boolAnd(boolNot(hasStartValue),isFixed) then "(fixed=true)"
    else if boolAnd(boolNot(hasStartValue),boolNot(isFixed)) then "(fixed=false)"
  case "" then
    if boolAnd(hasStartValue,boolNot(isFixed)) then "(start="+startValue+",fixed=false)"
end dumpFMIBooleanModelVariableStartValue;

template dumpFMIStringModelVariableStartValue(String variability, Boolean hasStartValue, String startValue, Boolean isFixed)
::=
match variability
  case "parameter" then
    if boolAnd(hasStartValue,isFixed) then " = \""+startValue+"\""
    else if boolAnd(hasStartValue,boolNot(isFixed)) then "(start=\""+startValue+"\",fixed=false)"
    else if boolAnd(boolNot(hasStartValue),isFixed) then "(fixed=true)"
    else if boolAnd(boolNot(hasStartValue),boolNot(isFixed)) then "(fixed=false)"
  case "" then
    if boolAnd(hasStartValue,boolNot(isFixed)) then "(start=\""+startValue+"\",fixed=false)"
end dumpFMIStringModelVariableStartValue;

template dumpFMIEnumerationModelVariableStartValue(list<TypeDefinitions> fmiTypeDefinitionsList, String baseType, Boolean hasStartValue, Integer startValue, Boolean isFixed)
::=
  <<
  <%if hasStartValue then " = map_" + getEnumerationTypeFromTypes(fmiTypeDefinitionsList, baseType) + "_from_integer(" + startValue + ")"%>
  >>
end dumpFMIEnumerationModelVariableStartValue;

template dumpFMIModelVariableDescription(String description)
::=
  <<
  <%if stringEq(description, "") then "" else " \""+description+"\""%>
  >>
end dumpFMIModelVariableDescription;

template dumpFMIModelVariablePlacementAnnotation(Integer x1Placement, Integer x2Placement, Integer y1Placement, Integer y2Placement, Boolean generateInputConnectors, Boolean generateOutputConnectors, String causality)
::=
  if boolAnd(generateInputConnectors, stringEq(causality, "input")) then " annotation(Placement(transformation(extent={{"+x1Placement+","+y1Placement+"},{"+x2Placement+","+y2Placement+"}})))"
  else if boolAnd(generateOutputConnectors, stringEq(causality, "output")) then " annotation(Placement(transformation(extent={{"+x1Placement+","+y1Placement+"},{"+x2Placement+","+y2Placement+"}})))"
end dumpFMIModelVariablePlacementAnnotation;

template dumpVariables(list<ModelVariables> fmiModelVariablesList, String type, String variabilityCausality, Boolean dependent, Integer what)
::=
  <<
  <%fmiModelVariablesList |> fmiModelVariable => dumpVariable(fmiModelVariable, type, variabilityCausality, dependent, what) ;separator=", "%>
  >>
end dumpVariables;

template dumpVariable(ModelVariables fmiModelVariable, String type, String variabilityCausality, Boolean dependent, Integer what)
::=
if boolAnd(stringEq(type, "real"), (boolAnd(stringEq(variabilityCausality, "parameter"), boolNot(dependent)))) then
<<
<%
match fmiModelVariable
  case REALVARIABLE(variability="parameter", hasStartValue=true) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "integer"), (boolAnd(stringEq(variabilityCausality, "parameter"), boolNot(dependent)))) then
<<
<%
match fmiModelVariable
  case INTEGERVARIABLE(variability="parameter", hasStartValue=true) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "boolean"), (boolAnd(stringEq(variabilityCausality, "parameter"), boolNot(dependent)))) then
<<
<%
match fmiModelVariable
  case BOOLEANVARIABLE(variability="parameter", hasStartValue=true) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "string"), (boolAnd(stringEq(variabilityCausality, "parameter"), boolNot(dependent)))) then
<<
<%
match fmiModelVariable
  case STRINGVARIABLE(variability="parameter", hasStartValue=true) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "real"), (boolAnd(stringEq(variabilityCausality, "parameter"), dependent))) then
<<
<%
match fmiModelVariable
  case REALVARIABLE(variability="parameter", hasStartValue=false, isFixed=false) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "integer"), (boolAnd(stringEq(variabilityCausality, "parameter"), dependent))) then
<<
<%
match fmiModelVariable
  case INTEGERVARIABLE(variability="parameter", hasStartValue=false, isFixed=false) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "boolean"), (boolAnd(stringEq(variabilityCausality, "parameter"), dependent))) then
<<
<%
match fmiModelVariable
  case BOOLEANVARIABLE(variability="parameter", hasStartValue=false, isFixed=false) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "string"), (boolAnd(stringEq(variabilityCausality, "parameter"), dependent))) then
<<
<%
match fmiModelVariable
  case STRINGVARIABLE(variability="parameter", hasStartValue=false, isFixed=false) then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "real"), stringEq(variabilityCausality, "input")) then
<<
<%
match fmiModelVariable
  case REALVARIABLE(causality="input") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name else if intEq(what,3) then "fmi_input_"+name
%>
>>
else if boolAnd(stringEq(type, "integer"), stringEq(variabilityCausality, "input")) then
<<
<%
match fmiModelVariable
  case INTEGERVARIABLE(causality="input") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name else if intEq(what,3) then "fmi_input_"+name
%>
>>
else if boolAnd(stringEq(type, "boolean"), stringEq(variabilityCausality, "input")) then
<<
<%
match fmiModelVariable
  case BOOLEANVARIABLE(causality="input") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name else if intEq(what,3) then "fmi_input_"+name
%>
>>
else if boolAnd(stringEq(type, "string"), stringEq(variabilityCausality, "input")) then
<<
<%
match fmiModelVariable
  case STRINGVARIABLE(causality="input") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name else if intEq(what,3) then "fmi_input_"+name
%>
>>
else if boolAnd(stringEq(type, "real"), stringEq(variabilityCausality, "output")) then
<<
<%
match fmiModelVariable
  case REALVARIABLE(variability = "",causality="") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
  case REALVARIABLE(variability = "",causality="output") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "integer"), stringEq(variabilityCausality, "output")) then
<<
<%
match fmiModelVariable
  case INTEGERVARIABLE(variability = "",causality="") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
  case INTEGERVARIABLE(variability = "",causality="output") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "boolean"), stringEq(variabilityCausality, "output")) then
<<
<%
match fmiModelVariable
  case BOOLEANVARIABLE(variability = "",causality="") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
  case BOOLEANVARIABLE(variability = "",causality="output") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
else if boolAnd(stringEq(type, "string"), stringEq(variabilityCausality, "output")) then
<<
<%
match fmiModelVariable
  case STRINGVARIABLE(variability = "",causality="") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
  case STRINGVARIABLE(variability = "",causality="output") then
    if intEq(what,1) then valueReference else if intEq(what,2) then name
%>
>>
end dumpVariable;

template dumpOutputGetEnumerationVariables(list<ModelVariables> fmiModelVariablesList, list<TypeDefinitions> fmiTypeDefinitionsList, String fmiGetFunction, String fmiType)
::=
  <<
  <%fmiModelVariablesList |> fmiModelVariable => dumpOutputGetEnumerationVariable(fmiModelVariable, fmiTypeDefinitionsList, fmiGetFunction, fmiType)%>
  >>
end dumpOutputGetEnumerationVariables;

template dumpOutputGetEnumerationVariable(ModelVariables fmiModelVariable, list<TypeDefinitions> fmiTypeDefinitionsList, String fmiGetFunction, String fmiType)
::=
match fmiModelVariable
case ENUMERATIONVARIABLE(variability = "",causality="") then
  <<
  {<%name%>} = map_<%getEnumerationTypeFromTypes(fmiTypeDefinitionsList, baseType)%>_from_integers(<%fmiGetFunction%>(<%fmiType%>, {<%valueReference%>}, flowStatesInputs));<%\n%>
  >>
case ENUMERATIONVARIABLE(variability = "",causality="output") then
  <<
  {<%name%>} = map_<%getEnumerationTypeFromTypes(fmiTypeDefinitionsList, baseType)%>_from_integers(<%fmiGetFunction%>(<%fmiType%>, {<%valueReference%>}, flowStatesInputs));<%\n%>
  >>
end dumpOutputGetEnumerationVariable;

annotation(__OpenModelica_Interface="backend");
end CodegenFMU;

// vim: filetype=susan sw=2 sts=2
