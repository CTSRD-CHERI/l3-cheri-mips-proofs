from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class ValueAndStatePartsGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "state and value parts")

  def ValuePartToIsa(self, l3Function):
    result = ""
    if (isinstance(l3Function, SplitFun)):
      if (l3Function.resultIsUnit):
        result += 'text \<open>The term @{term "ValuePart [NAME+VARS]"} is simplified to @{term "\<lambda>_. ()"}.\<close>\n\n'
      else:
        result += 'abbreviation "[getNAME][VARS] \<equiv> ValuePart [NAME+VARS]"\n\n'
      getNamePlusVars = generateFunctionApp("[getNAME]", l3Function.arity)
      result = result.replace("[getNAME+VARS]", getNamePlusVars)
      result = result.replace("[getNAME]", l3Function.resultPartName)
    return result

  def StatePartToIsa(self, l3Function):
    result = ""
    if (isinstance(l3Function, SplitFun)):
      if (l3Function.transitiveWrites is None):
        result += 'abbreviation "[setNAME][VARS] \<equiv> StatePart [NAME+VARS]"\n\n'
      elif (len(l3Function.transitiveWrites) == 0 
            and len(l3Function.nextUnknownIds) == 0):
        result += '''lemma [NAME]_read_only [simp]:
  shows "StatePart [NAME+VARS] = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_[NAME]) auto

'''
      else:
        result += 'abbreviation "[setNAME][VARS] \<equiv> StatePart [NAME+VARS]"\n\n'

      setNamePlusVars = generateFunctionApp("[setNAME]", l3Function.arity)
      result = result.replace("[setNAME+VARS]", setNamePlusVars)
      result = result.replace("[setNAME]", l3Function.statePartName)
    return result

  def getSetSimp(self, l3Function):
    result = ""
    if (isinstance(l3Function, SplitFun)):
      if (l3Function.getSetSimp and
          (not l3Function.parentComponent is None) and
          (l3Function.parentComponent.setter is l3Function)):
        getter = l3Function.parentComponent.getter
        setter = l3Function.parentComponent.setter
        if (l3Function.indexed):
          result += \
"""lemma [getterResultNAME]_[setterStateNAME]_simp [simp]:
  shows "[getterResultNAME] index' ([setterStateNAME] x s) = (if index' = snd x then fst x else [getterResultNAME] index' s)"
unfolding [getterNAME]_alt_def [setterNAME]_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

"""
        else:
          result += \
"""lemma [getterResultNAME]_[setterStateNAME]_simp [simp]:
  shows "[getterResultNAME] ([setterStateNAME] v s) = v"
unfolding [getterNAME]_alt_def [setterNAME]_alt_def
by (simp add: ValuePart_bind StatePart_bind)

"""
        result = result.replace("[getterResultNAME]", getter.resultPartName)
        result = result.replace("[setterStateNAME]", setter.statePartName)
        result = result.replace("[getterNAME]", getter.name)
        result = result.replace("[setterNAME]", setter.name)
    return result

  def functionToIsa(self, l3Function):
    result = ""

    if (isinstance(l3Function, SplitFun)):
      result = generateHeader(3, "@{const [NAME]}") + "\n\n"
      result += self.ValuePartToIsa(l3Function)
      result += self.StatePartToIsa(l3Function)
      result += self.getSetSimp(l3Function)    

      namePlusVars = generateFunctionApp("[NAME]", l3Function.arity)
      result = result.replace("[NAME+VARS]", namePlusVars)
      result = result.replace("[NAME]", l3Function.name)
      if (l3Function.arity == 0):
        result = result.replace("[VARS]", "")
      else:
        result = result.replace("[VARS]", " " + generateVariables(l3Function.arity))
      
    return result