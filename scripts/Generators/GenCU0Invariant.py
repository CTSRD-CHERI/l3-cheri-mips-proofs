from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class CU0InvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "CU0 invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif (l3Function.transitiveDependencies is not None):
      result = ""
    else:
      result = \
"""lemma CU0Invariant_[NAME] [CU0InvariantI]:
  shows "IsInvariant CU0Invariant [NAME+VARS]"
unfolding [NAME]_alt_def 
by (Invariant intro: CU0InvariantI)""" 

      result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
      result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"