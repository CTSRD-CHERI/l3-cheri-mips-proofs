from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class UndefinednessLemmaGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "undefinedness lemma")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif ((l3Function.transitiveDependencies is not None) and
          ("raise'exception" not in [f.name for f in l3Function.transitiveDependencies])):
      result = ""
    else:
      result = \
"""lemma UndefinedCase_[NAME] [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) [NAME+VARS]"
unfolding [NAME]_alt_def 
by UndefinedCases""" 

      result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
      result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"