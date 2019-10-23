from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class MonotonicityGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "SemanticsRestrict")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif ((l3Function.transitiveDependencies is not None) and
          ("raise'exception" not in [f.name for f in l3Function.transitiveDependencies]) and
          (["c_state", "c_exceptionSignalled"] not in l3Function.transitiveWrites) and
          (["BranchDelayPCC"] not in l3Function.transitiveWrites)):
      result = ""
    else:
      result = \
'''lemma SemanticsRestrict_Branch_[NAME] [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 [NAME+VARS]"
unfolding [NAME]_alt_def
by SemanticsRestrict_Branch'''

    namePlusVars = generateFunctionApp("[NAME]", l3Function.arity)
    result = result.replace("[NAME+VARS]", namePlusVars)
    result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"