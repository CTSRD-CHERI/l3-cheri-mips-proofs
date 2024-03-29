from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class ExceptionSignalledInvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "ExceptionSignalled invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    else:
      result = \
"""lemma ExceptionSignalled_[NAME] [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) [NAME+VARS]"
unfolding [NAME]_alt_def
by (Invariant intro: ExceptionSignalledI)""" 

      result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
      result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"