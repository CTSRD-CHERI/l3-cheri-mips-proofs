from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class KernelModeInvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "KernelMode invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif ((l3Function.transitiveDependencies is not None) and
          ("SignalException" not in [f.name for f in l3Function.transitiveDependencies])):
      result = ""
    else:
      result = \
"""lemma kernelModeInvariant_[NAME] [KernelModeInvariantI]:
  shows "PrePost KernelModePre [NAME+VARS] (\<lambda>_. KernelModePost)" 
unfolding [NAME]_alt_def 
by KernelModeInvariant""" 

      result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
      result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"