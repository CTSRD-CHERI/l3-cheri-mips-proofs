from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class ExceptionLemmaGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "exception lemma")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif ((l3Function.transitiveDependencies is not None) and
          ("SignalException" not in [f.name for f in l3Function.transitiveDependencies])):
      result = ""
    else:
      result = \
"""lemma ExceptionCase_[NAME] [ExceptionCases]:
  shows "PrePost (exceptionLemmaPre exl pc pcc capr scapr mem)
                 [NAME+VARS]
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding [NAME]_alt_def
by ExceptionCase""" 

      result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
      result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"