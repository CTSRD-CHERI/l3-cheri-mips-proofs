from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class AddressTranslationInvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "address translation invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    else:
      conflictsWithLookupTLB = l3Function.conflictsWith(model.findFunction("LookupTLB"))
      conflictsWithCheckSegment = l3Function.conflictsWith(model.findFunction("CheckSegment"))
      conflictsWithRaiseException = l3Function.conflictsWith(model.findFunction("raise'exception"))

      if (conflictsWithLookupTLB == False and 
          conflictsWithCheckSegment == False and 
          conflictsWithRaiseException == False):
        result = ""
      else:
        result = \
"""lemma AddressTranslationInvariant_[NAME] [MapVirtualAddressInvariantI]:
  shows "PrePost (AddressTranslationPre X) [NAME+VARS] (\<lambda>_. AddressTranslationPost X)" 
unfolding [NAME]_alt_def
by MapVirtualAddressInvariant"""
        
        result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
        result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"