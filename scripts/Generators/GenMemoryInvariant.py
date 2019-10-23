from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class MemoryInvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "memory invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif (l3Function.name in FunctionsWithActions):
      result = \
'''lemma MemoryInvariant_[NAME] [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind [DERIVATIONS+VARS]
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 [NAME+VARS]
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding [NAME]_alt_def [DERIVATIONS]_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?'''
      derivationsPlusVars = generateFunctionApp("[DERIVATIONS]", l3Function.arity)
      if (l3Function.name.startswith("dfn'")):
        derivationsName = l3Function.name[4:]
      else:
        derivationsName = l3Function.name
      result = result.replace("[DERIVATIONS+VARS]", derivationsPlusVars)
      result = result.replace("[DERIVATIONS]", derivationsName + "Actions")
    elif ((l3Function.transitiveDependencies is not None) and
          ("SignalException" in [f.name for f in l3Function.transitiveDependencies])):
      result = \
"""lemma MemoryInvariant_[NAME] [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) [NAME+VARS]"
by MemoryInvariant auto?""" 
    elif ((l3Function.transitiveDependencies is not None) and
          (["the_MEM"] not in l3Function.transitiveWrites)):
      result = ""
    else:
      result = \
"""lemma MemoryInvariant_[NAME] [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) [NAME+VARS]"
unfolding [NAME]_alt_def 
by MemoryInvariant auto?""" 

    result = result.replace("[NAME+VARS]", generateFunctionApp("[NAME]", l3Function.arity))
    result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"