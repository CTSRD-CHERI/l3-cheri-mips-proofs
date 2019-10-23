from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class CapInvariantGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "capability invariant")

  def functionToIsa(self, l3Function):
    if (isinstance(l3Function, UnfoldFun)):
      result = ""
    elif (l3Function.name in FunctionsWithActions):
      result = \
"""lemma CapInvariant_[NAME] [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind [DERIVATIONS+VARS]
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 [NAME+VARS] 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding [NAME]_alt_def [DERIVATIONS]_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?"""
      derivationsPlusVars = generateFunctionApp("[DERIVATIONS]", l3Function.arity)
      if (l3Function.name.startswith("dfn'")):
        derivationsName = l3Function.name[4:]
      else:
        derivationsName = l3Function.name
      result = result.replace("[DERIVATIONS+VARS]", derivationsPlusVars)
      result = result.replace("[DERIVATIONS]", derivationsName + "Actions")
    elif ((l3Function.transitiveDependencies is not None) and
          ("raise'exception" not in [f.name for f in l3Function.transitiveDependencies]) and
          ("write'PCC" not in [f.name for f in l3Function.transitiveDependencies]) and
          ("write'CAPR" not in [f.name for f in l3Function.transitiveDependencies]) and
          (["BranchDelayPCC"] not in l3Function.transitiveWrites) and
          (["BranchToPCC"] not in l3Function.transitiveWrites) and
          (["the_MEM"] not in l3Function.transitiveWrites)):
      result = ""
    else:
      result = \
"""lemma CapInvariant_[NAME] [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) [NAME+VARS]"
unfolding [NAME]_alt_def
by CapInvariant"""

    namePlusVars = generateFunctionApp("[NAME]", l3Function.arity)
    result = result.replace("[NAME+VARS]", namePlusVars)
    result = result.replace("[NAME]", l3Function.name)
  
    if (result == ""):
      return ""
    else:
      return result + "\n\n"