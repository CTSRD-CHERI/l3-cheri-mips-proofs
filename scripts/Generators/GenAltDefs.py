from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class AltDefsGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "alternative definitions")

  def functionToIsa(self, l3Function):
    result = """schematic_goal [NAME]_alt_def[ATTRIBUTE]:
  shows "[NAME] = ?x"
unfolding [NAME]_def
unfolding Let_def
by compute_alt_def

""" 
    if (isinstance(l3Function, UnfoldFun)):
      result = result.replace("[ATTRIBUTE]", " [simp]")
    else:
      result = result.replace("[ATTRIBUTE]", "")
    result = result.replace("[NAME]", l3Function.name)
    return result