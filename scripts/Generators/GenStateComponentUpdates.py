from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class StateComponentUpdatesGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "state component updates")

  def modelToIsa(self, isaPart, l3Model):

    statements = []
    for c in stateComponents:
      statements.extend(self.componentToIsa(c, []))
    result = "lemma state_component_update_simps [simp]:\n"
    result += generateConclusions(statements)
    result += "by simp_all\n"
    result += "\n"

    return result

  def componentToIsa(self, component, prefix):
    fullName = component[0]
    name = fullName.replace(".", "")
    subComponents = component[1]
    names = [fullName] + prefix
    updates = ""
    values = ""
    for n in names:
      updates = n + "_update (" + updates
      values = values + "(" + n + " "
    result = updates + "\<lambda>_. f_" + name + " " + values + "s" + (")" * (2 * len(names))) + " s = \n" + \
             "         " + updates + "f_" + name + (")" * len(names)) + " s"
    statements = [result]
    for c in subComponents:
      statements.extend(self.componentToIsa(c, names))
    return statements
