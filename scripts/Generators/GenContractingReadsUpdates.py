from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class ContractingReadsUpdatesGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "contracting reads and updates")

  def getCompName(self, value):
    if (value.startswith("c_")):
      value = value[2:]
    i = value.find(".")
    if (i >= 0):
      value = value[i+1:]
    return firstLetterUpperCase(value)

  def getCompPathName(self, values):
    if (len(values) == 0):
      return ""
    else:
      if (values[0] == "c_state"):
        # We omit c_state, because at the moment all sub components of interest are sub components
        # of c_state. 
        prefix = ""
      else:
        prefix = self.getCompName(values[0])
      return prefix + self.getCompPathName(values[1:])      

  def subcomponentsToIsa(self, prefix, parentComponent):
    result = ""
    for c in parentComponent[1]:
      result += generateHeader(2, "@{const [COMP]}") + "\n\n"
      result += '''abbreviation get[COMP_NAME] where
  "get[COMP_NAME] \<equiv> (\<lambda>s. [COMPONENTS])"

lemmas contract_get[PARENT_NAME]_[COMP_NAME] [alt_def_simp] = 
  contract_read[where getParent=get[PARENT_NAME] and sub=[COMP]]

abbreviation set[COMP_NAME] where
  "set[COMP_NAME] v \<equiv> [COMPONENTS_UPDATE]"

lemmas contract_c_state_update_[COMP_NAME] [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=get[PARENT_NAME]
                           and setParent=set[PARENT_NAME]
                           and sub_update=[COMP]_update]
  contract_update[where getParent=get[PARENT_NAME] 
                    and setParent=set[PARENT_NAME]
                    and sub=[COMP]
                    and sub_update=[COMP]_update]

'''
      parentPath = prefix + [parentComponent[0]]
      path = parentPath + [c[0]]
      result = result.replace("[COMP]", c[0])
      result = result.replace("[COMPONENTS]", applyComponents(path, "s"))
      result = result.replace("[COMPONENTS_UPDATE]", applyComponentUpdates(path, "(\<lambda>_. v)"))
      result = result.replace("[COMP_NAME]", self.getCompPathName(path))
      result = result.replace("[PARENT_NAME]", self.getCompPathName(parentPath))
      result += self.subcomponentsToIsa(parentPath, c)
    return result

  def modelToIsa(self, isaPart, l3Model):
    result = ""
    c_state_component = findComponent("c_state")
    for c in c_state_component[1]:
      result += generateHeader(2, "@{const [COMP]}") + "\n\n"
      result += '''abbreviation get[COMP_NAME] where
  "get[COMP_NAME] \<equiv> (\<lambda>s. [COMP] (c_state s))"

lemma [L3_COMP_NAME]_alt [alt_def_simp]:
  shows "[L3_COMP_NAME] = read_state get[COMP_NAME]"
unfolding [L3_COMP_NAME]_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_[COMP_NAME] [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=[COMP]]

abbreviation set[COMP_NAME] where
  "set[COMP_NAME] v \<equiv> c_state_update ([COMP]_update (\<lambda>_. v))"

lemma write'[L3_COMP_NAME]_alt [alt_def_simp]:
  shows "write'[L3_COMP_NAME] = (\<lambda>v. update_state (set[COMP_NAME] v))"
unfolding write'[L3_COMP_NAME]_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_[COMP_NAME] [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=[COMP]_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=[COMP]
                    and sub_update=[COMP]_update]

'''
      result = result.replace("[COMP]", c[0])
      result = result.replace("[COMP_NAME]", self.getCompName(c[0]))
      if (c[0] == "c_CoreStats"):
        # Just removing "c_" would resul in "CoreStats", but
        # the corresponding function in the model is "coreStats". Not
        # sure why the capitalisation is not consistent in the model. 
        result = result.replace("[L3_COMP_NAME]", "coreStats")
      elif (c[0].startswith("c_")):
        result = result.replace("[L3_COMP_NAME]", c[0][2:])
      else:
        result = result.replace("[L3_COMP_NAME]", c[0])
      result += self.subcomponentsToIsa(["c_state"], c)
    return result