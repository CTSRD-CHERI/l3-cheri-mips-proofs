from CodeGenBase import *
from CheriStateComponents import *
from CheriModel import *
from IsabelleUtils import *
from Utilities import assertEqual, extendNoDuplicates

class CommutativityGenerator(CodeGenerator):

  def __init__(self):
    CodeGenerator.__init__(self, "commutativity")

  def dependenciesL3FunExt(self, l3Function):
    if (not isinstance(l3Function, L3FunExt)):
      raise Exception("This function can only be used on instances of L3FunExt.")
    if (l3Function.dependencies is None):
      return None
    else:
      result = []
      for d in l3Function.dependencies:
        f = l3Function.findFunction(d)
        if (isinstance(f, ResultPart)):
          result.append(f.parent)
        elif (isinstance(f, StatePart)):
          result.append(f.parent)
        else:
          raise Exception("Unexpected type: %s." % type(f))
      return result

  def canComputeDependencies(self, l3Function):
    if (not isinstance(l3Function, L3FunExt)):
      return False
    else:
      return (not l3Function.reads is None) and \
             (not l3Function.writes is None) and \
             (not l3Function.dependencies is None)

  def functionToIsa(self, l3Function):
    result = ""

    if (isinstance(l3Function, SplitFun)):
      if (self.canComputeDependencies(l3Function)):
        assumptions = []
        for read in l3Function.reads:
          if (len(read) == 1):
            assumptions.append("Commute (read_state %s) m" % read[0])
          else:
            assumptions.append("Commute (read_state (\<lambda>s. %s)) m" % \
                               applyComponents(read, "s"))
        for write in l3Function.writes:
          assumptions.append("\<And>x. Commute (update_state (%s)) m" % \
                             applyComponentUpdates(write, "x"))
        for f in l3Function.dependencyFunctions:
          # Some dependencies are value or state parts, but at this point in the Isabelle file
          # these haven't been generated yet. We therefore use their parent instead. 
          if (isinstance(f, ResultPart)):
            dependency = f.parent
          elif (isinstance(f, StatePart)):
            dependency = f.parent
          else:
            dependency = f
          if (dependency.arity == 0):
            assumptions.append("Commute %s m" % dependency.name)
          else:
            assumptions.append("\<And>x. Commute %s m" % \
                               generateFunctionApp(dependency.name, 
                                                   dependency.arity, 
                                                   baseCharacter = "x"))

        for nextUnknownId in l3Function.nextUnknownIds:
            assumptions.append("Commute (next_unknown ''%s'') m" % nextUnknownId)

        result = generateHeader(3, "@{const [NAME]}") + "\n\n"
        result += '''lemma Commute_[NAME] [Commute_compositeI]:
[ASSUMPTIONS]  shows "Commute [NAME+VARS] m"
unfolding [NAME]_alt_def
using assms
by - Commute_find_dependencies

'''
        result = result.replace("[ASSUMPTIONS]", generateAssumptions(assumptions))
        # if (len(assumptions) == 0):
        #   result = result.replace("[METHOD]", "Commute")
        # else:
        #   result = result.replace("[METHOD]", "(Commute intro: assms)")

    namePlusVars = generateFunctionApp("[NAME]", l3Function.arity)
    result = result.replace("[NAME+VARS]", namePlusVars)
    result = result.replace("[NAME]", l3Function.name)

    if (l3Function.arity == 0):
      result = result.replace("[VARS]", "")
    else:
      result = result.replace("[VARS]", " " + generateVariables(l3Function.arity))
      
    return result