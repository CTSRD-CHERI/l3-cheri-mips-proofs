# Author: Kyndylan Nienhuis

from Utilities import assertEqual

def hideFromLatex(value):
  return "(*<*)\n" + value + "\n(*>*)"

def firstLetterUpperCase(value):
  if (len(value) == 0):
    return value
  elif (len(value) == 1):
    return value.upper()
  else:
    return value[0].upper() + value[1:]

# Testing firstLetterUpperCase
assertEqual("", firstLetterUpperCase(""))
assertEqual("A", firstLetterUpperCase("a"))
assertEqual("Ab", firstLetterUpperCase("ab"))
assertEqual("AB", firstLetterUpperCase("AB"))
assertEqual("_", firstLetterUpperCase("_"))
# End of test

def generateHeader(level, name):
  if (level == 0):
    result = "chapter"
  elif (level == 1):
    result = "section"
  elif (level == 2):
    result = "subsection"
  elif (level == 3):
    result = "subsubsection"
  elif (level == 4):
    result = "paragraph"
  else:
    raise Exception("Invalid level: %s." % level)
  return result + " \<open>" + name + "\<close>"

def generateEscapedHeader(level, name):
  escapedName = name.replace("_", "-")
  return generateHeader(level, escapedName)

def generateVariables(count, baseCharacter = "v"):
  if (count < 0):
    raise Exception("Invalid count: %s." % count)
  elif (count == 0):
    return ""
  elif (count == 1):
    return baseCharacter
  else:
    names = []
    for i in range(1, count + 1):
      names.append("%s%i" % (baseCharacter, i))
    return " ".join(names)

# Testing generateVariables
assertEqual("", generateVariables(0))
assertEqual("v", generateVariables(1))
assertEqual("v1 v2", generateVariables(2))
assertEqual("v1 v2 v3", generateVariables(3))
assertEqual("u1 u2 u3", generateVariables(3, "u"))
# End of test

def generateLambda(countOfVars):
  if (countOfVars < 0):
    raise Exception("Invalid count: %s." % countOfVars)
  elif (countOfVars == 0):
    return ""
  else:
    return "\<lambda>" + generateVariables(countOfVars) + ". "

# Testing generateLambda
assertEqual("", generateLambda(0))
assertEqual("\<lambda>v. ", generateLambda(1))
assertEqual("\<lambda>v1 v2. ", generateLambda(2))
assertEqual("\<lambda>v1 v2 v3. ", generateLambda(3))
# End of test

def generateFunctionApp(name, arity, parenthesis = True, baseCharacter = "v"):
  if (arity < 0):
    raise Exception("Invalid arity: %s." % arity)
  elif (arity == 0):
    result = name
  else:
    result = name + " " + generateVariables(arity, baseCharacter)
    if (parenthesis):
      result = "(" + result + ")"
  return result

# Testing generateFunctionApp
assertEqual("foo", generateFunctionApp("foo", 0))
assertEqual("(foo v)", generateFunctionApp("foo", 1))
assertEqual("foo v", generateFunctionApp("foo", 1, parenthesis = False))
assertEqual("(foo v1 v2)", generateFunctionApp("foo", 2))
assertEqual("(foo u1 u2)", generateFunctionApp("foo", 2, baseCharacter = "u"))
# End of test

def generateAssumptions(statements):
  result = ""
  if (len(statements) > 0):
    result = result + "  assumes \"" + statements[0] + "\"\n"
    for statement in statements[1:]:
      result = result + "      and \"" + statement + "\"\n"
  return result

def generateConclusions(statements):
  result = ""
  if (len(statements) > 0):
    result = result + "  shows \"" + statements[0] + "\"\n"
    for statement in statements[1:]:
      result = result + "    and \"" + statement + "\"\n"
  return result
