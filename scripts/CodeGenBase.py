# Author: Kyndylan Nienhuis

from shutil import copyfile
from Utilities import assertEqual, zeroBasedLineNumber

CodeGenCommentName = "Code generation"
CodeGenCommentSeparator = " - "
CodeGenCommentStart = "start"
CodeGenCommentEnd = "end"
CodeGenCommentOverride = "override"
CodeGenCommentEndOverride = "end override" 
CodeGenCommentSkip = "skip"    
CodeGenCommentPrefix = "prefix"
CodeGenCommentEndPrefix = "end prefix" 
CodeGenCommentSuffix = "suffix"
CodeGenCommentEndSuffix = "end suffix"  

# Meant for exception messages
def locationFromIndex(content, index, precedingLineCount = None):
  if (precedingLineCount is None):
    return "index %s" % index
  else:
    # In editors the first line is usually line 1 and not line 0
    oneBasedLineNumber = zeroBasedLineNumber(content, index) + 1 + precedingLineCount
    return "line %s" % oneBasedLineNumber

class CodeGenComment:

  def __init__(self, start, startContent, args):
    # start is an integer
    self.start = start
    # startContent is an integer
    self.startContent = startContent
    # args is a list of strings
    self.args = args

def parseCodeGenComment(value, start, precedingLineCount = None):

  startSearchString = "(* " + CodeGenCommentName + CodeGenCommentSeparator
  endSearchString = " *)"

  if (startSearchString != value[start:start + len(startSearchString)]):
    location = locationFromIndex(value, start, precedingLineCount)
    raise Exception("Did not find a CodeGen comment starting at %s. Instead found: '%s'."
                    % (location, value[start:start+10]))
  end = value.find(endSearchString, start)
  if (end == -1):
    location = locationFromIndex(value, start, precedingLineCount)
    raise Exception("Cannot find end of the comment '%s' starting at %s. Comment: '%s'." 
                    % (endSearchString, location, value[start:start+50]))

  arg = value[start + len(startSearchString) : end]
  args = arg.split(CodeGenCommentSeparator)
  if (len(args) < 1):
    raise Exception("To few arguments in CodeGenComment '%s'." % arg)

  item = CodeGenComment(start = start, startContent = end + len(endSearchString), args = args)

  return item

# Testing parseCodeGenComment
testContent = """Lorem ipsum
(* Code generation - blah - foo *)
bla bla bla
(* Code generation - bar *)
bla bla bla bla
(* Code generation - blah *)
Lorem ipsum"""
testComment = parseCodeGenComment(testContent, 12)
assertEqual(["blah", "foo"], testComment.args)
assertEqual(12, testComment.start)
assertEqual(46, testComment.startContent)
testComment = parseCodeGenComment(testContent, 59)
assertEqual(["bar"], testComment.args)
assertEqual(59, testComment.start)
assertEqual(86, testComment.startContent)
# End of test

def indexOfComment(content, argPrefix, index):
  # We cannot search for an exact match, because there might follow more arguments. 
  # Because we do not want to match "end override" if we search for "end", we
  # also cannot search for the prefix only, we have to assert that either the comment
  # end, or other arguments follow.
  searchString = ("(* " + CodeGenCommentName 
                  + CodeGenCommentSeparator 
                  + argPrefix)
  while True:
    index = content.find(searchString, index)
    if (index == -1):
      break
    endIndex = index + len(searchString)
    if (content[endIndex:endIndex + len(" *)")] == " *)"):
      break
    elif (content[endIndex:endIndex + len(CodeGenCommentSeparator)] == CodeGenCommentSeparator):
      break
    else:
      # We have to continue looking
      index = endIndex

  return index

# Testing indexOfComment
assertEqual(-1, indexOfComment("(* Code generation - blah *)", "bar", 0))
assertEqual(0, indexOfComment("(* Code generation - blah *)", "blah", 0))
assertEqual(0, indexOfComment("(* Code generation - blah - foo*)", "blah", 0))
assertEqual(-1, indexOfComment("(* Code generation - blah blah *)", "blah", 0))
# End of test

def findCodeGenComments(content, argPrefix, precedingLineCount = None):
  index = 0
  comments = []
  while True:
    index = indexOfComment(content, argPrefix, index)
    if (index == -1):
      break
    comment = parseCodeGenComment(content, index, precedingLineCount)
    comments.append(comment)
    index = comment.startContent
  return comments

# Testing findCodeGenComments
testContent = """Lorem ipsum
(* Code generation - blah - foo *)
bla bla bla
(* Code generation - bar *)
bla bla bla bla
(* Code generation - blah *)
Lorem ipsum"""
testComments = findCodeGenComments(testContent, "does not exist")
assertEqual(0, len(testComments))
testComments = findCodeGenComments(testContent, "blah")
assertEqual(2, len(testComments))
assertEqual(["blah", "foo"], testComments[0].args)
assertEqual(12, testComments[0].start)
assertEqual(46, testComments[0].startContent)
assertEqual(["blah"], testComments[1].args)
assertEqual(103, testComments[1].start)
assertEqual(131, testComments[1].startContent)
testComments = findCodeGenComments(testContent, "bar")
assertEqual(1, len(testComments))
assertEqual(["bar"], testComments[0].args)
assertEqual(59, testComments[0].start)
assertEqual(86, testComments[0].startContent)
# End of test

def findCodeGenCommentPairs(content, argPrefixStart, argPrefixEnd, precedingLineCount = None):
  index = 0
  comments = []
  while True:
    index = indexOfComment(content, argPrefixStart, index)
    if (index == -1):
      break
    startComment = parseCodeGenComment(content, index, precedingLineCount)

    index = indexOfComment(content, argPrefixEnd, index)
    if (index == -1):
      location = locationFromIndex(content, startComment.start, precedingLineCount)
      raise Exception("The '%s' comment at %s does not end in a '%s' comment." % 
                      (argPrefixStart, location, argPrefixEnd))
    endComment = parseCodeGenComment(content, index, precedingLineCount)

    comments.append((startComment, endComment))
    index = endComment.startContent

  return comments

# Testing findCodeGenCommentPairs
testContent = """Lorem ipsum
(* Code generation - blah - foo *)
bla bla bla
(* Code generation - bar *)
bla bla bla bla
(* Code generation - xxx *)
Lorem ipsum"""
testComments = findCodeGenCommentPairs(testContent, "does not exist", "does not exist")
assertEqual(0, len(testComments))
testComments = findCodeGenCommentPairs(testContent, "blah", "bar")
assertEqual(1, len(testComments))
assertEqual(["blah", "foo"], testComments[0][0].args)
assertEqual(12, testComments[0][0].start)
assertEqual(46, testComments[0][0].startContent)
assertEqual(["bar"], testComments[0][1].args)
assertEqual(59, testComments[0][1].start)
assertEqual(86, testComments[0][1].startContent)
# End of test

class IsaCodeGenPart:

  def __init__(self, codeGenKey, codeGenArgs, content, precedingLineCount = None):

    self.codeGenKey = codeGenKey
    self.codeGenArgs = codeGenArgs
    self.skips = []
    self.overrides = dict([])
    self.prefixes = dict([])
    self.suffixes = dict([])

    # Finding the skips
    skipComments = findCodeGenComments(content, CodeGenCommentSkip, precedingLineCount)
    for comment in skipComments:
      if (len(comment.args) < 2):
        line = lineNumberFromIndex(content, comment.start)
        raise Exception("The '%s' comment at line %s, index %s does not specify a function name." 
                        % (CodeGenCommentSkip, line, comment.start))
      self.skips.append(comment.args[1])

    # Finding the overrides
    overrideComments = findCodeGenCommentPairs(content, 
                         CodeGenCommentOverride, 
                         CodeGenCommentEndOverride,
                         precedingLineCount)
    for commentPair in overrideComments:
      startComment = commentPair[0]
      endComment = commentPair[1]
      if (len(startComment.args) < 2):
        line = lineNumberFromIndex(content, startComment.start)
        raise Exception("The '%s' comment at line %s, index %s does not specify a function name." 
                        % (CodeGenCommentOverride, line, startComment.start))
      self.overrides[startComment.args[1]] = content[startComment.startContent:endComment.start]

    # Finding the prefixes
    prefixComments = findCodeGenCommentPairs(content, 
                         CodeGenCommentPrefix, 
                         CodeGenCommentEndPrefix,
                         precedingLineCount)
    for commentPair in prefixComments:
      startComment = commentPair[0]
      endComment = commentPair[1]
      if (len(startComment.args) < 2):
        line = lineNumberFromIndex(content, startComment.start)
        raise Exception("The '%s' comment at line %s, index %s does not specify a function name." 
                        % (CodeGenCommentPrefix, line, startComment.start))
      self.prefixes[startComment.args[1]] = content[startComment.startContent:endComment.start]

    # Finding the suffixes
    suffixComments = findCodeGenCommentPairs(content, 
                         CodeGenCommentSuffix, 
                         CodeGenCommentEndSuffix,
                         precedingLineCount)
    for commentPair in suffixComments:
      startComment = commentPair[0]
      endComment = commentPair[1]
      if (len(startComment.args) < 2):
        line = lineNumberFromIndex(content, startComment.start)
        raise Exception("The '%s' comment at line %s, index %s does not specify a function name." 
                        % (CodeGenCommentSuffix, line, startComment.start))
      self.suffixes[startComment.args[1]] = content[startComment.startContent:endComment.start]

# Testing IsaCodeGenPart
testContent = """Lorem ipsum
(* Code generation - bla *)
(* Code generation - override - foo *)
bla bla bla
(* Code generation - end override *)
(* Code generation - baz *)
(* Code generation - override - bar *)
bla bla
(* Code generation - end override *)
blub blub
(* Code generation - skip - foobar *)
Lorem ipsum
(* Code generation - suffix - bar2 *)
blob blob blob
(* Code generation - end suffix *)
Lorem ipsum
(* Code generation - prefix - bar2 *)
boo boo boo
(* Code generation - end prefix *)
Lorem ipsum"""
testIsaPart = IsaCodeGenPart("test", ["arg1"], testContent)
assertEqual(["foobar"], testIsaPart.skips)
assertEqual(2, len(testIsaPart.overrides))
assertEqual(True, "foo" in testIsaPart.overrides)
assertEqual(True, "bar" in testIsaPart.overrides)
assertEqual(False, "baz" in testIsaPart.overrides)
assertEqual(False, "bar2" in testIsaPart.overrides)
assertEqual("""
bla bla bla
""", testIsaPart.overrides["foo"])
assertEqual("""
bla bla
""", testIsaPart.overrides["bar"])
assertEqual(1, len(testIsaPart.prefixes))
assertEqual(False, "foo" in testIsaPart.prefixes)
assertEqual(False, "bar" in testIsaPart.prefixes)
assertEqual(False, "baz" in testIsaPart.prefixes)
assertEqual(True, "bar2" in testIsaPart.prefixes)
assertEqual("""
boo boo boo
""", testIsaPart.prefixes["bar2"])
assertEqual(1, len(testIsaPart.suffixes))
assertEqual(False, "foo" in testIsaPart.suffixes)
assertEqual(False, "bar" in testIsaPart.suffixes)
assertEqual(False, "baz" in testIsaPart.suffixes)
assertEqual(True, "bar2" in testIsaPart.suffixes)
assertEqual("""
blob blob blob
""", testIsaPart.suffixes["bar2"])
# End of test

class IsaFile:

  def __init__(self, content):

    self.parts = []

    commentPairs = findCodeGenCommentPairs(content, 
                         CodeGenCommentStart, 
                         CodeGenCommentEnd,
                         precedingLineCount = 0)
    end = 0
    for commentPair in commentPairs:
      startComment = commentPair[0]
      endComment = commentPair[1]

      # We add the text part before this pair
      if (startComment.start != end):
        self.parts.append(content[end:startComment.start])

      # We add the code generation part
      # The first argument is the name of the code generator    
      if (len(startComment.args) < 2):
        line = lineNumberFromIndex(content, start)
        raise Exception("The '%s' comment at line %s, index %s has too few arguments." 
                        % (CodeGenCommentStart, line, start))
      codeGenerationName = startComment.args[1]
      # The other arguments are just passed on
      codeGenArgs = startComment.args[2:]
      line = zeroBasedLineNumber(content, startComment.startContent)
      self.parts.append(IsaCodeGenPart(codeGenerationName,
                                       codeGenArgs,
                                       content[startComment.startContent:endComment.start],
                                       precedingLineCount = line))
      end = endComment.startContent        

    # We add the final text part
    self.parts.append(content[end:])

# Testing IsaFile
testContent = """Lorem ipsum
(* Code generation - start - foo *)
bla bla blup
(* Code generation - bar *)
(* Code generation - override - foo *)
bla bla bla
(* Code generation - end override *)
bla bla bla bla blup
(* Code generation - end *)
Ipsum lorem"""
testIsaFile = IsaFile(testContent)
assertEqual(3, len(testIsaFile.parts))
assertEqual("""Lorem ipsum
""", testIsaFile.parts[0])
assertEqual("""
bla bla bla
""", testIsaFile.parts[1].overrides["foo"])
assertEqual("""
Ipsum lorem""", testIsaFile.parts[2])
# End of test

def findFunctionIn(name, functions):
  result = next ((f for f in functions if f.name == name), None)
  if (result is None):
    raise Exception("Cannot find function '%s'." % name)
  else:
    return result

class L3Fun:
  
  def __init__(self, name):
    # name should be of type string
    self.name = name
    # The following field is set by L3Component
    self.parentComponent = None
    # The following field is set by setPreviousFunctions
    self.previousFunctions = None

    # The following field can be changed by child classes.
    # It is a list of L3Fun, containing function definitions that 
    # are derived from this function (self). 
    self.derivedFunctions = []

  def setPreviousFunctions(self, previousFunctions):
    self.previousFunctions = previousFunctions

  def findFunction(self, name):
    if (self.previousFunctions is None):
      raise Exception("findFunction can only be called when previousFunctions has a value.")
    return findFunctionIn(name, self.previousFunctions)

class L3Component:

  def __init__(self, getter, setter):
    # getter and setter should be of type L3Fun
    self.getter = getter
    self.setter = setter
    getter.parentComponent = self
    setter.parentComponent = self

class L3File:

  def __init__(self, name, members):
    # name should be of type string
    self.name = name
    # members should be of type (L3Component or L3Fun) list
    self.members = members
    # We compute the subfunctions
    self.subFunctions = []
    for member in self.members:
      if (isinstance(member, L3Component)):
        self.subFunctions.append(member.getter)
        self.subFunctions.append(member.setter)
      elif (isinstance(member, L3Fun)):
        self.subFunctions.append(member)
      else:
        raise Exception("Invalid type: %s." % type(member))
    self.subFunctionsAndDerivatives = []
    for f in self.subFunctions:
      self.subFunctionsAndDerivatives.append(f)
      self.subFunctionsAndDerivatives.extend(f.derivedFunctions)

  def setPreviousFunctions(self, previousFunctions):
    self.previousFunctions = previousFunctions
    for f in self.subFunctions:
      i = self.subFunctionsAndDerivatives.index(f)
      f.setPreviousFunctions(previousFunctions + self.subFunctionsAndDerivatives[0:i])

  def setPreviousFiles(self, previousFiles):
    functions = []
    for f in previousFiles:
      functions.extend(f.subFunctionsAndDerivatives)
    self.setPreviousFunctions(functions)

  def findFunction(self, name):
    if (self.previousFunctions is None):
      raise Exception("findFunction can only be called when previousFunctions has a value.")
    return findFunctionIn(name, self.previousFunctions + self.subFunctionsAndDerivatives)

class L3Model:

  def __init__(self, files):
    # files should be of type L3File list
    self.files = files
    # We compute the subfunctions
    self.subFunctions = []
    self.subFunctionsAndDerivatives = []
    for f in self.files:
      self.subFunctions.extend(f.subFunctions)
      self.subFunctionsAndDerivatives.extend(f.subFunctionsAndDerivatives)
    # We finish the initialisation of the files by calling setPreviousFunctions
    for i in range(0, len(self.files)):
      self.files[i].setPreviousFiles(self.files[0:i])

  def findFunction(self, name):
    return findFunctionIn(name, self.subFunctionsAndDerivatives)

def codeGenCommentToString(codeCommentParts):
  return ("(* " + CodeGenCommentName 
                + CodeGenCommentSeparator 
                + CodeGenCommentSeparator.join(codeCommentParts) 
                + " *)")

# Testing codeGenCommentToString
assertEqual("(* " + CodeGenCommentName + " - foo1 - foo2 *)", 
            codeGenCommentToString(["foo1", "foo2"]))
# End of test
      
# Testing subFunctions, findFunction, previousFunctions, etc.
testL3Model = L3Model(
  [L3File("file0", [L3Fun("fun0"), L3Fun("fun1"), L3Fun("fun2")]),
   L3File("file1", [L3Fun("fun3"), L3Fun("fun4"), L3Fun("fun5")]),
   L3File("file2", [L3Component(L3Fun("fun6"), L3Fun("fun7"))])])
fun4 = testL3Model.files[1].members[1]
# subFunctions
assertEqual(8, len(testL3Model.subFunctions))
assertEqual(3, len(testL3Model.files[1].subFunctions))
# previousFunctions
assertEqual(3, len(testL3Model.files[1].previousFunctions))
assertEqual(4, len(fun4.previousFunctions))
# findFunction
assertEqual("fun1", testL3Model.files[1].findFunction("fun1").name)
assertEqual("fun1", fun4.findFunction("fun1").name)
# End of test

class CodeGenerator:

  def __init__(self, codeGenKey):
    self.codeGenKey = codeGenKey

  def headerToIsa(self, headerName):
    return ""

  def functionToIsa(self, l3Function):
    return ""

  def overrideOrFunctionToIsa(self, isaPart, l3Function):
    result = ""
    if (l3Function.name in isaPart.skips):
      result += codeGenCommentToString([CodeGenCommentSkip, l3Function.name])
      result += "\n\n"
    elif (l3Function.name in isaPart.overrides):
      result += codeGenCommentToString([CodeGenCommentOverride, l3Function.name])
      # We don't add a newline here, because an override contains everything between the comments
      # in the original file (in other words, it also contains the starting and ending newlines). 
      result += isaPart.overrides[l3Function.name]
      result += codeGenCommentToString([CodeGenCommentEndOverride])
      result += "\n\n"
    else:
      if (l3Function.name in isaPart.prefixes):
        result += codeGenCommentToString([CodeGenCommentPrefix, l3Function.name])
        # We don't add a newline here, same reason
        result += isaPart.prefixes[l3Function.name]
        result += codeGenCommentToString([CodeGenCommentEndPrefix])
        result += "\n\n"
      result += self.functionToIsa(l3Function)
      if (l3Function.name in isaPart.suffixes):
        result += codeGenCommentToString([CodeGenCommentSuffix, l3Function.name])
        # We don't add a newline here, same reason
        result += isaPart.suffixes[l3Function.name]
        result += codeGenCommentToString([CodeGenCommentEndSuffix])
        result += "\n\n"
    return result
   
  def fileToIsa(self, isaPart, l3File):
    result = ""
    for member in l3File.members:
      if (isinstance(member, L3Component)):
        result += self.overrideOrFunctionToIsa(isaPart, member.getter)
        result += self.overrideOrFunctionToIsa(isaPart, member.setter)
      elif (isinstance(member, L3Fun)):
        result += self.overrideOrFunctionToIsa(isaPart, member)
      else:
        raise Exception("Invalid type: %s." % type(member))      
    return result

  def modelToIsa(self, isaPart, l3Model):
    result = ""
    for l3File in l3Model.files:
      result += self.headerToIsa(l3File.name)
      result += self.fileToIsa(isaPart, l3File)
    return result

def findCodeGenerator(CodeGenerators, codeGenKey):
  found = [x for x in CodeGenerators if x.codeGenKey == codeGenKey]
  if (len(found) == 0):
    raise Exception("There is no CodeGenerator with key: %s." % codeGenKey)
  elif (len(found) > 1):
    raise Exception("There are multiple CodeGenerators with key: %s." % codeGenKey)
  else:
    return found[0]

def generateContent(CodeGenerators, content, l3Model):
  isaFile = IsaFile(content)
  result = ""
  for part in isaFile.parts:
    if (type(part) is str):
      result += part
    else:
      CodeGenerator = findCodeGenerator(CodeGenerators, part.codeGenKey)
      result += codeGenCommentToString([CodeGenCommentStart, part.codeGenKey] + part.codeGenArgs)
      result += "\n\n"
      result += CodeGenerator.modelToIsa(part, l3Model)
      result += codeGenCommentToString([CodeGenCommentEnd])
  return result

def generateFile(CodeGenerators, fileName, l3Model):

  with open (fileName, "r", newline = '') as myFile:
    fileContents = myFile.read()

  try:
    newContents = generateContent(CodeGenerators, fileContents, l3Model)
  except Exception as ex:
    raise Exception("Exception while processing file '%s'." % fileName) from ex

  if (newContents != fileContents):
    tempFileName = fileName + ".temp"
    copyfile(fileName, tempFileName)    
    with open (fileName, "w", newline = '') as myFile:
      myFile.write(newContents)
    
  return

# Testing CodeGenerator
class TestCodeGenerator(CodeGenerator):
  def __init__(self):
    CodeGenerator.__init__(self, "foo")
  def headerToIsa(self, headerName):
    return "Header " + headerName + "\n\n"
  def functionToIsa(self, l3Function):
    return "Function " + l3Function.name + "\n\n"

testContent = \
"""Lorem ipsum bla blah

(* Code generation - start - foo *)

Header file0

Function fun0

(* Code generation - override - fun1 *)

Bla blah blah blah

(* Code generation - end override *)

(* Code generation - prefix - fun2 *)

Foo bar foo bar

(* Code generation - end prefix *)

Function fun2

(* Code generation - override - fun3 *)

Blub blub

(* Code generation - end override *)

(* Code generation - skip - fun4 *)

Function fun5

(* Code generation - suffix - fun5 *)

Blub Blah blub

(* Code generation - end suffix *)

(* Code generation - end *)

Ipsum lorem"""

testL3Model = L3Model([L3File("file0", [
  L3Fun("fun0"), L3Fun("fun1"), L3Fun("fun2"), L3Fun("fun3"), L3Fun("fun4"), L3Fun("fun5")])])
generator = TestCodeGenerator()
generatedContent = generateContent([generator], testContent, testL3Model)
assertEqual(testContent, generatedContent)

# We test whether we can override modelToIsa
class TestCodeGenerator2(CodeGenerator):
  def __init__(self):
    CodeGenerator.__init__(self, "foo")
  def modelToIsa(self, isaPart, l3Model):
    return "bar: " + " ".join(isaPart.codeGenArgs) + "\n\n"

testContent = \
"""Lorem ipsum bla blah

(* Code generation - start - foo - arg1 - arg2 - arg3 *)

bar: arg1 arg2 arg3

(* Code generation - end *)

Ipsum lorem blah bla"""

generator = TestCodeGenerator2()
generatedContent = generateContent([generator], testContent, None)
assertEqual(testContent, generatedContent)
# End of test
