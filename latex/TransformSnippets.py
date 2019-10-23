from Testing import assertEqual
from IsaMetaInfo import *
import datetime

SnippetStart = "\\DefineSnippet{"
SnippetEnd = "}%EndSnippet"

def removeComments(value):
  lines = value.splitlines()
  result = []
  for line in lines:
    index = line.find("%")
    if (index == -1):
      result.append(line)
    else:
      result.append(line[0:index])
  return "\n".join(result)

# Testing removeComments
assertEqual("", removeComments(""))
assertEqual("", removeComments("%"))
assertEqual("foo ", removeComments("foo % bar"))
assertEqual("foo \nbar ", removeComments("foo % bar\nbar % baz"))
# End of test

def findClosingBracket(value, index):
  depth = 0
  for i in range(index, len(value)):
    if value[i] == "{":
      depth += 1
    elif value[i] == "}":
      depth -= 1
    if depth < 0:
      # We found the end
      return i
  return -1

# Testing findClosingBracket
assertEqual(-1, findClosingBracket("", 0))
assertEqual(0, findClosingBracket("}", 0))
assertEqual(3, findClosingBracket("foo}", 0))
assertEqual(5, findClosingBracket("{}foo}", 0))
assertEqual(6, findClosingBracket("{{}}{}}", 0))
# End of test

def removeCommand(value, commandName, removeArgument):
  startCommand = "\\%s{" % commandName
  indexStartCommand = value.find(startCommand)
  if indexStartCommand == -1:
    # The command does not appear
    return value
  else:
    processedPrefix = value[0:indexStartCommand]
    indexStartArgument = indexStartCommand + len(startCommand)
    indexEndArgument = findClosingBracket(value, indexStartArgument)
    if (indexEndArgument == -1):
      raise Exception("The command %s in %s does not contains a closing bracket." % \
                      (commandName, value))
    indexEndCommand = indexEndArgument + 1
    rawPostfix = value[indexEndCommand:len(value)]
    processedPostFix = removeCommand(rawPostfix, commandName, removeArgument)
    if removeArgument:
      return processedPrefix + processedPostFix
    else:
      rawArgument = value[indexStartArgument:indexEndArgument]
      processedArgument = removeCommand(rawArgument, commandName, removeArgument)
      return processedPrefix + processedArgument + processedPostFix

# Testing removeCommand
assertEqual("", removeCommand("", "cmd", True))
assertEqual("", removeCommand("\\cmd{}", "cmd", True))
assertEqual("", removeCommand("\\cmd{foo}", "cmd", True))
assertEqual("", removeCommand("\\cmd{foo{}}", "cmd", True))
assertEqual("", removeCommand("\\cmd{foo\\cmd{}}", "cmd", True))
assertEqual("blah  bla  blah", removeCommand("blah \\cmd{foo} bla \\cmd{baz} blah", "cmd", True))
assertEqual("blah  bla", removeCommand("blah \\cmd{foo} bla", "cmd", True))
assertEqual("foo", removeCommand("\\cmd{foo}", "cmd", False))
assertEqual("blah foo bla", removeCommand("blah \\cmd{foo} bla", "cmd", False))
assertEqual("foo bar", removeCommand("\\cmd{foo \\cmd{bar}}", "cmd", False))
# End of test

def extractLabelName(value):
  startLabel = "\\label{"
  index = value.find(startLabel)
  if index == -1:
    # There is no label
    return None
  else:
    indexStartName = index + len(startLabel)
    indexEndName = findClosingBracket(value, indexStartName)
    if indexEndName == -1:
      raise Exception("Cannot find the end of the label name %s" 
                      % value[indexStartName, indexStartName + 20])
    labelName = value[indexStartName:indexEndName]
    labelName = labelName.replace("{\\isacharprime}", "")
    labelName = labelName.replace("{\\isacharminus}", "-")
    return labelName

# Testing extractLabelName
assertEqual(None, extractLabelName(""))
assertEqual("foo", extractLabelName("\\label{foo}"))
assertEqual("foo", extractLabelName("blah \\label{foo} bar baz"))
# End of test

def removeLabelsFromIndent(value):
  startIndent = "\\isaindent{"
  index = value.find(startIndent)
  if index == -1:
    # There is no indent
    return value
  else:
    indexStartIndent = index + len(startIndent)
    indexEndIndent = findClosingBracket(value, indexStartIndent)
    prefix = value[0:indexStartIndent]
    indent = removeCommand(value[indexStartIndent:indexEndIndent], "label", removeArgument=True)
    postfix = value[indexEndIndent:len(value)]
    return prefix + indent + postfix

# Testing removeLabelsFromIndent
assertEqual("", removeLabelsFromIndent(""))
assertEqual("\\label{foo}", removeLabelsFromIndent("\\label{foo}"))
assertEqual("\\isaindent{}", removeLabelsFromIndent("\\isaindent{\\label{foo}}"))
assertEqual("\\label{bar}\\isaindent{}", 
            removeLabelsFromIndent("\\label{bar}\\isaindent{\\label{foo}}"))
# End of test

class SnippetLine:

  def __init__(self, line, labelName=None):
    self.line = line
    self.labelName = labelName
    self.hasLabel = (not labelName is None)

def parseSnippetLine(line):
  # We remove the labels from the indent, because otherwise extractLabel could get confused
  line = removeLabelsFromIndent(line)
  labelName = extractLabelName(line)
  # We now remove the label itself too
  line = removeCommand(line, "label", removeArgument=True)
  line = line.strip()
  return SnippetLine(line, labelName)

class Snippet:

  def __init__(self, name, lines):

    self.name = name
    self.lines = lines
    self.hasLabels = any(l.hasLabel for l in lines)

def parseSnippet(value, start):

  if (SnippetStart != value[start:start + len(SnippetStart)]):
    raise Exception("Expected the start of a snippet, but instead found: '%s'."
                    % (value[start:start+len(SnippetStart)]))

  endOfName = value.find("}", start)
  if (endOfName == -1):
    raise Exception("Cannot find end of the name of the snippet. Snippet: '%s'." 
                    % (value[start:start+50]))
  name = value[start + len(SnippetStart) : endOfName]
  
  startOfContent = value.find("{", endOfName)
  if (startOfContent == -1):
    raise Exception("Cannot find the start of the content of the snippet. Snippet: '%s'." 
                    % (value[start:start+50]))
  # The content starts at the character after the '{'
  startOfContent += 1

  endOfContent = value.find(SnippetEnd, startOfContent)
  if (endOfContent == -1):
    raise Exception("Cannot find the end of the content of the snippet. Snippet: '%s'." 
                    % (value[start:start+50]))

  content = value[startOfContent:endOfContent]
  content = removeComments(content)
  content = content.replace("\\begin{isabelle}", "")
  content = content.replace("\\end{isabelle}", "")
  content = removeCommand(content, "isa", removeArgument=False)
  content = " ".join([x.strip() for x in content.splitlines() if x.strip() != ""])
  logicalLines = [x.strip() for x in content.split("\isanewline")]
  snippetLines = [parseSnippetLine(l) for l in logicalLines]

  return Snippet(name, snippetLines)

# Testing parseCodeGenComment
testContent = \
"""\\DefineSnippet{test-snippet}{%
%
%%
Line1 \isanewline
Line2 \isanewline
Line3
%
}%EndSnippet
Foo bar baz"""
testSnippet = parseSnippet(testContent, 0)
assertEqual("test-snippet", testSnippet.name)
assertEqual(3, len(testSnippet.lines))
assertEqual("Line1", testSnippet.lines[0].line)
assertEqual("Line2", testSnippet.lines[1].line)
assertEqual("Line3", testSnippet.lines[2].line)
# End of test
 
def getSnippets(content):
  snippets = []
  end = 0
  while True:
    index = content.find(SnippetStart, end)
    if (index == -1):
      break
    snippets.append(parseSnippet(content, index))
    # This suffices, but could be done in a smarter way
    end = index + 1
  return snippets

def transformLogicalLine(snippetLine, tabular, isFirst, isLast, snippet):
  result = ""
  if (tabular and snippet.hasLabels):
    result += "\AddSnippetLineNumber{} "
    if (snippetLine.hasLabel):
      result += "\\label{ln:%s:%s} " % (snippet.name, snippetLine.labelName)
    result += "& "
  result += "\\SnippetLine{"
  result += snippetLine.line
  result += "}"
  if isLast:
    # result += " &"
    result += "%"
  else:
    result += "\\\\"
  result += "\n"
  return result

def transformSnippet(snippet):
  if (snippet.hasLabels):
    tabular = True
    columnLayout = "@{}l@{}l@{}"
  elif (len(snippet.lines) > 1):
    tabular = True
    columnLayout = "@{}l@{}"
  else:
    tabular = False
  result = ""
  result += SnippetStart
  result += snippet.name
  result += "}{%\n"
  if (tabular and snippet.hasLabels):
    result += "\\setcounter{SnippetLineNumber}{0}%\n"
  if (tabular):
    result += "\\begin{tabular}{%s}%%\n" % columnLayout
  for i in range(0, len(snippet.lines)):
    line = snippet.lines[i]
    isFirst = (i == 0)
    isLast = (i == len(snippet.lines) - 1)
    result += transformLogicalLine(line, tabular, isFirst, isLast, snippet)
  if (tabular):
    result += "\\end{tabular}%%\n"
  result += SnippetEnd
  result += "\n\n"
  return result

def getTransformedSnippets(content):
  snippets = getSnippets(content)
  result = ""
  for snippet in snippets:
    result += transformSnippet(snippet)
  return result

def sanitiseCommandName(name):
  name = name.replace("_", "-")
  name = name.replace("0", "zero")
  name = name.replace("1", "one")
  name = name.replace("2", "two")
  name = name.replace("3", "three")
  name = name.replace("4", "four")
  name = name.replace("5", "five")
  name = name.replace("6", "six")
  name = name.replace("7", "seven")
  name = name.replace("8", "eight")
  name = name.replace("9", "nine")
  return name

def generateTextCommand(name, format):
  result = ""
  result += "\\newcommand{\\text%s}{%s}\n" % (sanitiseCommandName(name), name)
  result += "\\newcommand{\\math%s}{\\mathit{\\%s{%s}}}\n" % \
            (sanitiseCommandName(name), format, name)
  result += "\n"
  return result

def generateTextCommands():
  result = ""
  for constructor in constructors:
    result += generateTextCommand(constructor.name, "IsaConstructor")
  for field in fields:
    result += generateTextCommand(field.name, "IsaField")
  for definition in definitions:
    result += generateTextCommand(definition.name, "IsaDefinition")
  for lemma in lemmas:
    result += ""
  return result

def copyAndTransformSnippets(filename, newFilename):
  now = datetime.datetime.now()
  todayFormatted = now.strftime("%d-%m-%Y")
  with open (filename, "r") as myFile:
    contents = myFile.read()
  newContents = "%% Generated on %s\n" % todayFormatted
  newContents += "\n"
  newContents += generateTextCommands()
  newContents += getTransformedSnippets(contents)
  with open (newFilename, "w") as myFile:
    myFile.write(newContents)
