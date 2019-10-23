# Author: Kyndylan Nienhuis

import re
import os
from Utilities import assertEqual

# Returns a pair (lineWithoutComments, newDepth)
def getNonCommentAndNewDepth(line, depth, startToken, endToken):

  if (depth < 0):
    raise Exception("Depth cannot be negative")
  
  startTokenIndex = line.find(startToken)
  endTokenIndex = line.find(endToken)

  if (startTokenIndex == -1 and endTokenIndex == -1):
    nonCommentLine = (line if (depth == 0) else "")
    return (nonCommentLine, depth)

  elif (startTokenIndex > -1 and (endTokenIndex == -1 or endTokenIndex > startTokenIndex)):
    nonCommentStart = (line[:startTokenIndex] if (depth == 0) else "")
    remainingLine = line[startTokenIndex + len(startToken):]
    (nonCommentRemaing, newDepth) = \
      getNonCommentAndNewDepth(remainingLine, depth + 1, startToken, endToken)
    return (nonCommentStart + nonCommentRemaing, newDepth)

  elif (endTokenIndex > -1 and (startTokenIndex == -1 or startTokenIndex > endTokenIndex)):
    if (depth == 0):
      raise Exception("Cannot end comment when depth is already 0") 
    remainingLine = line[endTokenIndex + len(endToken):]
    return getNonCommentAndNewDepth(remainingLine, depth - 1, startToken, endToken)

  else:
    raise Exception("This cannot happen")

# Testing parseCodeGenComment
assertEqual(("bla", 0), getNonCommentAndNewDepth("bla", 0, "(*", "*)"))
assertEqual(("", 1), getNonCommentAndNewDepth("bla", 1, "(*", "*)"))
assertEqual(("", 0), getNonCommentAndNewDepth("(* bla *)", 0, "(*", "*)"))
assertEqual(("foo  bar", 0), getNonCommentAndNewDepth("foo (* bla *) bar", 0, "(*", "*)"))
assertEqual(("", 1), getNonCommentAndNewDepth("foo (* bla *) bar", 1, "(*", "*)"))
assertEqual(("", 0), getNonCommentAndNewDepth("foo *)", 1, "(*", "*)"))
assertEqual(("", 1), getNonCommentAndNewDepth("(* foo", 0, "(*", "*)"))
assertEqual((" bla ", 0), getNonCommentAndNewDepth("(* foo *) bla (* bar *)", 0, "(*", "*)"))
assertEqual(("az", 0), getNonCommentAndNewDepth("a(* foo (* bla *) bar *)z", 0, "(*", "*)"))
# End of test

def removeCommentsAndEmptyLines(lines, startToken, endToken):

  depth = 0
  result = []

  for i in range(0, len(lines)):
    line = lines[i]
    try:
      (nonCommentLine, depth) = getNonCommentAndNewDepth(line, depth, startToken, endToken)
    except Exception as ex:
      raise Exception("Exception while processing line %i." % i) from ex
    trimmedNonCommentLine = nonCommentLine.strip()
    if (trimmedNonCommentLine != ""):
      result.append(nonCommentLine)

  return result

# Testing removeCommentsAndEmptyLines
assertEqual(0, len(removeCommentsAndEmptyLines([" "], "(*", "*)")))
assertEqual(1, len(removeCommentsAndEmptyLines(["b"], "(*", "*)")))
assertEqual(0, len(removeCommentsAndEmptyLines([" (* bla *) "], "(*", "*)")))
assertEqual(1, len(removeCommentsAndEmptyLines([" (* bla *) foo"], "(*", "*)")))
assertEqual(0, len(removeCommentsAndEmptyLines([" (* ", "b", "*)"], "(*", "*)")))
# End of test

def countNonEmptyNonCommentLines(lines, startToken, endToken):
  return len(removeCommentsAndEmptyLines(lines, startToken, endToken))

def countNonEmptyNonCommentLinesinFile(fileName, startToken, endToken):
  with open (fileName, "r") as myFile:
    lines = myFile.readlines()
  return countNonEmptyNonCommentLines(lines, startToken, endToken)

def countNonEmptyNonCommentLinesInDir(directory, wildcard, startToken, endToken):

  totalCount = 0
  count = 0

  for item in os.listdir(directory):
    path = os.path.join(directory, item)
    if (os.path.isdir(path)):
      # Subdirectory
      totalCount += countNonEmptyNonCommentLinesInDir(path, wildcard, startToken, endToken)
    elif re.match(wildcard, item):
      # File that matches the wildcard
      count = countNonEmptyNonCommentLinesinFile(path, startToken, endToken)
      # print ("%s: %i" % (path, count))
      totalCount += count

  return totalCount
