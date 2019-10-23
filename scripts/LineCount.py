# Author: Kyndylan Nienhuis

from LineCountBase import \
  countNonEmptyNonCommentLines, \
  countNonEmptyNonCommentLinesInDir
from CodeGenBase import IsaFile
from Utilities import assertEqual
import re
import os

def countNonEmptyNonCommentIsaLines(lines):
  return countNonEmptyNonCommentLines(lines, "(*", "*)")

def nonGeneratedLinesOfIsaFile(isaFile):
  lines = []
  for part in isaFile.parts:
    if (type(part) is str):
      lines.extend(part.splitlines(True))
    else:
      for fun in part.overrides:
        lines.extend(part.overrides[fun].splitlines(True))
  return lines

# Returns a pair (number of manual lines, number of generated lines)
def countIsaLinesOfFile(filename):

  with open (filename, "r") as myFile:
    fileContents = myFile.read()

  lines = fileContents.splitlines(True)
  totalNumberOfLines = countNonEmptyNonCommentIsaLines(lines)

  if (totalNumberOfLines < 0):
    raise Exception("Total number of lines can't be negative.")

  isaFile = IsaFile(fileContents)
  manualLines = nonGeneratedLinesOfIsaFile(isaFile)
  numberOfManualLines = countNonEmptyNonCommentIsaLines(manualLines)

  if (numberOfManualLines < 0):
    raise Exception("Number of manual lines can't be negative.")
  if (totalNumberOfLines < numberOfManualLines):
    raise Exception("Total number of lines can't be less than the number of manual lines.")

  return (numberOfManualLines, totalNumberOfLines - numberOfManualLines)

# Returns a pair (number of manual lines, number of generated lines)
def countIsaLinesOfDir(directory, wildcard):

  totalManualLines = 0
  totalGeneratedLines = 0

  for item in os.listdir(directory):
    path = os.path.join(directory, item)
    if (os.path.isdir(path)):
      # Subdirectory
      (manual, generated) = countIsaLinesOfDir(path, wildcard)
      totalManualLines += manual
      totalGeneratedLines += generated
    elif re.match(wildcard, item):
      # File that matches the wildcard
      try:
        (manual, generated) = countIsaLinesOfFile(path)
      except Exception as ex:
        raise Exception("Exception while processing file '%s'." % path) from ex
      totalManualLines += manual
      totalGeneratedLines += generated
      # Debug:
      print ("%s: %i %i" % (path, manual, generated))

  # Debug:
  print ("%s: %i %i" % (directory, totalManualLines, totalGeneratedLines))

  return (totalManualLines, totalGeneratedLines)

countIsaLinesOfDir(".", ".*\.thy$")

# print ("All L3 files: %i" % \
#   countNonEmptyNonCommentLinesInDir("/auto/homes/kn307/github/l3mips/", ".*\.spec$", "{-", "-}"))