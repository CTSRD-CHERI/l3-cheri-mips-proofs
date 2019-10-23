from Testing import assertEqual
from GenerateSnippets import generateFile
from TransformSnippets import copyAndTransformSnippets
import subprocess
import os.path

isaFilenames = ["SecurityPropertiesReadable.thy"]
texFilenames = ["SecurityPropertiesReadable.tex"]

def buildIsabelle(session = None, directory = None, quickAndDirty = True):
  command = ["isabelle", "build"]
  if quickAndDirty:
    command.extend(["-o", "quick_and_dirty"])
  if (not directory is None):
    command.extend(["-D", directory])
  if (not session is None):
    command.append(session)
  # Assumes there is a root file that tells isabelle how to build stuff
  subprocess.check_output(command)

for filename in isaFilenames:
  generateFile(filename)

buildIsabelle(directory = ".")

for filename in texFilenames:
  prefix, extension = os.path.splitext(filename)
  newFilename = prefix + "Snippets" + extension
  copyAndTransformSnippets("output/document/" + filename, "output/document/" + newFilename)