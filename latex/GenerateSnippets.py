# Hack to make the other python files visible
import sys
sys.path.insert(0, '../scripts')

from shutil import copyfile
from Testing import assertEqual
from PoorMansParser import Token, getTokens
from CodeGenBase import CodeGenComment, findCodeGenCommentPairs, codeGenCommentToString
from IsaMetaInfo import *

CodeGenCommentStart = "snippets"
CodeGenCommentEnd = "end snippets"

def getSnippetName(name):
  # return "isa_" + name
  # return "isa-" + name.replace("_", "-")
  return name.replace("_", "-")

def generateTextCommand(name):
  result = ""
  result += "text_raw \\<open>\\newcommand{\\text%s}{%s}\\<close>\n" % (name, name)
  result += "\n"
  return result

def generateThmSnippet(snippetName, theoremName, inline, margin):
  # TODO: do something with inline
  result = ""
  result += "text_raw \\<open>\n"
  result += "\\DefineSnippet{%s}{%%\n" % (getSnippetName(snippetName))
  result += "@{thm [display, margin = %i] %s}\n" % (margin, theoremName)
  result += "}%EndSnippet\\<close>\n"
  result += "\n"
  return result

def generateTypeOfSnippet(snippetName, expression):
  result = ""
  result += "text_raw \\<open>\n"
  result += "\\DefineSnippet{%s}{%%\n" % (getSnippetName(snippetName))
  result += "@{typeof \"%s\"}\n" % expression
  result += "}%EndSnippet\\<close>\n"
  result += "\n"
  return result

def generateConstructorSyntax(constructorInfo):
  result = ""
  result += "syntax (latex output) \"_%s\" :: 'a (\"%s\")\n" % \
             (constructorInfo.name, constructorInfo.name)
  result += "translations \"(CONST IsaConstructor _%s)\" \<leftharpoondown> \"CONST %s.%s\"\n" % \
             (constructorInfo.name, constructorInfo.constructedType, constructorInfo.originalName)
  result += "\n"
  return result

def generateFieldSyntax(name):
  result = ""
  result += "syntax (latex output) \"_%s\" :: 'a (\"%s\")\n" % (name, name)
  result += "translations \"(CONST IsaField _%s)\" \<leftharpoondown> \"CONST %s\"\n" % (name, name)
  result += "\n"
  return result

def generateDefinitionSyntax(name):
  result = ""
  result += "syntax (latex output) \"_%s\" :: 'a (\"%s\")\n" % (name, name)
  result += "translations \"(CONST IsaDefinition _%s)\" \<leftharpoondown> \"CONST %s\"\n" % (name, name)
  result += "\n"
  return result

def generateSnippet(name, lemma):
  result = ""
  result += "text_raw \\<open>\n"
  result += "\\DefineSnippet{%s}{%%\n" % getSnippetName(name)
  result += "@{thm [display, margin = %i] %s}\n" % (margin, lemma)
  result += "}%EndSnippet\\<close>\n"
  result += "\n"
  return result

def generateSnippets(content):
  result = ""
  for constructor in constructors:
    result += generateConstructorSyntax(constructor)
    result += generateTypeOfSnippet(constructor.name + "-type", 
                                    constructor.constructedType + "." + constructor.originalName)
  for field in fields:
    result += generateFieldSyntax(field.name)
    result += generateTypeOfSnippet(field.name + "-type", field.name)
    result += generateTypeOfSnippet(field.name + "-field-type", field.name + " x")
  for definition in definitions:
    result += generateDefinitionSyntax(definition.name)
    result += generateTypeOfSnippet(definition.name + "-type", definition.name)
    if not definition.definingLemma is None:
      result += generateThmSnippet(snippetName=definition.name, 
                                   theoremName=definition.definingLemma, 
                                   inline=definition.inline, 
                                   margin=definition.margin)
  for lemma in lemmas:
    result += generateThmSnippet(snippetName=lemma.name, 
                                 theoremName=lemma.name, 
                                 inline=False, 
                                 margin=lemma.margin)    
  return result

def generateContent(content):
  commentPairs = findCodeGenCommentPairs(content, CodeGenCommentStart, CodeGenCommentEnd, 0)
  if len(commentPairs) == 0:
    return content
  elif len(commentPairs) > 1:
    raise Exception("Only one occurrence of a snippet directive is allowed.")
  else:
    startComment = commentPairs[0][0]
    endComment = commentPairs[0][1]
    result = content[0:startComment.start]
    result += codeGenCommentToString([CodeGenCommentStart])
    result += "\n\n"
    result += generateSnippets(content)
    result += codeGenCommentToString([CodeGenCommentEnd])
    result += content[endComment.startContent:len(content)]
    return result

def generateFile(fileName):

  with open (fileName, "r", newline = '') as myFile:
    fileContents = myFile.read()

  try:
    newContents = generateContent(fileContents)
  except Exception as ex:
    raise Exception("Exception while processing file '%s'." % fileName) from ex

  if (newContents != fileContents):
    tempFileName = fileName + ".temp"
    copyfile(fileName, tempFileName)    
    with open (fileName, "w", newline = '') as myFile:
      myFile.write(newContents)
    
  return
