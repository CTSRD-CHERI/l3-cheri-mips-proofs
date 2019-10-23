from Testing import assertEqual

# This is a poor man's version of an Isabelle parser. If the beginning of a line is a keyword it
# searches for the next line that starts with a keyword and treats everything in between as a 
# 'token'. This works well enough for our purposes. 

# alphanumeric characters and characters in specialChars are allowed
def getFirstWord(value, specialChars = []):
  length = len(value)
  for i in range(len(value)):
    char = value[i]
    if not (char.isalnum() or char in specialChars):
      length = i
      break
  return value[:length]
      
# Testing getFirstWord
assertEqual("", getFirstWord(""))
assertEqual("", getFirstWord("  bla blah"))
assertEqual("bla", getFirstWord("bla bla bla"))
assertEqual("bla2", getFirstWord("bla2 bla bla"))
assertEqual("foo_bar'baz", getFirstWord("foo_bar'baz blah", ["_", "'"]))
assertEqual("foo", getFirstWord("foo: bar baz"))
# End of test

# # Returns the index of the closing bracket
# def getClosingBracket(value, index, openingBracket, closingBracket):
#   if not (value[index] == openingBracket):
#      raise Exception("Value[index] equals %s, which is not an opening bracket %s." % \
#                      (value[index], openingBracket))
#   depth = 0
#   for i in range(index, len(value)):
#     char = value[i]
#     if (char == openingBracket):
#       depth += 1
#     elif (char == closingBracket):
#       depth -= 1
#     if (depth == 0):
#       return i
#   return -1  
#       
# # Testing getClosingBracket
# assertEqual(1, getClosingBracket("()", 0, "(", ")"))
# assertEqual(-1, getClosingBracket("(", 0, "(", ")"))
# assertEqual(2, getClosingBracket("( )", 0, "(", ")"))
# assertEqual(3, getClosingBracket("(())", 0, "(", ")"))
# assertEqual(-1, getClosingBracket("(()", 0, "(", ")"))
# assertEqual(7, getClosingBracket("{([]){}}", 0, "{", "}"))
# # End of test

proofKeywords = \
  ["using", 
   "unfolding", 
   "apply", 
   "by", 
   "proof", 
   "oops", 
   "sorry"]

keywords = list(proofKeywords)
keywords.extend(
  ["datatype",
   "type_synonym",
   "record",
   "definition",
   "fun",
   "function",
   "abbreviation",
   "lemma",
   "proposition",
   "theorem",
   "schematic_goal",
   "inductive_set",
   "method",
   "instantiation",
   "instance",
   "interpretation",
   "named_theorems", 
   "consts",
   "code_printing",
   "lemmas",
   "section",
   "subsection",
   "subsubsection",
   "paragraph",
   "text",
   "text_raw", 
   "thm",
   "value",
   "find_theorems",
   "declare",
   "theory", 
   "imports",
   "begin",
   "end",
   "(*<*)",
   "(*>*)"])

class Token:

  def __init__(self, lines, keyword, name = "", remainder = ""):

    self.lines = lines
    self.keyword = keyword
    self.name = name
    self.remainderOfFirstLine = remainder

def getTokens(lines):
  start = 0
  keyword = ""
  name = ""
  remainder = ""
  commentLevel = 0
  tokens = []
  for i in range(len(lines)):
    line = lines[i]
    if (commentLevel == 0):
      # We should not overwrite start, keyword, name and remainder before we know
      # it is a token (i.e. the first word is a keyword). Hence we use the new
      # variables trimmed and firstWord.
      trimmed = line.lstrip()
      firstWord = getFirstWord(trimmed, ["_", "(", ")", "<", ">", "*"])
      if (firstWord in keywords):
        if (i > 0):
          # The previous token is finished
          token = Token(lines[start:i], keyword, name, remainder)
          tokens.append(token)
        start = i
        keyword = firstWord
        remainder = trimmed[len(keyword):].lstrip()
        name = getFirstWord(remainder, ["_", "'"])
        remainder = remainder[len(name):]
    commentLevel += line.count("(*")
    commentLevel -= line.count("*)")
    if (commentLevel < 0):
      raise Exception ("Line %i: comment level became negative." % i)
  # The last token
  if (len(lines) > 0):
    token = Token(lines[start:len(lines)], keyword, name, remainder)
    tokens.append(token)
  return tokens
      
# Testing getTokens
testTokens = getTokens([])
assertEqual(0, len(testTokens))
testTokens = getTokens(["lemma"])
assertEqual(1, len(testTokens))
assertEqual(1, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("", testTokens[0].name)
assertEqual("", testTokens[0].remainderOfFirstLine)
testTokens = getTokens(["lemma foo"])
assertEqual(1, len(testTokens))
assertEqual(1, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("foo", testTokens[0].name)
assertEqual("", testTokens[0].remainderOfFirstLine)
testTokens = getTokens(["  lemma  foo  "])
assertEqual(1, len(testTokens))
assertEqual(1, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("foo", testTokens[0].name)
assertEqual("  ", testTokens[0].remainderOfFirstLine)
testTokens = getTokens(["lemma foo'def2: blah [baz]"])
assertEqual(1, len(testTokens))
assertEqual(1, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("foo'def2", testTokens[0].name)
assertEqual(": blah [baz]", testTokens[0].remainderOfFirstLine)
testTokens = getTokens(["lemma foo", "blah", "blah"])
assertEqual(1, len(testTokens))
assertEqual(3, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("foo", testTokens[0].name)
assertEqual("", testTokens[0].remainderOfFirstLine)
testTokens = getTokens(["lemma foo", "blah", "blah", "type_synonym baz blah", "blah"])
assertEqual(2, len(testTokens))
assertEqual(3, len(testTokens[0].lines))
assertEqual("lemma", testTokens[0].keyword)
assertEqual("foo", testTokens[0].name)
assertEqual("", testTokens[0].remainderOfFirstLine)
assertEqual(2, len(testTokens[1].lines))
assertEqual("type_synonym", testTokens[1].keyword)
assertEqual("baz", testTokens[1].name)
assertEqual(" blah", testTokens[1].remainderOfFirstLine)
testTokens = getTokens(["not_a_keyword foo", "blah", "blah", "type_synonym baz blah", "blah"])
assertEqual(2, len(testTokens))
assertEqual(3, len(testTokens[0].lines))
assertEqual("", testTokens[0].keyword)
assertEqual("", testTokens[0].name)
assertEqual("", testTokens[0].remainderOfFirstLine)
assertEqual(2, len(testTokens[1].lines))
assertEqual("type_synonym", testTokens[1].keyword)
assertEqual("baz", testTokens[1].name)
assertEqual(" blah", testTokens[1].remainderOfFirstLine)
testTokens = getTokens(["(*", "definition foo", "definition bar", "type_synonym baz blah", "*)"])
assertEqual(1, len(testTokens))
assertEqual("", testTokens[0].keyword)
assertEqual("", testTokens[0].name)
# End of test

class TokenWithProof(Token):
  
  def __init__(self, lines, keyword, name = "", remainder = "", proofLines = []):
    Token.__init__(self, lines, keyword, name, remainder)
    self.proofLines = proofLines

def getTokenWithProofFromToken(token, proofTokens):
  proofLines = []
  for proofToken in proofTokens:
    proofLines.extend(proofToken.lines)
  tokenWithProof = TokenWithProof(token.lines,
                                  token.keyword,
                                  token.name,
                                  token.remainderOfFirstLine,
                                  proofLines)
  return tokenWithProof

def getTokensWithProof(lines):
  tokensWithProof = []
  tokens = getTokens(lines)
  lastNonProofToken = None
  proofTokens = None
  for i in range(len(tokens)):
    token = tokens[i]
    if token.keyword in proofKeywords:
      if lastNonProofToken is None:
        raise Exception("The lines cannot start with a proof.")
      proofTokens.append(token)
    else:
      if not lastNonProofToken is None:
        tokenWithProof = getTokenWithProofFromToken(lastNonProofToken, proofTokens)
        tokensWithProof.append(tokenWithProof)
      lastNonProofToken = token
      proofTokens = []
  # The last token
  if not lastNonProofToken is None:
    tokenWithProof = getTokenWithProofFromToken(lastNonProofToken, proofTokens)
    tokensWithProof.append(tokenWithProof)
  return tokensWithProof

