# Author: Kyndylan Nienhuis

# Raises an exception is "actual" is not equal to "expected"
def assertEqual(expected, actual, message = ""):
  if (expected != actual):
    raise Exception("AssertEqual failed: %s != %s. %s"
                    % (str(expected), str(actual), message))

# Assumes that "left" and "right" are lists without duplicates, and returns their concatenation
# with duplicates removed. "left" and "right are unchanged.
def extendNoDuplicates(left, right):
  # "result" cannot be initialised as "left" (or "right" for that matter), because
  # then we would change "left" (or "right"). 
  result = []
  result.extend(left)
  for value in right:
    if value not in left:
      result.append(value)
  return result

# Zero based means the first line is line 0
def zeroBasedLineNumber(value, index):
  return value.count("\n", 0, index)

# Testing lineNumberFromIndex
assertEqual(0, zeroBasedLineNumber("foo", 0))
assertEqual(0, zeroBasedLineNumber("foo", 1))
assertEqual(0, zeroBasedLineNumber("foo", 2))
# Note that newlines themselves also have an index, so below every line consists
# of 10 characters. 
testString = \
"""012345678
012345678
012345678
012345678
"""
assertEqual(0, zeroBasedLineNumber(testString, 0))
assertEqual(0, zeroBasedLineNumber(testString, 9))
assertEqual(1, zeroBasedLineNumber(testString, 10))
assertEqual(1, zeroBasedLineNumber(testString, 19))
assertEqual(2, zeroBasedLineNumber(testString, 20))
assertEqual(2, zeroBasedLineNumber(testString, 29))
# End of test