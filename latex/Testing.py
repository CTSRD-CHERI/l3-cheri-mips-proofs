def assertEqual(expected, actual, message = ""):
  if (expected != actual):
    raise Exception("AssertEqual failed: %s != %s. %s"
                    % (str(expected), str(actual), message))