# Author: Kyndylan Nienhuis

from Utilities import assertEqual

stateComponents = [
  ("BranchDelayPCC", []),
  ("BranchToPCC", []),
  ("JTAG_UART", []),
  ("PIC_base_address", []),
  ("PIC_config_regs", []),
  ("PIC_external_intrs", []),
  ("PIC_ip_bits", []),
  ("UNPREDICTABLE_HI", []),
  ("UNPREDICTABLE_LO", []),
  ("UNPREDICTABLE_TLB", []),
  ("all_BranchDelayPCC", []),
  ("all_BranchToPCC", []),
  ("all_TLB_assoc", []),
  ("all_TLB_direct", []),
  ("all_capcause", []),
  ("all_capr", []),
  ("all_gpr", []),
  ("all_pcc", []),
  ("all_scapr", []),
  ("all_state", []),
  ("c_TLB_assoc", []),
  ("c_TLB_direct", []),
  ("c_capr", []),
  ("c_gpr", []),
  ("c_pcc", []),
  ("c_scapr", []),
  ("c_state", [
    ("c_BranchDelay", []),
    ("c_BranchTo", []),
    ("c_CP0", [
      ("BadInstr", []),
      ("BadInstrP", []),
      ("BadVAddr", []),
      ("Cause", [
        ("BD", []),
        ("CE", []),
        ("CauseRegister.ExcCode", []),
        ("IP", []),
        ("TI", []),
        ("causeregister'rst", [])]),
      ("Compare", []),
      ("Config", [
        ("AR", []),
        ("AT", []),
        ("BE", []),
        ("K0", []),
        ("ConfigRegister.M", []),
        ("ConfigRegister.MT", []),
        ("configregister'rst", [])]),
      ("Config1", []),
      ("Config2", []),
      ("Config3", []),
      ("Config6", []),
      ("Context", [
        ("Context.BadVPN2", []),
        ("Context.PTEBase", []),
        ("context'rst", [])]),
      ("Count", []),
      ("Debug", []),
      ("EPC", []),
      ("EntryHi", [
        ("EntryHi.ASID", []),
        ("EntryHi.R", []),
        ("EntryHi.VPN2", []),
        ("entryhi'rst", [])]),
      ("EntryLo0", []),
      ("EntryLo1", []),
      ("ErrCtl", []),
      ("ErrorEPC", []),
      ("HWREna", []),
      ("Index", []),
      ("LLAddr", []),
      ("PRId", []),
      ("PageMask", []),
      ("Random", [
        ("Random.Random", []),
        ("random'rst", [])]),
      ("Status", [
        ("BEV", []),
        ("CU0", []),
        ("CU1", []),
        ("CU2", []),
        ("CU3", []),
        ("ERL", []),
        ("EXL", []),
        ("FR", []),
        ("IE", []),
        ("IM", []),
        ("KSU", []),
        ("KX", []),
        ("StatusRegister.RE", []),
        ("SX", []),
        ("UX", []), 
        ("statusregister'rst", [])]),
      ("UsrLocal", []),
      ("Wired", [
        ("Wired.Wired", []),
        ("wired'rst", [])]),
      ("XContext", [
        ("XContext.BadVPN2", []),
        ("XContext.PTEBase", []),
        ("XContext.R", []),
        ("xcontext'rst", [])])]),
    ("c_CoreStats", [
      ("branch_not_taken", []),
      ("branch_taken", [])]),
    ("c_LLbit", []),
    ("c_PC", []),
    ("c_exceptionSignalled", []),
    ("c_hi", []),
    ("c_lo", [])]),
  ("capcause", []),
  ("csv_stats_header_done", []),
  ("currentInst", []),
  ("done", []),
  ("dynamicMemStats", []),
  ("dynamic_shadow_16K_TAGS", []),
  ("dynamic_shadow_4K_MEM", []),
  ("dynamic_shadow_4K_TAGS", []),
  ("dynamic_shadow_MEM", []),
  ("dynamic_shadow_TAGS", []),
  ("exception", []),
  ("hasCP1", []),
  ("hasCP2", []),
  ("instCnt", []),
  ("lastInst", []),
  ("log", []),
  ("memAccessStats", []),
  ("print", []),
  ("procID", []),
  ("staticMemStats", []),
  ("static_shadow_16K_TAGS", []),
  ("static_shadow_4K_MEM", []),
  ("static_shadow_4K_TAGS", []),
  ("static_shadow_MEM", []),
  ("static_shadow_TAGS", []),
  ("the_MEM", []),
  ("totalCore", []),
  ("trace_level", []),
  ("unknown_counters", []),
  ("watchOOBCap", []),
  ("watchPaddr", []),
  ("watcher", [])]

def tryFindComponentsIn(name, values):
  result = []
  for v in values:
    if (v[0] == name):
      result.append(v)
    result.extend(tryFindComponentsIn(name, v[1]))
  return result

def findComponent(name):
  found = tryFindComponentsIn(name, stateComponents)
  if (len(found) == 0):
    raise Exception("Cannot find state component %s." % name)
  elif (len(found) > 1):
    raise Exception("Found multiple state components %s." % name)
  return found[0]

# Testing findComponent
# We just test whether the invocations do not return an error
findComponent("c_gpr")
findComponent("c_CP0")
findComponent("ErrorEPC")
# End of test 

# left and right are list of strings
def stateComponentsConflict(left, right):
  sharedLength = min(len(left), len(right))
  result = True
  for i in range(0, sharedLength):
    if (left[i] != right[i]):
      result = False
  return result

# Testing stateComponentsConflict
assertEqual(False, stateComponentsConflict(["foo"], ["bar"]))
assertEqual(True, stateComponentsConflict(["bar"], ["bar"]))
assertEqual(True, stateComponentsConflict(["bar", "blah"], ["bar"]))
assertEqual(False, stateComponentsConflict(["bar", "blah"], ["bar", "foo"]))
assertEqual(True, stateComponentsConflict([], ["bar", "foo"]))
# End of test

# Returns None if the result cannot be determined
# Reads and writes are None or a list of lists of strings
def stateComponentListsConflict(reads, writes):
  if (writes is None and reads is None):
    # 'Writes' and 'reads' cannot both be None
    return None
  elif (writes == [] or reads == []):
    # Here it's fine if the other is None
    return False
  elif (writes is None or reads is None):
    # If either 'reads' or 'writes' is non-empty, then the other cannot be None
    return None
  else:
    conflict = False
    for read in reads:
      for write in writes:
        conflict = conflict or stateComponentsConflict(read, write)
    return conflict

# Testing stateComponentListsConflict
assertEqual(None, stateComponentListsConflict(None, None))
assertEqual(False, stateComponentListsConflict([], None))
assertEqual(False, stateComponentListsConflict(None, []))
assertEqual(None, stateComponentListsConflict(None, [["foo"]]))
assertEqual(None, stateComponentListsConflict([["foo"]], None))
assertEqual(False, stateComponentListsConflict([["foo"]], [["bar"]]))
assertEqual(True, stateComponentListsConflict([["baz"], ["foo"]], [["bar"], ["foo"]]))
assertEqual(False, stateComponentListsConflict([["baz"], ["foo", "blah"]], [["bar"], ["foo", "booh"]]))
# End of test

def stateComponentComplement_aux(values, prefix, subcomponents):
  # 'values' is a list of components (a list of lists of strings)
  # 'prefix' is a component (a list of strings)
  # 'subcomponents' is a list of (string \times subcomponents)
  if (values is None):
    raise Exception("values are None")
  # 'result' is a list of components
  result = []
  for subcomponent in subcomponents:
    fullcomponent = prefix + [subcomponent[0]]
    if not stateComponentListsConflict([fullcomponent], values):
      result.append(fullcomponent)
    else:
      newPrefix = fullcomponent
      newSubcomponents = subcomponent[1]
      result.extend(stateComponentComplement_aux(values, newPrefix, newSubcomponents))
  return result

# Returns all the accessors that are conflict free with values
def stateComponentComplement(values):
  return stateComponentComplement_aux(values, [], stateComponents)

# Testing stateComponentComplement
assertEqual(False, ["c_pcc"] in stateComponentComplement([["c_pcc"]]))
assertEqual(True, ["c_gpr"] in stateComponentComplement([["c_pcc"]]))
assertEqual(False, ["c_state"] in stateComponentComplement([["c_state", "c_hi"]]))
assertEqual(False, ["c_state", "c_hi"] in stateComponentComplement([["c_state", "c_hi"]]))
assertEqual(True, ["c_state", "c_lo"] in stateComponentComplement([["c_state", "c_hi"]]))
# End of test

# The following function assumes that no item in 'left' 
# conflicts with another item in 'left' and similarly for 
# 'right'. 
#
# It returns the list of items in 'left' that either do not 
# conflict with any item in 'right', or that are at least as general
# as the items in 'right' with which it conflicts. More general
# means a shorter component list, so ["bar"] is more general 
# than ["bar", "foo"].
def combineStateComponents_aux(left, right):
  result = []
  for value1 in left:
    conflictingValues = []
    for value2 in right:
      if stateComponentsConflict(value1, value2):
        conflictingValues.append(value2)
    if (len(conflictingValues) == 0):
      # value1 does not conflict with any item in 'right'
      result.append(value1)
    elif (len(conflictingValues) == 1):
      if (len(value1) <= len(conflictingValues[0])):
        # value1 is at least as general as value2
        result.append(value1)
    else:
      # In this case value1 conflicts with multiple items
      # i_0, ..., i_n in 'right'. Since we assume that no item in 'right'
      # conflicts with another item in 'right', we know that i_0, ..., i_n
      # don't conflict each other. Because they all conflict value1, this 
      # means that value1 is more general. 
      result.append(value1)
  return result

# The following function assumes that no item in 'left' 
# conflicts with another item in 'left' and similarly for 
# 'right'. 
def combineStateComponents(left, right):
  if (left is None):
    raise Exception("'left' is None")
  if (right is None):
    raise Exception("'right' is None")
  left_filtered = combineStateComponents_aux(left, right)
  right_filtered = combineStateComponents_aux(right, left)
  # Because these list might contain the same value, we 
  # check for duplicates. 
  result = []
  result.extend(left_filtered)
  for value in right_filtered:
    if value not in left_filtered:
      result.append(value)
  return result

# Testing combineStateComponents
assertEqual([], combineStateComponents([], []))
assertEqual([["bar"]], combineStateComponents([], [["bar"]]))
assertEqual([["bar"]], combineStateComponents([["bar"]], []))
assertEqual([["bar"]], combineStateComponents([["bar"]], [["bar"]]))
assertEqual([["bar"], ["foo"]], combineStateComponents([["bar"]], [["foo"]]))
assertEqual([["bar"]], combineStateComponents([["bar"]], [["bar", "baz"]]))
assertEqual([["bar"]], combineStateComponents([["bar", "baz"]], [["bar"]]))
assertEqual([["bar"]], combineStateComponents([["bar", "baz"], ["bar", "foo"]], [["bar"]]))
# End of test

def applyComponents(components, argument):
  if (components == []):
    return argument
  elif (len(components) == 1):
    return "%s %s" % (components[0], argument)
  else:
    return applyComponents(components[1:], "(%s %s)" % (components[0], argument))

# Testing applyComponents
assertEqual("s", applyComponents([], "s"))
assertEqual("foo s", applyComponents(["foo"], "s"))
assertEqual("bar (foo s)", applyComponents(["foo", "bar"], "s"))
assertEqual("baz (bar (foo s))", applyComponents(["foo", "bar", "baz"], "s"))
# End of test

def applyComponentUpdates(components, argument = None):
  if (components == []):
    return ""
  elif (len(components) == 1):
    if (argument is None):
      argument = "x_" + components[0]
    return "%s_update %s" % (components[0], argument)
  else:
    return "%s_update (%s)" % (components[0], applyComponentUpdates(components[1:], argument))

# Testing applyComponentUpdates
assertEqual("", applyComponentUpdates([], "x"))
assertEqual("foo_update x", applyComponentUpdates(["foo"], "x"))
assertEqual("foo_update (bar_update x)", applyComponentUpdates(["foo", "bar"], "x"))
assertEqual("foo_update (bar_update (baz_update x))", 
            applyComponentUpdates(["foo", "bar", "baz"], "x"))
assertEqual("foo_update (bar_update (baz_update x_baz))", 
            applyComponentUpdates(["foo", "bar", "baz"]))
# End of test