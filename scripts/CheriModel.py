# Author: Kyndylan Nienhuis

from CodeGenBase import L3Fun, L3Component, L3File, L3Model
from CheriStateComponents \
  import stateComponentListsConflict, stateComponentComplement, combineStateComponents
from IsabelleUtils import firstLetterUpperCase
from Utilities import assertEqual, extendNoDuplicates

class L3FunExt(L3Fun):
  
  def __init__(self, name, arity = 1, 
               reads = None, writes = None, 
               dependencies = None, nextUnknownIds = []):
    L3Fun.__init__(self, name)
    # "arity" is a non-negative number
    self.arity = arity
    # "reads" is a list of list of strings denoting which components of the state the functions reads
    self.reads = reads
    # "writes" is a list of list of strings denoting which components of the state the functions writes
    self.writes = writes
    # "dependencies" is a list of strings denoting which functions this function depends on
    self.dependencies = dependencies
    # Many functions have a dependency on "next_unknown", but do not conflict with each other
    # because each invocations uses a unique parameter (and inside next_unknown a separate counter).
    # Because our handling of dependencies cannot handle this (functions that have the same 
    # dependency are treated as conflicting), we special case dependencies of next_unknown. The 
    # parameter nextUnknownIds contains the list of parameters that are used in invocations of
    # next_unknown. This list can be empty. 
    self.nextUnknownIds = nextUnknownIds
    # The following fields are set by setPreviousFunctions
    self.transitiveReads = None
    self.transitiveReadsComplement = None
    self.transitiveWrites = None
    self.transitiveWritesComplement = None
    self.transitiveDependencies = None
    self.transitiveNextUnknownIds = None

  def _transitiveReads(self):
    if (self.reads is None):
      raise Exception("Reads are None")
    if (self.dependencyFunctions is None):
      raise Exception("dependencyFunctions are None")
    result = self.reads
    for dependencyFunction in self.dependencyFunctions:
      if (dependencyFunction.transitiveReads is None):
        raise Exception("The transitive reads of %s (a dependency of %s) are None" % 
                        (dependencyFunction.name, self.name))
      result = combineStateComponents(result, dependencyFunction.transitiveReads)
    return result
  
  def _transitiveWrites(self):
    if (self.writes is None):
      raise Exception("Writes are None")
    if (self.dependencyFunctions is None):
      raise Exception("dependencyFunctions are None")
    result = self.writes
    for dependencyFunction in self.dependencyFunctions:
      if (dependencyFunction.transitiveWrites is None):
        raise Exception("The transitive writes of %s (a dependency of %s) are None" % 
                        (dependencyFunction.name, self.name))
      result = combineStateComponents(result, dependencyFunction.transitiveWrites)
    return result

  def _transitiveNextUnknownIds(self):
    if (self.nextUnknownIds is None):
      raise Exception("nextUnknownIds are None")
    if (self.dependencyFunctions is None):
      raise Exception("dependencyFunctions are None")
    result = self.nextUnknownIds
    for dependencyFunction in self.dependencyFunctions:
      if (dependencyFunction.transitiveNextUnknownIds is None):
        raise Exception("The transitive nextUnknownIds of %s (a dependency of %s) are None" % 
                        (dependencyFunction.name, self.name))
      result = extendNoDuplicates(result, dependencyFunction.transitiveNextUnknownIds)
    return result    

  def _transitiveDependencies(self):
    if (self.dependencyFunctions is None):
      raise Exception("dependencyFunctions are None")
    result = self.dependencyFunctions
    for dependencyFunction in self.dependencyFunctions:
      if (dependencyFunction.transitiveDependencies is None):
        raise Exception("The transitive dependencies of %s (a dependency of %s) are None" % 
                        (dependencyFunction.name, self.name))
      result = extendNoDuplicates(result, dependencyFunction.transitiveDependencies)
    return result

  def setPreviousFunctions(self, previousFunctions):
    L3Fun.setPreviousFunctions(self, previousFunctions)
    if (not self.dependencies is None):
      self.dependencyFunctions = [self.findFunction(d) for d in self.dependencies]
      self.transitiveDependencies = self._transitiveDependencies()
    if (not self.reads is None and not self.dependencies is None):
      self.transitiveReads = self._transitiveReads()
      self.transitiveReadsComplement = stateComponentComplement(self.transitiveReads)
    if (not self.writes is None and not self.dependencies is None):
      self.transitiveWrites = self._transitiveWrites()
      self.transitiveWritesComplement = stateComponentComplement(self.transitiveWrites)
    if (not self.nextUnknownIds is None and not self.dependencies is None):
      self.transitiveNextUnknownIds = self._transitiveNextUnknownIds()
    self.nonConflictingFunctions = [f for f in previousFunctions 
                                    if self.conflictsWith(f) == False]

  # Returns None if the result cannot be determined
  def conflictsWith(self, other):
    left = stateComponentListsConflict(self.transitiveReads, other.transitiveWrites)
    right = stateComponentListsConflict(self.transitiveWrites, other.transitiveReads)
    writes = stateComponentListsConflict(self.transitiveWrites, other.transitiveWrites)
    if (left is None or right is None or writes is None):
      return None
    else:
      return left or right or writes

# Test model
testL3Model = L3Model(
  [L3File("file0", [L3FunExt("fun0", reads = [["bar0"]], writes = [], dependencies = []), 
                    L3FunExt("fun1", reads = [], writes = [["bar0"], ["bar1"]], dependencies = []), 
                    L3FunExt("fun2")]),
   L3File("file1", [L3FunExt("fun3"), 
                    L3FunExt("fun4", reads = [], writes = [["bar1"]], dependencies = []), 
                    L3FunExt("fun5", reads = [["bar2"]], writes = [], dependencies = [])]),
   L3File("file2", [L3Component(L3FunExt("fun6", reads = [], writes = [], dependencies = ["fun0"]), 
                                L3FunExt("fun7", reads = [], writes = [["bar1"], ["bar2"]], 
                                                 dependencies = ["fun1"]))]),
   L3File("file3", [L3FunExt("fun8", reads = [], writes = [], dependencies = ["fun6", "fun7"])])])
testFun0 = testL3Model.findFunction("fun0")
testFun1 = testL3Model.findFunction("fun1")
testFun2 = testL3Model.findFunction("fun2")
testFun3 = testL3Model.findFunction("fun3")
testFun4 = testL3Model.findFunction("fun4")
testFun5 = testL3Model.findFunction("fun5")
testFun6 = testL3Model.findFunction("fun6")
testFun7 = testL3Model.findFunction("fun7")
testFun8 = testL3Model.findFunction("fun8")
# Testing transitiveReads and transitiveWrites
assertEqual([["bar0"]], testFun0.transitiveReads)
assertEqual([], testFun0.transitiveWrites)
assertEqual([], testFun1.transitiveReads)
assertEqual([["bar0"], ["bar1"]], testFun1.transitiveWrites)
assertEqual(None, testFun2.transitiveReads)
assertEqual(None, testFun2.transitiveWrites)
assertEqual([["bar0"]], testFun6.transitiveReads)
assertEqual([], testFun6.transitiveWrites)
assertEqual([], testFun7.transitiveReads)
assertEqual([["bar1"], ["bar2"], ["bar0"]], testFun7.transitiveWrites)
assertEqual([["bar0"]], testFun8.transitiveReads)
assertEqual([["bar1"], ["bar2"], ["bar0"]], testFun8.transitiveWrites)
# Testing conflictsWith
assertEqual(True, testFun0.conflictsWith(testFun1))
assertEqual(True, testFun1.conflictsWith(testFun0))
assertEqual(False, testFun0.conflictsWith(testFun4))
assertEqual(False, testFun4.conflictsWith(testFun0))
assertEqual(True, testFun1.conflictsWith(testFun4))
assertEqual(True, testFun4.conflictsWith(testFun1))
assertEqual(None, testFun2.conflictsWith(testFun4))
assertEqual(None, testFun2.conflictsWith(testFun5))
assertEqual(True, testFun6.conflictsWith(testFun1))
assertEqual(True, testFun1.conflictsWith(testFun6))
assertEqual(True, testFun6.conflictsWith(testFun8))
assertEqual(True, testFun8.conflictsWith(testFun6))
# End of test

class ResultPart(L3FunExt):

  def __init__(self, reads = [], writes = [], dependencies = [], name = None, arity = None):
    # We allow name and arity to be None, if they are set later
    # We allow reads to be None (even if they are never set to anything else)
    L3FunExt.__init__(self, name = name, arity = arity, 
                      reads = reads, writes = writes, 
                      dependencies = dependencies)

# Tells the code generation that the result is unit
class UnitResult(ResultPart):
  
  def __init__(self):
    ResultPart.__init__(self, reads = [])

# Tells the code generation that the result depends on the state
class ReadStateResult(ResultPart):

  def __init__(self, reads = [], writes = [], 
               dependencies = [], 
               name = None, arity = None):
    ResultPart.__init__(self, reads, writes, dependencies, name, arity)

class StatePart(L3FunExt):

  def __init__(self, reads = [], writes = [], dependencies = [], name = None, arity = None):
    # We allow name and arity to be None, if they are later set by setParentFunction
    # We allow writes to be None (even if they are never set to anything else)
    L3FunExt.__init__(self, name = name, arity = arity, 
                      reads = reads, writes = writes, 
                      dependencies = dependencies)

# Tells the code generation that the state part is updated
class UpdateStatePart(StatePart):
  
  def __init__(self, reads = [], writes = [], 
               dependencies = [], 
               indexed = False, idem = True, getSetSimp = True,
               name = None, arity = None):
    StatePart.__init__(self, reads, writes, dependencies, name, arity)
    # Indexed is true if the parameter is of the shape (value, index) instead of value
    # This is generally the case if the corresponding getter has a parameter.
    self.indexed = indexed
    # Idem is true if the function is idempotent 
    # (actually slightly more general: if (f v' (f v s) = f v'))
    self.idem = idem
    # GetSetSimp is true if (get (set v s) = v). This property is only relevant when
    # the function ("set" in the above formula) is part of a L3Component.
    self.getSetSimp = getSetSimp

# Tells the code generation to unfold the function
class UnfoldFun(L3FunExt):  

  def __init__(self, name, arity = 1):
    L3FunExt.__init__(self, name, arity)

# Tells the code generation to split the function into a result and a state part
class SplitFun(L3FunExt): 

  def __init__(self, name, arity = 1, 
               resultPart = UnitResult(), 
               statePart = UpdateStatePart(),
               nextUnknownIds = []):

    if (resultPart.reads is None):
      myReads = statePart.reads
    elif (statePart.reads is None):
      myReads = resultPart.reads
    else:
      myReads = combineStateComponents(resultPart.reads, statePart.reads)

    if (resultPart.writes is None):
      myWrites = statePart.writes
    elif (statePart.writes is None):
      myWrites = resultPart.writes
    else:
      myWrites = combineStateComponents(resultPart.writes, statePart.writes)

    if (resultPart.dependencies is None):
      myDependencies = statePart.dependencies
    elif (statePart.dependencies is None):
      myDependencies = resultPart.dependencies
    else:
      myDependencies = extendNoDuplicates(resultPart.dependencies, statePart.dependencies)

    L3FunExt.__init__(self, name, arity, 
                      reads = myReads, 
                      writes = myWrites, 
                      dependencies = myDependencies,
                      nextUnknownIds = nextUnknownIds)

    # Set extra fields 
    if (isinstance(statePart, UpdateStatePart)):
      self.getSetSimp = statePart.getSetSimp
      self.indexed = statePart.indexed
    else:
      self.getSetSimp = False
    self.resultIsUnit = (isinstance(resultPart, UnitResult))
    self.resultPartName = "get" + firstLetterUpperCase(self.name)
    self.statePartName = self.getSetterName(resultPart)

  def getSetterName(self, resultPart):
    if (isinstance(resultPart, UnitResult)):
      if (self.name.startswith("write'")):
        return "set" + firstLetterUpperCase(self.name[6:])
      elif (self.name.startswith("dfn'")):
        return "set" + firstLetterUpperCase(self.name[4:])
      else:
        return "set" + firstLetterUpperCase(self.name)
    else:
      return "sideEffects" + firstLetterUpperCase(self.name)

model = L3Model([ 
  L3File("L3 library", [ 
    SplitFun("raise'exception", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["exception"]],
                                         writes = [["exception"]]))]),
  L3File("mips-log.spec", [  
    UnfoldFun("println", 1),
    UnfoldFun("clear_watcher", 0),
    UnfoldFun("clear_logs", 0)]),
  L3File("mips-pic.spec", [
    SplitFun("PIC_update", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["PIC_config_regs"], 
                                                  ["PIC_ip_bits"], 
                                                  ["PIC_external_intrs"],
                                                  ["c_state", "c_CP0", "Cause", "IP"], 
                                                  ["all_state"],
                                                  ["procID"]],
                                         writes = [["c_state", "c_CP0", "Cause", "IP"], 
                                                   ["all_state"]])),
    SplitFun("PIC_initialise", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["PIC_base_address"], 
                                                  ["PIC_config_regs"], 
                                                  ["PIC_ip_bits"], 
                                                  ["PIC_external_intrs"],
                                                  ["procID"]], 
                                         writes = [["PIC_base_address"], 
                                                   ["PIC_config_regs"], 
                                                   ["PIC_ip_bits"], 
                                                   ["PIC_external_intrs"]], 
                                         dependencies = ["PIC_update"])),
    SplitFun("PIC_load", 1, 
             ReadStateResult(reads = [["PIC_base_address"], 
                                      ["PIC_config_regs"], 
                                      ["PIC_ip_bits"], 
                                      ["PIC_external_intrs"]]),
             nextUnknownIds = ["pic-data"]),
    SplitFun("PIC_store", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["PIC_config_regs"], 
                                                  ["PIC_ip_bits"], 
                                                  ["PIC_base_address"]], 
                                         writes = [["PIC_config_regs"], 
                                                   ["PIC_ip_bits"]], 
                                         dependencies = ["PIC_update"]))]),
  L3File("mips-uart.spec", [
    SplitFun("JTAG_UART_update_interrupt_bit", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["JTAG_UART"], ["PIC_external_intrs"]], 
                                         writes = [["JTAG_UART"], ["PIC_external_intrs"]], 
                                         dependencies = ["PIC_update"])),
    SplitFun("JTAG_UART_load", 0, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["JTAG_UART"]], 
                                         writes = [["JTAG_UART"]], 
                                         dependencies = ["JTAG_UART_update_interrupt_bit"])),
    SplitFun("JTAG_UART_input", 1, 
             statePart = UpdateStatePart(idem = False,
                                         reads = [["JTAG_UART"]], 
                                         writes = [["JTAG_UART"]], 
                                         dependencies = ["JTAG_UART_update_interrupt_bit", 
                                                         "JTAG_UART_load"])),
    SplitFun("JTAG_UART_store", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["JTAG_UART"]], 
                                         writes = [["JTAG_UART"]], 
                                         dependencies = ["JTAG_UART_update_interrupt_bit"])),
    SplitFun("JTAG_UART_output", 0, 
             ReadStateResult(reads = [["JTAG_UART"]]), 
             UpdateStatePart(idem = False,
                             writes = [["JTAG_UART"]], 
                             dependencies = ["JTAG_UART_update_interrupt_bit"])),
    SplitFun("JTAG_UART_initialise", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["JTAG_UART"]], 
                                         writes = [["JTAG_UART"]]))]),
  L3File("mips-base.spec", [
    L3Component(
      SplitFun("gpr", 1, 
               ReadStateResult(reads = [["c_gpr"]])),
      SplitFun("write'gpr", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           reads = [["c_gpr"]],
                                           writes = [["c_gpr"]]))),
    L3Component(
      SplitFun("GPR", 1, 
               ReadStateResult(dependencies = ["gpr"])),
      SplitFun("write'GPR", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           getSetSimp = False, 
                                           dependencies = ["write'gpr"]))),
    SplitFun("UserMode", 0, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Status", "KSU"],
                                      ["c_state", "c_CP0", "Status", "EXL"],
                                      ["c_state", "c_CP0", "Status", "ERL"]])),
    SplitFun("SupervisorMode", 0, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Status", "KSU"],
                                      ["c_state", "c_CP0", "Status", "EXL"],
                                      ["c_state", "c_CP0", "Status", "ERL"]])),
    SplitFun("KernelMode", 0, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Status", "KSU"],
                                      ["c_state", "c_CP0", "Status", "EXL"],
                                      ["c_state", "c_CP0", "Status", "ERL"]])),
    SplitFun("BigEndianMem", 0, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Config", "BE"]])),
    SplitFun("ReverseEndian", 0, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Status", "StatusRegister.RE"]],
                             dependencies = ["UserMode"])),
    SplitFun("BigEndianCPU", 0, 
             ReadStateResult(dependencies = ["BigEndianMem", "ReverseEndian"])),
    SplitFun("CheckBranch", 0, 
             statePart = UpdateStatePart(reads = [["BranchDelayPCC"],
                                                  ["c_state", "c_BranchDelay"]],
                                         dependencies = ["raise'exception"])),
    SplitFun("BranchNotTaken", 0, 
             statePart = UpdateStatePart(reads = [["c_state", "c_PC"]],
                                         writes = [["c_state", "c_BranchTo"]],
                                         dependencies = ["CheckBranch"])),
    SplitFun("BranchLikelyNotTaken", 0, 
             statePart = UpdateStatePart(reads = [["c_state", "c_PC"]],
                                         writes = [["c_state", "c_PC"]],
                                         dependencies = ["CheckBranch"])),
    UnfoldFun("dumpRegs", 1),
    SplitFun("initCoreStats", 0, 
             statePart = UpdateStatePart(writes = [["c_state", "c_CoreStats"]])),
    SplitFun("printCoreStats", 0, 
             ReadStateResult(reads = [["c_state", "c_CoreStats"]])),
    SplitFun("next_unknown", 1, 
             ReadStateResult(reads = [["unknown_counters"]]), 
             UpdateStatePart(writes = [["unknown_counters"]]))]),
  L3File("cheri/state.spec", [
    UnfoldFun("dumpCRegs", 1),
    L3Component(
      SplitFun("PCC", 0, 
               ReadStateResult(reads = [["c_pcc"], ["procID"]])),
      SplitFun("write'PCC", 1, 
               statePart = UpdateStatePart(writes = [["c_pcc"]]))),
    L3Component(
      SplitFun("CAPR", 1, 
               ReadStateResult(reads = [["c_capr"], ["procID"]])),
      SplitFun("write'CAPR", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           reads = [["c_capr"]],
                                           writes = [["c_capr"]]))),
    L3Component(
      SplitFun("SCAPR", 1, 
               ReadStateResult(reads = [["c_scapr"], ["procID"]])),
      SplitFun("write'SCAPR", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           reads = [["c_scapr"]],
                                           writes = [["c_scapr"]]))),
    L3Component(
      UnfoldFun("RCC", 0),
      UnfoldFun("write'RCC", 1)),
    L3Component(
      UnfoldFun("IDC", 0),
      UnfoldFun("write'IDC", 1)),
    L3Component(
      UnfoldFun("DDC", 0),
      UnfoldFun("write'DDC", 1)),
    L3Component(
      UnfoldFun("TLSC", 0),
      UnfoldFun("write'TLSC", 1)),
    L3Component(
      UnfoldFun("PTLSC", 0),
      UnfoldFun("write'PTLSC", 1)),
    L3Component(
      UnfoldFun("KR1C", 0),
      UnfoldFun("write'KR1C", 1)),
    L3Component(
      UnfoldFun("KR2C", 0),
      UnfoldFun("write'KR2C", 1)),
    L3Component(
      UnfoldFun("KCC", 0),
      UnfoldFun("write'KCC", 1)),
    L3Component(
      UnfoldFun("KDC", 0),
      UnfoldFun("write'KDC", 1)),
    L3Component(
      UnfoldFun("EPCC", 0),
      UnfoldFun("write'EPCC", 1))]),
  L3File("cheri/exceptions.spec", [
    SplitFun("SignalException", 1, 
             statePart = UpdateStatePart( \
               idem = False, 
               reads = [["currentInst"],
                        ["lastInst"],
                        ["BranchDelayPCC"],
                        ["capcause"],
                        ["c_state", "c_BranchDelay"],
                        ["c_state", "c_PC"],
                        ["c_state", "c_CP0", "Status", "EXL"],
                        ["c_state", "c_CP0", "Status", "BEV"]],
               writes = [["BranchDelayPCC"], 
                         ["BranchToPCC"],
                         ["c_state", "c_BranchDelay"],
                         ["c_state", "c_BranchTo"],
                         ["c_state", "c_PC"],
                         ["c_state", "c_exceptionSignalled"],
                         ["c_state", "c_CP0", "Status", "EXL"],
                         ["c_state", "c_CP0", "EPC"],
                         ["c_state", "c_CP0", "BadInstr"],
                         ["c_state", "c_CP0", "BadInstrP"],
                         ["c_state", "c_CP0", "Cause", "BD"],
                         ["c_state", "c_CP0", "Cause", "CauseRegister.ExcCode"]],
               dependencies = ["PCC", "write'PCC", 
                               "SCAPR", "write'SCAPR"]),
             nextUnknownIds = ["BadInstrP"]),
    SplitFun("SignalCP2UnusableException", 0, 
             statePart = UpdateStatePart(idem = False, 
                                         writes = [["c_state", "c_CP0", "Cause", "CE"]],
                                         dependencies = ["SignalException"])),
    SplitFun("SignalCapException_internal", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["capcause"]], 
                                         writes = [["capcause"]], 
                                         dependencies = ["SignalException"])),
    SplitFun("SignalCapException", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["SignalCapException_internal"])),
    SplitFun("SignalCapException_noReg", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["SignalCapException_internal"])),
    # SplitFun("dfn'ERET", 0,
    #          statePart = UpdateStatePart(idem = False, 
    #                                      reads = [["c_state", "c_CP0", "Status", "CU0"],
    #                                               ["c_state", "c_CP0", "Status", "ERL"],
    #                                               ["c_state", "c_CP0", "ErrorEPC"],
    #                                               ["c_state", "c_CP0", "EPC"]], 
    #                                      writes = [["c_state", "c_CP0", "Status", "EXL"],
    #                                                ["c_state", "c_CP0", "Status", "ERL"],
    #                                                ["c_state", "c_PC"],
    #                                                ["c_state", "c_LLbit"]], 
    #                                      dependencies = ["SCAPR", 
    #                                                      "KernelMode", 
    #                                                      "CheckBranch", 
    #                                                      "write'PCC", 
    #                                                      "SignalException"])),
    L3FunExt("dfn'ERET", 0)]),
  L3File("tlb/base.spec", [
    L3Component(
      SplitFun("TLB_direct", 1, 
               ReadStateResult(reads = [["c_TLB_direct"], ["procID"]])),
      SplitFun("write'TLB_direct", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           reads = [["c_TLB_direct"]],
                                           writes = [["c_TLB_direct"]]))),
    L3Component(
      SplitFun("TLB_assoc", 1, 
               ReadStateResult(reads = [["c_TLB_assoc"], ["procID"]])),
      SplitFun("write'TLB_assoc", 1, 
               statePart = UpdateStatePart(indexed = True, 
                                           reads = [["c_TLB_assoc"]],
                                           writes = [["c_TLB_assoc"]]))),
    SplitFun("LookupTLB", 1, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Config6"],
                                      ["c_state", "c_CP0", "EntryHi"]],
                             dependencies = ["TLB_assoc", 
                                             "TLB_direct"])),
    SplitFun("SignalTLBException_internal", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         writes = [["c_state", "c_CP0", "BadVAddr"],
                                                   ["c_state", "c_CP0", "EntryHi"],
                                                   ["c_state", "c_CP0", "Context"],
                                                   ["c_state", "c_CP0", "XContext"]])),
    SplitFun("SignalTLBException", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["SignalException",
                                                         "SignalTLBException_internal"])),
    SplitFun("CheckSegment", 1, 
             ReadStateResult(reads = [["c_state", "c_CP0", "Config", "K0"]],
                             dependencies = ["UserMode", 
                                             "SupervisorMode"])),
    SplitFun("check_cca", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["raise'exception"])),
    SplitFun("TLB_next_random", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["c_state", "c_CP0", "Random", "Random.Random"],
                                                  ["c_state", "c_CP0", "Wired", "Wired.Wired"]],
                                         writes = [["c_state", "c_CP0", "Random", "Random.Random"]]))]),
  L3File("cheri/tlb-translate.spec", [
    SplitFun("AddressTranslation", 1, 
             ReadStateResult(dependencies = ["CheckSegment", "LookupTLB"]), 
             UpdateStatePart(idem = False, 
                             reads = [["c_state", "c_CP0", "EntryHi"]],
                               writes = [["c_state", "c_CP0", "BadVAddr"]],
                             dependencies = ["PCC", 
                                             "SignalTLBException", 
                                             "raise'exception", 
                                             "check_cca", 
                                             "SignalException"]),
             nextUnknownIds = ["tlb-translation"]),
    SplitFun("CP0TLBEntry", 1, 
             ReadStateResult(reads = [["c_state", "c_CP0"]])),
    SplitFun("SignalTLBCapException", 1, 
             statePart = UpdateStatePart(dependencies = ["SignalTLBException_internal",
                                                         "SignalCapException_noReg"]),
             nextUnknownIds = ["tlb-cap-exception"])]),
  L3File("cheri/memory.spec", [
    SplitFun("printMemStats", 0, 
             ReadStateResult(reads = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("initMemStats", 0, 
             statePart = UpdateStatePart(writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_data_reads_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_data_writes_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_inst_reads_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_valid_cap_reads_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_valid_cap_writes_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_invalid_cap_reads_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    SplitFun("stats_invalid_cap_writes_updt", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["staticMemStats"], ["dynamicMemStats"]],
                                         writes = [["staticMemStats"], ["dynamicMemStats"]])),
    L3Component(
      SplitFun("MEM", 1, 
               ReadStateResult(reads = [["the_MEM"]])),
      SplitFun("write'MEM", 1, 
               statePart = UpdateStatePart(indexed = True,
                                           reads = [["the_MEM"]],
                                           writes = [["the_MEM"]]))),
    SplitFun("InitMEM", 0,
             statePart = UpdateStatePart(idem = False, 
                                         writes = [["static_shadow_MEM"],
                                                  ["static_shadow_TAGS"],
                                                  ["static_shadow_4K_TAGS"],
                                                  ["static_shadow_16K_TAGS"],
                                                  ["dynamic_shadow_MEM"],
                                                  ["dynamic_shadow_TAGS"],
                                                  ["dynamic_shadow_4K_TAGS"],
                                                  ["dynamic_shadow_16K_TAGS"],
                                                  ["the_MEM"]]),
             nextUnknownIds = ["mem-data"]),
    SplitFun("ReadData", 1, 
             ReadStateResult(dependencies = ["MEM"]), 
             UpdateStatePart(dependencies = ["stats_data_reads_updt"])),
    SplitFun("WriteData", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         reads = [["the_MEM"]],
                                         dependencies = ["write'MEM", 
                                                         "stats_data_writes_updt"])),
    SplitFun("ReadInst", 1, 
             ReadStateResult(dependencies = ["MEM"]), 
             UpdateStatePart(dependencies = ["stats_inst_reads_updt"])),
    SplitFun("ReadCap", 1, 
             ReadStateResult(dependencies = ["MEM"]), 
             UpdateStatePart(dependencies = ["stats_valid_cap_reads_updt", 
                                             "stats_invalid_cap_reads_updt"])),
    SplitFun("WriteCap", 1, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["write'MEM", 
                                                         "stats_valid_cap_writes_updt", 
                                                         "stats_invalid_cap_writes_updt"]))]),
  L3File("cheri/memaccess.spec.m4", [
    SplitFun("AdjustEndian", 1, 
             ReadStateResult(dependencies = ["ReverseEndian"]), 
             UpdateStatePart(dependencies = ["raise'exception"])),
    SplitFun("initMemAccessStats", 0, 
             statePart = UpdateStatePart(reads = [["memAccessStats"]],
                                         writes = [["memAccessStats"]])),
    SplitFun("printMemAccessStats", 0, 
             ReadStateResult(reads = [["memAccessStats"]])),
    UnfoldFun("watchForLoad", 1),
    UnfoldFun("watchForCapLoad", 1),
    UnfoldFun("watchForStore", 1),
    UnfoldFun("watchForCapStore", 1),
    SplitFun("getVirtualAddress", 1, 
             ReadStateResult(dependencies = ["SCAPR"])),
    SplitFun("LoadMemoryCap", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False, 
                             reads = [["JTAG_UART"],
                                      ["totalCore"],
                                      ["PIC_base_address"],
                                      ["memAccessStats"],
                                      ["c_state", "c_exceptionSignalled"]],
                             writes = [["memAccessStats"],
                                       ["c_state", "c_LLbit"],
                                       ["c_state", "c_CP0", "BadVAddr"],
                                       ["c_state", "c_CP0", "LLAddr"]],
                             dependencies = ["AdjustEndian",
                                             "ReadData",
                                             "PIC_load",
                                             "SignalException",
                                             "AddressTranslation",
                                             "raise'exception",
                                             "JTAG_UART_load",
                                             "stats_data_reads_updt"]),
             nextUnknownIds = ["mem-data"]),
    SplitFun("LoadMemory", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False,
                             dependencies = ["SCAPR", 
                                             "SignalCapException", 
                                             "LoadMemoryCap"]),
             nextUnknownIds = ["mem-data"]),
    SplitFun("LoadCap", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False,
                             reads = [["JTAG_UART"],
                                      ["totalCore"],
                                      ["PIC_base_address"],
                                      ["memAccessStats"],
                                      ["c_state", "c_exceptionSignalled"]],
                             writes = [["memAccessStats"],
                                       ["c_state", "c_LLbit"],
                                       ["c_state", "c_CP0", "LLAddr"]],
                             dependencies = ["AddressTranslation", 
                                             "raise'exception",
                                             "ReadCap"]),
             nextUnknownIds = ["capability"]),
    SplitFun("StoreMemoryCap", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False,
                             reads = [["JTAG_UART"],
                                      ["totalCore"],
                                      ["PIC_base_address"],
                                      ["memAccessStats"],
                                      ["c_state", "c_LLbit"],
                                      ["c_state", "c_exceptionSignalled"],
                                      ["c_state", "c_CP0", "LLAddr"],
                                      ["all_state"],
                                      ["procID"]],
                             writes = [["all_state"], 
                                       ["memAccessStats"],
                                       ["c_state", "c_LLbit"],
                                       ["c_state", "c_CP0", "BadVAddr"]],
                             dependencies = ["AdjustEndian",
                                             "SignalException",
                                             "AddressTranslation",
                                             "raise'exception",
                                             "JTAG_UART_store", 
                                             "PIC_store",
                                             "WriteData"]),
             nextUnknownIds = ["sc-success"]),
    SplitFun("StoreMemory", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False,
                             dependencies = ["SCAPR", 
                                             "SignalCapException", 
                                             "StoreMemoryCap",]),
             nextUnknownIds = ["sc-success"]),
    SplitFun("StoreCap", 1,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False, 
                             reads = [["JTAG_UART"],
                                      ["totalCore"],
                                      ["PIC_base_address"],
                                      ["memAccessStats"],
                                      ["c_state", "c_LLbit"],
                                      ["c_state", "c_exceptionSignalled"],
                                      ["c_state", "c_CP0", "LLAddr"],
                                      ["c_state", "c_CP0", "EntryHi", "ASID"],
                                      ["all_state"],
                                      ["procID"]],
                             writes = [["all_state"], 
                                       ["memAccessStats"],
                                       ["c_state", "c_LLbit"]],
                             dependencies = ["AddressTranslation",
                                             "raise'exception",
                                             "SignalTLBCapException",
                                             "WriteCap"])),
    SplitFun("Fetch", 0,
             ReadStateResult(reads = None),
             UpdateStatePart(idem = False,
                             reads = [["c_state", "c_exceptionSignalled"],
                                      ["c_state", "c_PC"],
                                      ["c_state", "c_CP0", "Compare"],
                                      ["c_state", "c_CP0", "Count"],
                                      ["c_state", "c_CP0", "Status", "IE"],
                                      ["c_state", "c_CP0", "Status", "EXL"],
                                      ["c_state", "c_CP0", "Status", "ERL"],
                                      ["c_state", "c_CP0", "Status", "IM"],
                                      ["c_state", "c_CP0", "Cause", "IP"]],
                             writes = [["c_state", "c_CP0", "Cause"],
                                       ["c_state", "c_CP0", "BadVAddr"]],
                             dependencies = ["SignalException",
                                             "SignalCapException_noReg",
                                             "PCC",
                                             "ReadInst",
                                             "AddressTranslation"]))]),
  L3File("mips-CP0.spec", [
    L3Component(
      SplitFun("CP0R", 1, 
               ReadStateResult(reads = [["procID"], 
                                        ["totalCore"], 
                                        ["c_state", "c_CP0"]]),
               nextUnknownIds = ["cop-reg"]),
      SplitFun("write'CP0R", 1, 
               statePart = UpdateStatePart(getSetSimp = False, 
                                           reads = [["hasCP1"],
                                                    ["hasCP2"],
                                                    ["c_state", "c_CP0"]],
                                           writes = [["done"],
                                                     ["c_state", "c_CP0"]],
                                           dependencies = ["raise'exception"])))]),
  L3File("mips-utils.spec", [
    SplitFun("resetStats", 0, 
             statePart = UpdateStatePart(idem = False, 
                                         dependencies = ["initMemStats", 
                                                         "initMemAccessStats", 
                                                         "initCoreStats"])),
    UnfoldFun("dumpStats", 0),
    L3Component(
      SplitFun("HI", 0, 
               ReadStateResult(reads = [["c_state", "c_hi"]]),
               nextUnknownIds = ["hi-reg"]),
      SplitFun("write'HI", 1, 
               statePart = UpdateStatePart(writes = [["c_state", "c_hi"]]))),
    L3Component(
      SplitFun("LO", 0, 
               ReadStateResult(reads = [["c_state", "c_lo"]]),
               nextUnknownIds = ["lo-reg"]),
      SplitFun("write'LO", 1, 
               statePart = UpdateStatePart(writes = [["c_state", "c_lo"]])))]),
  L3File("cheri/cop-access.spec", [
    L3FunExt("mtc"),
    L3FunExt("dmtc"),
    L3FunExt("mfc"),
    L3FunExt("dmfc")]),
  L3File("mips-instructions.spec", [
    L3FunExt("dfn'ADDI"),
    L3FunExt("dfn'ADDIU"), 
    L3FunExt("dfn'DADDI"),
    L3FunExt("dfn'DADDIU"),
    L3FunExt("dfn'SLTI"),
    L3FunExt("dfn'SLTIU"),
    L3FunExt("dfn'ANDI"),
    L3FunExt("dfn'ORI"),
    L3FunExt("dfn'XORI"),
    L3FunExt("dfn'LUI"),
    L3FunExt("dfn'ADD"), 
    L3FunExt("dfn'ADDU"), 
    L3FunExt("dfn'SUB"), 
    L3FunExt("dfn'SUBU"), 
    L3FunExt("dfn'DADD"), 
    L3FunExt("dfn'DADDU"), 
    L3FunExt("dfn'DSUB"), 
    L3FunExt("dfn'DSUBU"), 
    L3FunExt("dfn'SLT"), 
    L3FunExt("dfn'SLTU"), 
    L3FunExt("dfn'AND"), 
    L3FunExt("dfn'OR"), 
    L3FunExt("dfn'XOR"),
    L3FunExt("dfn'NOR"), 
    L3FunExt("dfn'MOVN"), 
    L3FunExt("dfn'MOVZ"), 
    L3FunExt("dfn'MADD"),
    L3FunExt("dfn'MADDU"),
    L3FunExt("dfn'MSUB"),
    L3FunExt("dfn'MSUBU"),
    L3FunExt("dfn'MUL"),
    L3FunExt("dfn'MULT"),
    L3FunExt("dfn'MULTU"),
    L3FunExt("dfn'DMULT"),
    L3FunExt("dfn'DMULTU"),
    L3FunExt("dfn'DIV"),
    L3FunExt("dfn'DIVU"),
    L3FunExt("dfn'DDIV"),
    L3FunExt("dfn'DDIVU"),
    L3FunExt("dfn'MFHI"),
    L3FunExt("dfn'MFLO"),
    L3FunExt("dfn'MTHI"),
    L3FunExt("dfn'MTLO"),
    L3FunExt("dfn'SLL"),
    L3FunExt("dfn'SRL"),
    L3FunExt("dfn'SRA"),
    L3FunExt("dfn'SLLV"),
    L3FunExt("dfn'SRLV"),
    L3FunExt("dfn'SRAV"),
    L3FunExt("dfn'DSLL"),
    L3FunExt("dfn'DSRL"),
    L3FunExt("dfn'DSRA"),
    L3FunExt("dfn'DSLLV"),
    L3FunExt("dfn'DSRLV"),
    L3FunExt("dfn'DSRAV"),
    L3FunExt("dfn'DSLL32"),
    L3FunExt("dfn'DSRL32"),
    L3FunExt("dfn'DSRA32"),
    L3FunExt("dfn'TGE"),
    L3FunExt("dfn'TGEU"),
    L3FunExt("dfn'TLT"),
    L3FunExt("dfn'TLTU"),
    L3FunExt("dfn'TEQ"),
    L3FunExt("dfn'TNE"),
    L3FunExt("dfn'TGEI"),
    L3FunExt("dfn'TGEIU"),
    L3FunExt("dfn'TLTI"),
    L3FunExt("dfn'TLTIU"),
    L3FunExt("dfn'TEQI"),
    L3FunExt("dfn'TNEI"),
    L3FunExt("loadByte"),
    L3FunExt("loadHalf"),
    L3FunExt("loadWord"),
    L3FunExt("loadDoubleword"),
    L3FunExt("dfn'LB"),
    L3FunExt("dfn'LBU"),
    L3FunExt("dfn'LH"),
    L3FunExt("dfn'LHU"),
    L3FunExt("dfn'LW"),
    L3FunExt("dfn'LWU"),
    L3FunExt("dfn'LL"),
    L3FunExt("dfn'LD"),
    L3FunExt("dfn'LLD"),
    L3FunExt("dfn'LWL"),
    L3FunExt("dfn'LWR"),
    L3FunExt("dfn'LDL"),
    L3FunExt("dfn'LDR"),
    L3FunExt("dfn'SB"),
    L3FunExt("dfn'SH"),
    L3FunExt("storeWord"),
    L3FunExt("storeDoubleword"),
    L3FunExt("dfn'SW"),
    L3FunExt("dfn'SD"),
    L3FunExt("dfn'SC"),
    L3FunExt("dfn'SCD"),
    L3FunExt("dfn'SWL"),
    L3FunExt("dfn'SWR"),
    L3FunExt("dfn'SDL"),
    L3FunExt("dfn'SDR"),
    L3FunExt("dfn'BREAK", 0),
    L3FunExt("dfn'SYSCALL", 0),
    L3FunExt("dfn'MTC0"),
    L3FunExt("dfn'DMTC0"),
    L3FunExt("dfn'MFC0"),
    L3FunExt("dfn'DMFC0"),
    L3FunExt("dfn'J"), 
    L3FunExt("dfn'JAL"), 
    L3FunExt("dfn'JALR"), 
    L3FunExt("dfn'JR"),
    L3FunExt("dfn'BEQ"), 
    L3FunExt("dfn'BNE"), 
    L3FunExt("dfn'BLEZ"), 
    L3FunExt("dfn'BGTZ"), 
    L3FunExt("dfn'BLTZ"), 
    L3FunExt("dfn'BGEZ"), 
    L3FunExt("dfn'BLTZAL"), 
    L3FunExt("dfn'BGEZAL"), 
    L3FunExt("dfn'BEQL"), 
    L3FunExt("dfn'BNEL"), 
    L3FunExt("dfn'BLEZL"), 
    L3FunExt("dfn'BGTZL"), 
    L3FunExt("dfn'BLTZL"), 
    L3FunExt("dfn'BGEZL"), 
    L3FunExt("dfn'BLTZALL"), 
    L3FunExt("dfn'BGEZALL"), 
    L3FunExt("dfn'RDHWR"),
    L3FunExt("dfn'CACHE"),
    L3FunExt("dfn'ReservedInstruction", 0),
    L3FunExt("dfn'Unpredictable", 0)]),
  L3File("tlb/instructions.spec", [
    L3FunExt("dfn'TLBP", 0),
    L3FunExt("dfn'TLBR", 0),
    L3FunExt("dfn'TLBWI", 0),
    L3FunExt("dfn'TLBWR", 0)]),
  L3File("cp1-null/instructions.spec", [
    L3FunExt("dfn'COP1")]),
  L3File("cheri/instructions.spec.m4", [
    UnfoldFun("watchOOB", 1),
    UnfoldFun("dfn'DumpCapReg", 0),
    L3FunExt("dfn'CGetBase"),
    L3FunExt("dfn'CGetOffset"),
    L3FunExt("dfn'CGetLen"),
    L3FunExt("dfn'CGetTag"),
    L3FunExt("dfn'CGetSealed"),
    L3FunExt("dfn'CGetPerm"),
    L3FunExt("dfn'CGetType"),
    L3FunExt("dfn'CGetAddr"),
    L3FunExt("dfn'CGetPCC"),
    L3FunExt("dfn'CGetPCCSetOffset"),
    L3FunExt("dfn'CGetCause"),
    L3FunExt("dfn'CSetCause"),
    L3FunExt("dfn'CIncOffset"),
    L3FunExt("dfn'CIncOffsetImmediate"),
    L3FunExt("dfn'CSetBounds"),
    L3FunExt("dfn'CSetBoundsExact"),
    L3FunExt("dfn'CSetBoundsImmediate"),
    L3FunExt("ClearRegs"),
    L3FunExt("dfn'ClearLo"),
    L3FunExt("dfn'ClearHi"),
    L3FunExt("dfn'CClearLo"),
    L3FunExt("dfn'CClearHi"),
    # L3FunExt("dfn'FPClearLo"),
    # L3FunExt("dfn'FPClearHi"),
    L3FunExt("dfn'CClearTag"),
    L3FunExt("dfn'CAndPerm"),
    L3FunExt("dfn'CSetOffset"),
    L3FunExt("dfn'CSub"),
    L3FunExt("dfn'CCheckPerm"),
    L3FunExt("dfn'CCheckType"),
    L3FunExt("dfn'CFromPtr"),
    L3FunExt("dfn'CToPtr"),
    L3FunExt("CPtrCmp"),
    L3FunExt("dfn'CEQ"),
    L3FunExt("dfn'CNE"),
    L3FunExt("dfn'CLT"),
    L3FunExt("dfn'CLE"),
    L3FunExt("dfn'CLTU"),
    L3FunExt("dfn'CLEU"),
    L3FunExt("dfn'CEXEQ"),
    L3FunExt("dfn'CNEXEQ"),
    L3FunExt("dfn'CBTU"),
    L3FunExt("dfn'CBTS"),
    L3FunExt("dfn'CBEZ"),
    L3FunExt("dfn'CBNZ"),
    L3FunExt("dfn'CSC"),
    L3FunExt("dfn'CLC"),
    L3FunExt("dfn'CLoad"),
    L3FunExt("store"),
    L3FunExt("dfn'CStore"),
    L3FunExt("dfn'CLLC"),
    L3FunExt("dfn'CLLx"),
    L3FunExt("dfn'CSCC"),
    L3FunExt("dfn'CSCx"),
    L3FunExt("dfn'CMOVN"),
    L3FunExt("dfn'CMOVZ"),
    L3FunExt("dfn'CMove"),
    L3FunExt("dfn'CTestSubset"),
    L3FunExt("dfn'CBuildCap"),
    L3FunExt("dfn'CCopyType"),
    L3FunExt("dfn'CJR"),
    L3FunExt("dfn'CJALR"),
    L3FunExt("dfn'CSeal"),
    L3FunExt("dfn'CUnseal"),
    L3FunExt("dfn'CCall"),
    L3FunExt("dfn'CCallFast"),
    SplitFun("special_register_accessible", 1, 
             ReadStateResult(dependencies = ["PCC", 
                                             "KernelMode"],
                             reads = [["c_state", "c_CP0", "Status", "CU0"]])),
    L3FunExt("dfn'CReadHwr"),
    L3FunExt("dfn'CWriteHwr"),
    L3FunExt("dfn'CReturn", 0),
    L3FunExt("dfn'UnknownCapInstruction", 0)]),
  L3File("cheri/next.spec", [
    SplitFun("log_instruction", 1, 
             ReadStateResult(reads = [["procID"], 
                                      ["instCnt"],
                                      ["c_state", "c_PC"]], 
                             dependencies = ["PCC"])),
    L3FunExt("Run"),
    L3FunExt("Next", 0)])
  ])

FunctionsWithActions = \
  ["dfn'CAndPerm",
   "dfn'CBuildCap",
   "dfn'CClearHi",
   "dfn'CClearLo",
   "dfn'CClearTag",
   "dfn'CCallFast",
   "dfn'CCopyType",
   "dfn'CFromPtr",
   "dfn'CGetPCC",
   "dfn'CGetPCCSetOffset",
   "dfn'CIncOffset",
   "dfn'CIncOffsetImmediate",
   "dfn'CJALR",
   "dfn'CJR",
   "dfn'CLC",
   "dfn'CLLC",
   "dfn'CMOVN",
   "dfn'CMOVZ",
   "dfn'CMove",
   "dfn'CReadHwr",
   "dfn'CSC",
   "dfn'CSCC",
   "dfn'CSeal",
   "dfn'CSetBounds",
   "dfn'CSetBoundsExact",
   "dfn'CSetBoundsImmediate",
   "dfn'CSetOffset",
   "dfn'CUnseal",
   "dfn'CWriteHwr",
   "dfn'ERET",
   "dfn'LB",
   "dfn'LBU",
   "dfn'LH",
   "dfn'LHU",
   "dfn'LW",
   "dfn'LWU",
   "dfn'LL",
   "dfn'LD",
   "dfn'LLD",
   "dfn'LWL",
   "dfn'LWR",
   "dfn'LDL",
   "dfn'LDR",
   "dfn'CLoad",
   "dfn'CLLx",
   "dfn'SB",
   "dfn'SH",
   "dfn'SW",
   "dfn'SD",
   "dfn'SC",
   "dfn'SCD",
   "dfn'SWL",
   "dfn'SWR",
   "dfn'SDL",
   "dfn'SDR",
   "dfn'CStore",
   "dfn'CSCx",
   "Run"]
