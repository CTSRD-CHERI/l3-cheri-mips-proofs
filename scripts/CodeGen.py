# Author: Kyndylan Nienhuis

from CodeGenBase import *
from CheriModel import *
import sys, glob, os

# CheriAltDefs
from Generators.GenStateComponentUpdates import *
from Generators.GenContractingReadsUpdates import *
from Generators.GenAltDefs import *

# CheriLemmas
from Generators.GenCommutativity import *
from Generators.GenValueAndStateParts import *

# SecurityProperties
from Generators.GenUndefinednessLemma import *
from Generators.GenExceptionSignalledInvariant import *
from Generators.GenExceptionLemma import *
from Generators.GenValidStateInvariant import *
from Generators.GenAddressTranslationInvariant import *
from Generators.GenMemoryInvariant import *
from Generators.GenCapInvariant import *
from Generators.GenMonotonicity import *

generators = \
  [StateComponentUpdatesGenerator(), 
   ContractingReadsUpdatesGenerator(),
   AltDefsGenerator(),
   CommutativityGenerator(),
   ValueAndStatePartsGenerator(),
   UndefinednessLemmaGenerator(),
   ExceptionSignalledInvariantGenerator(),
   ExceptionLemmaGenerator(),
   ValidStateInvariantGenerator(),
   AddressTranslationInvariantGenerator(),
   MemoryInvariantGenerator(),
   CapInvariantGenerator(),
   MonotonicityGenerator()]

directories = ["core", "properties" ,"instantiation"]

for d in directories:
  for f in glob.glob(d + "/*.thy"):
    generateFile(generators, f, model)

