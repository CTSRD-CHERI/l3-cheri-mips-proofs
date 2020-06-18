# INSTALL

The theory files work with Isabelle2017 in 64-bits polyml mode.

To reduce the startup time it is recommended to build a heap image of
the theories. Add the following to the ROOTS file of Isabelle
(usually located at ~/.isabelle/Isabelle2017/ROOTS):

* (path to repo)/generated
* (path to repo)/core
* (path to repo)/properties
* (path to repo)/instantiation

# Folder structure

"generated" contains the Isabelle export of the L3 model.

"core" contains generally useful lemmas about the L3 model, such as
commutativity lemmas, simplification rules and proof methods.

"properties" contains the definitions and proofs of security
properties of CHERI. These properties are defined in terms of an 
abstraction of CHERI. 

"instantiation" contains a mapping from CHERI instructions to abstract
actions and a proof that with this mapping, CHERI satisfies the 
security properties defined before. 

"scripts" contains the python scripts that are used to generate part
of the proofs.

