# INSTALL

The theory files work with Isabelle2017.

To reduce the startup time it is advisable to build a heap image of
some of the theories. Add the following to the ROOTS file of Isabelle
(usually located at ~/.isabelle/Isabelle2017/ROOTS):

(path to repo)/generated
(path to repo)/core
(path to repo)/properties

# Folder structure

"generated" contains the Isabelle export of the L3 model.

"core" contains generally useful lemmas about the L3 model, such as
commutativity lemmas, simplification rules and proof methods.

"properties" contains the definitions and proofs of security
properties of CHERI.

"scripts" contains the python scripts that are used to generate part
of the proofs.

"latex" contains the files necessary to export human readable versions
of the security properties.