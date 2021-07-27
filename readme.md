# Verified security properties for CHERI-MIPS

This repository contains formal definitions and proofs of security properties for the CHERI-MIPS architecture.

## Setup

- Install Isabelle 2017. This version can be downloaded [here](https://isabelle.in.tum.de/website-Isabelle2017/index.html).

- Turn on 64-bits polyml mode in Isabelle's settings.

- Build a heap image of the CHERI-MIPS specification:

  - Find the ROOTS file of Isabelle, which is usually located at `~/.isabelle/Isabelle2017/ROOTS`.

  - Add the line `(path to repo)/generated` to that file.

  - Open Isabelle. A dialog box will open confirming that Isabelle is building the heap image.

## Running the proofs

Open the top-level file [Examples.thy](properties/Examples.thy) in Isabelle.

## Directory structure

- [`generated`](generated/) contains the Isabelle/HOL export of the L3 specification of CHERI-MIPS. The L3 source can be found [here](https://github.com/acjf3/l3mips).

- [`core`](core/) contains generally useful lemmas about the L3 specification, such as commutativity lemmas, simplification rules, and automated proof tactics.

- [`properties`](properties/) contains the security properties that form an abstraction of CHERI-MIPS. It also contains the definitions and proofs of security properties that are based on the abstraction.

- [`instantiation`](instantiation/) contains the proof that CHERI-MIPS satisfies the abstraction mentioned above.

- [`scripts`](scripts/) contains the Python scripts that are used to generate part of the proofs.

## Building on our proofs

When building on our proofs, it is recommended to build a heap image of our theories. Add the following to the ROOTS file mentioned under `Setup`:

- `(path to repo)/core`
- `(path to repo)/properties`
- `(path to repo)/instantiation`

## People and funding

The security properties have been developed by [Kyndylan Nienhuis](https://www.cl.cam.ac.uk/~kn307/). These comprise all files except those in the directory named `generated`.

- This work was supported by a Gates Cambridge Scholarship.

- This work was supported by EPSRC programme grant EP/K008528/1 (REMS: Rigorous Engineering for Mainstream Systems).

- This project has received funding from the European Research Council (ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement 789108, ELVER).

- This work was supported by the Defense Advanced Research Projects Agency (DARPA) and the Air Force Research Laboratory (AFRL), under contract FA8650-18-C-7809 (CIFV). The views, opinions, and/or findings contained in this paper are those of the authors and should not be interpreted as representing the official views or policies, either expressed or implied, of the Department of Defense or the U.S. Government. Approved for public release; distribution is unlimited.

The L3 specification of CHERI-MIPS has been developed by [Alexandre Joannou](https://www.cl.cam.ac.uk/~aj443/), [Anthony Fox](https://acjf3.github.io/), [Michael Roe](https://www.cst.cam.ac.uk/people/mr101), and Matthew Naylor. The directory `generated` contains the Isabelle/HOL export, and the original L3 source can be found [here](https://github.com/acjf3/l3mips).

- This work was supported by EPSRC programme grant EP/K008528/1 (REMS: Rigorous Engineering for Mainstream Systems).

- This project has received funding from the European Research Council (ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement 789108, ELVER).

- This work was supported by the Defense Advanced Research Projects Agency (DARPA) and the Air Force Research Laboratory (AFRL), under contracts FA8650-18-C-7809 (CIFV), HR0011-18-C-0016 (ECATS), FA8750-10-C-0237 (CTSRD), and FA8750-11-C-0249 (MRC2). The views, opinions, and/or findings contained in this paper are those of the authors and should not be interpreted as representing the official views or policies, either expressed or implied, of the Department of Defense or the U.S. Government. Approved for public release; distribution is unlimited.

## Licence

The proofs are made available under the BSD three-clause licence in LICENCE.
