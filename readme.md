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

## Folder structure

- [`generated`](generated/) contains the Isabelle/HOL export of the L3 specification of CHERI-MIPS.

- [`core`](core/) contains generally useful lemmas about the L3 specification, such as commutativity lemmas, simplification rules, and automated proof tactics.

- [`properties`](properties/) contains the security properties that form an abstraction of CHERI-MIPS. It also contains the definitions and proofs of security properties that are based on the abstraction.

- [`instantiation`](instantiation/) contains the proof that CHERI-MIPS satisfies the abstraction mentioned above.

- [`scripts`](scripts/) contains the Python scripts that are used to generate part of the proofs.

## Building on our proofs

When building on our proofs, it is recommended to build a heap image of our theories. Add the following to the ROOTS file mentioned under `Setup`:

- `(path to repo)/core`
- `(path to repo)/properties`
- `(path to repo)/instantiation`

## Licence

The proofs are made available under the BSD three-clause licence in
LICENCE.
