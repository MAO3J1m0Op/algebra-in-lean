# Algebra In Lean

This is the repository for Algebra In Lean (AIL), an interactive problem set
that takes users through an advanced course in Lean through the lens of abstract
algebra. The goal of this problem set is to introduce users to formalization
and Lean 4 while also assisting in writing rigorous proofs in
group theory. Beginning with introductions to logic-based reasoning in Lean, each chapter takes users through various topics in group theory. Akin to Kevin
Buzzard’s [Formalising Mathematics course](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024) at the Imperial College London, AIL
includes chapters on group axioms, homomorphisms, and subgroups, each separated
into problem sheets. These problem sheets include both the formalization of
mathematical structures and exercises on proving related theorems.

Also included in AIL is the [Lean
Blueprint](https://mao3j1m0op.github.io/algebra-in-lean/blueprint/), which
provides a dependency graph of lemmas and definitions, a top-down view of
formalization progress, and a bottom-up view of individualized nodes. While this
problem set presents an extensive introduction to the formalization of algebra
and group theory mathematics, there is much left for future contributors. We
hope that others will add to the problem set in the future, including examples
related to quotient groups, group actions, Sylow theorems, ring theory, and much
more.

## Local installation

First you need to install Lean 4. Instructions for doing that are
[here](https://leanprover-community.github.io/get_started.html#regular-install).

Then you will need to clone this repository from github onto your computer. Open
up the same command line which you used to install Lean 4 and type:

```bash
git clone git@https://github.com/MAO3J1m0Op/algebra-in-lean.git
cd algebra-in-lean
lake exe cache get
```

Now open the folder `algebra-in-lean` which you just created, using
VS Code's "open folder" functionality. You will find all the exercises for the
course inside a subdirectory called `AlgebraInLean`.

## Contributors:

* Will Harris
* Justin Morrill
* Dominic King
* Adam Kern
* Clara Henne
* Arim Lim
* William Ho
* Stavan Jain
* Anoushka Sinha
* Ricardo Prado Cunha

## Credits

We thank Kevin Buzzard and his
[formalising-mathematics-2024](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024?tab=readme-ov-file)
repository for inspiring much of the infrastructure of this interactive problem
set.

We thank Dr. Colleen Robles for organizing and managing this project

We thank the Math+ program and the Duke Mathematics department for providing the
opportunity and the resources to work on this project.

This work was partially supported by NSF grants DMS-2003404 and ****
