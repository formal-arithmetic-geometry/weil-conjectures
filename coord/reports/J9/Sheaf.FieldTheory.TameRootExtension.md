## What changed

Proved `IsDiscreteValuationRing.tame_root_extension` with its public signature unchanged.
The private proved helper `tame_root_extension_integral_closure` embeds the standard
DVR root algebra into the explicitly constructed field F(alpha), identifies its
fraction field and integral closure, and computes the ramification index. The main
proof uses strict-local roots of unity, Mathlib Eisenstein and Gauss lemmas, and
Mathlib Kummer theory for the splitting field, cyclicity, Galois property and degree.
Added proof imports Eisenstein.Basic, GaussLemma, EnoughRootsOfUnity and Ideal.GoingUp.
Updated the existing node proof and dependencies to describe this argument.

## Proved and sorry left

Closed the one original hole, `IsDiscreteValuationRing.tame_root_extension`
(node `lem-exc-tame-root-extension`). No `sorry` remains in the item, and no hole
was added or split off. The private helper is also proved. The required dry run
compiled the module without warnings and passed the declaration axiom probe and
preflight. This is a proof of one original hole, not a decomposition.

## No longer needed

No original import, dependency module or node is removed. Retained RationalRoot
for the unique-factorization-domain integral-closedness instance. Removed the
redundant explicit IntegralClosure.IntegrallyClosed import from the retained
candidate; RationalRoot and GaussLemma already publicly import it.

The finite-module clause of `lem-weil-pbc-monic-quotient-free` remains needed
through `Monic.finite_adjoinRoot`; its explicit basis and the planned
coefficient-clearing calculation are unnecessary. Mathlib Eisenstein and Gauss
lemmas replace that calculation, using the existing Mathlib leaf
`lem-per-eisenstein-prime-ideal-criterion`. All original dependency nodes remain
used, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained candidate was complete but its report still marked compilation and
axiom validation as pending after earlier compile-server failures. Both checks now
pass. The DAG's original degree calculation is longer than needed because Mathlib
already proves the Eisenstein criterion and its fraction-field transfer.
No statement or definition repair was needed. The integral-closure helper works
for every positive m, including m=1, without residue-characteristic or henselian
hypotheses; those are used only for roots of unity in the main theorem.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
