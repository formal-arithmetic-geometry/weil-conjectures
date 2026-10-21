## What changed

Proved `SheafOfModules.constantScalar_injective_of_flat` in the assigned module, with its
public signature and all public imports unchanged. Added one proved private helper,
`constantScalar_ring_injective`. No definitions or consumers changed.

The ring argument embeds A into A[1/a]. Left exact ring sheafification preserves this
monomorphism, and naturality sends the constant scalar to a unit in the target sheaf.
The module argument applies the already proved local finite relation criterion to the
single relation a(s-t)=0. Ring regularity makes the local factorization coefficients
zero; separatedness then gives s=t. This is shorter than constructing a new tensor
unitor and its scalar compatibility in independent universes.

Added proof imports for `FlatLocalRelationsOfUniverses`, `Mathlib.RingTheory.Localization.Away.Basic`
and `Mathlib.Algebra.Category.Ring.Limits`. Updated only `proof`, `proof_deps` and
`proof_origin` of `lem-sfb-flat-constant-module-scalar-mono` to match the Lean proof.
The integral-model unit and its scalar cyclic resolution parent are preserved.

Remote single-file compilation passed in 3.2 seconds. A temporary `#print axioms` check
reported exactly `propext`, `Classical.choice`, `Quot.sound`; the check command was then
removed. Checked the original and final public signatures textually: identical.

## Proved and sorry left

Closed 1 of 1 holes: `SheafOfModules.constantScalar_injective_of_flat`
(node `lem-sfb-flat-constant-module-scalar-mono`).

Holes added: zero. Holes remaining in the delivered module: zero. No split-off statements.
The private helper is fully proved, and the local relation theorem used by the main proof
is already proved. The complete axiom check confirms no transitive `sorryAx` dependency.

## No longer needed

Removed the original proof imports:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

The item's direct DAG proof dependencies no longer include
`lem-weil-pbc-sheafification-exact`,
`lem-pc-sites-module-sheafification-interface`,
`def-pur-sheaf-tensor-product` or
`lem-sp-exact-functor-preserves-homology`.
Their specific planned constructions are unnecessary here: ring sheafification is used
directly, and the local relation criterion supplies the required consequence of flatness.
Tensor and module sheafification infrastructure remain transitively needed by that existing
criterion; this report does not request their withdrawal. No whole module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The old route was longer than necessary.
The hypotheses already provide left exact CommRingCat sheafification, allowing the
localization argument without identifying ring and abelian sheafification.

The proof uses `lem-weil-pbc-flat-local-relations-universes` as an already Lean-closed tool
from another unit, not as a replacement for an integral-model unit step. Its statement
fits all the independent universes and does not assume sectionwise module flatness.
Its source was checked at Stacks Tag 08FC, `sites-modules-lemma-flat-eq`, implication
(1) to (2); the localization fact is the existing Mathlib leaf
`lem-pc-affine-localization-injective`.

Edge cases retain the same argument: a unit, a regular zero divisor-free element in a
ring with other zero divisors, the zero ring, the zero module and an empty covering sieve.
In particular, if a=0 the hypothesis forces A to be the zero ring; the localization and
unit cancellation proof still applies. No domain or enough-points assumption was added.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
