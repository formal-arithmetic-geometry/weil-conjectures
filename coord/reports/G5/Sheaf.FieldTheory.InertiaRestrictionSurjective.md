## What changed

Proved `Ideal.inertia_map_restrictNormalHom` in
`Sheaf.FieldTheory.InertiaRestrictionSurjective`, preserving its full signature and public
imports. The proof follows the source's lift, prime correction, and residue correction
argument, directly on the two integral closures. The invariant ring of the action of
`Gal(M/L)` on the upper closure is the lower closure, by infinite Galois fixed fields
and descent of integrality. The action is continuous for the discrete integral closure,
since element stabilizers are open. Mathlib's profinite invariant-ring lemmas supply
both corrections on prime ideals and quotient rings, with no finiteness or maximality
assumption. The quotient-ring action suffices for inertia, so residue fraction fields
and comparison with a second presentation of the integral closure are unnecessary.

Added private proof imports `Mathlib.FieldTheory.Galois.Infinite`,
`Mathlib.FieldTheory.Galois.Profinite`, and `Mathlib.RingTheory.Invariant.Profinite`.
Updated the proof docstring and the item's DAG proof, proof dependencies and proof origin.
No other module, definition, statement, or public interface changed; no new nodes.

Validation: the proof compiled successfully on the server (7.0 seconds). The delivery
command compiles the final packet and checks axioms during server preflight. The first
successful delivery compile reached preflight, which requested a change record for a
module-level `open scoped Pointwise`. Repaired by supplying the pointwise action instances locally in the proof,
preserving the public interface. A term-level scope opening did not activate those
instances during elaboration and was replaced by explicit local instances. Earlier busy-server compile requests and
delivery attempts received no answer and pushed nothing. Static checks confirm the
signature and public imports are unchanged, line widths are at most 100, and the DAG
proof dependencies equal the union of its proof-step uses.

## Proved and sorry left

Closed the sole original hole: `Ideal.inertia_map_restrictNormalHom`
(node `lem-dl-a1-inertia-restriction-surjective`). Proved 1 of 1 original sorries.
Added 0 holes; split off 0 statements; 0 sorries remain in the delivered Lean module.
All proof dependencies used by the final proof are proved Mathlib declarations.

## No longer needed

Removed private import `Mathlib.RingTheory.Localization.Integral`.
The proof does not need the planned dependency
`lem-weil-pbc-integral-closure-algebraic-extension-normal`: it works directly with
invariant rings and quotient rings, avoiding fraction fields of the integral closures
and normality of those closures.

The proof does not need `lem-dl-a1-galois-prime-residue-lifting` or its module
`Sheaf.FieldTheory.GaloisPrimeResidueLifting`. Instead it applies the existing Mathlib
leaf `lem-dl-a1-profinite-invariant-ring-primes` directly to the action on the original
upper closure. No need to transport to the integral closure of B in M or to compare
residue fraction fields. These dependencies are removed from this node's proof route;
no claim is made that other library consumers no longer need them. Neither module
was imported in the original item. No modules or declarations are withdrawn.

Retained field restriction surjectivity, Galois-over-intermediate, and integral-closure
definitions from the stated plan. Added existing Mathlib leaf nodes for infinite
Galois fixed fields, Krull profiniteness, finite-group limits, and profinite invariant
rings. The unit record has no realized statement or steps, so no fixed unit step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned passage to residue fraction fields and the integral
closure of the lower closure is unnecessary for the quotient-ring definition of
inertia. The finite-tower private proof in
`Sheaf.FieldTheory.FiniteTameCharacterTower` gives the same algebraic argument;
its finite-group lifting lemmas are replaced here with their proved profinite analogues,
and the fixed-field lemma is the infinite version. That module is used only as a
proof reference and is not imported or modified.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
