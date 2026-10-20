## What changed

Prove `WeilConjectures.coefficientHomZeroEquiv_exists`, including naturality,
normalization by the actual zero-cycle class, and uniqueness. The proof uses the
canonical global Hom-complex comparison, the universal derived-sections unit,
K-injective comparison with derived morphisms, and localization descent.
K-flat representatives and surjectivity of the cycle-class map prove uniqueness.
The existing public declaration signatures are unchanged.

Prove the independent-universe K-flat-to-K-injective Hom theorem in the new module
`Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses`. Its complete proof constructs
the actual tensor-Hom adjunction, compares the signed Hom differential, and
transports null homotopies. No unfinished theorem is split off.

Make two definitionally equal presentation repairs to prevent repeated expansion
of chosen Hom-complex data: `coefficientHomSectionComplex` and
`coefficientHomZeroEvaluation`. The latter uses the recorded product component
through the unit-sections and internal-Hom sections equivalences. Proof imports
are private; no adopted `WeilConjectures` source file changes.

Repair the private projection presentation in the unclaimed
`HomComplexGlobalHomotopyOfUniverses`. The original source exceeded 60 seconds.
Use `homComplexπ` and its limit, differential, and naturality API in place of
repeated choice specifications. This is the same selected projection. Existing
signatures and public imports are unchanged.

The final sandbox build passed without warnings or errors: the assigned module
compiled in 53.2 seconds and the new auxiliary theorem in 36.3 seconds. The repaired
global-Hom module passed a fresh build in 31.7 seconds; the final build reused it.
The current unchanged sections-model consumer compiled in 6.5 seconds.
Three `rfl` checks validate the old and new section complex, evaluation, and private
projection bodies. The final proof optimizations leave those bodies unchanged.

The final axiom audit (1.5 seconds) lists only `propext`, `Classical.choice`, and
`Quot.sound` for all three public theorems: the assigned existence/uniqueness
theorem, the new K-injectivity theorem, and the global-Hom theorem. Temporary
validation files and unchanged consumer copies are excluded from the packet.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.coefficientHomZeroEquiv_exists`
(node `def-coef-hom-zero-cycle-class`).

Also proved the new source lemma
`CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses`
(node `lem-coef-hom-kflat-into-kinjective-independent-coefficients`).

Holes closed: 1. Holes added: 0. Holes remaining in the three delivered Lean
modules: 0. No axiom or admitted proof is added.

## No longer needed

No existing declaration, module, or node is withdrawn or pruned. The item's
original node had empty proof and proof-dependency lists. Its new route records
exactly the comparisons used in Lean.

The global-Hom module replaces its direct private `HomComplexProjections` import
by `HomComplexComponents`; the former is still needed transitively.
The original public `RhomGlobalSectionsOfUniverses` import stays for the statement
dependency. Its abstract isomorphism alone does not provide the prescribed
zero-cycle normalization.

A provisional private import of `DerivedInternalHomSectionsModel` was removed.
The final proof uses the independently proved auxiliary theorem and requires
neither its private lemmas nor temporary compiled dependency overrides.

## Where the brief, the DAG or earlier work was wrong

The original node had no proof plan. It now records the actual derived unit,
localization comparison, normalization calculation, and uniqueness argument.

The adopted K-flat-to-K-injective theorem at coefficients `max c v` does not
instantiate at `max c v u`. The new source lemma proves this independent-universe
case without additional mathematical hypotheses.

An earlier local check reused a temporary compiled sections-model dependency
containing a private lemma absent from the current repository source. Clean-cache
validation exposed this. The final packet includes the independent proof instead
and has no dependency on that temporary artifact.

An arbitrary RHom/global-sections isomorphism would not establish the required
normalization. The construction uses the actual global cochain comparison and
localization factorization throughout.

## New nodes

`lem-coef-hom-kflat-into-kinjective-independent-coefficients` formalizes Stacks
Tag 0A96 for arbitrary unbounded complexes and independent coefficient universes.
Its full signed-comparison and tensor-Hom null-homotopy proof is included, with
zero holes. Zero complexes and an empty site require no exclusions.

Definition change records:
`coord/changes/D4-zero-cycle-section-complex-api.md`,
`coord/changes/D4-zero-cycle-evaluation-api.md`, and
`coord/changes/D4-global-hom-projection-api.md`.
Their old/new bodies and current users are listed. Targets depending on the two
public definitions are reopened for independent statement review of their
definitional equalities. No consumer needs an adaptation.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
