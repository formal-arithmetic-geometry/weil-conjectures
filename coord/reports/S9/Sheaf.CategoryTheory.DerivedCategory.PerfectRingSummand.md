## What changed

Proved `DerivedCategory.isPerfectRingComplex_summand` in
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingSummand`, with its signature and
public imports unchanged. The proof obtains pseudo-coherence by finite-free
replacement and `pseudoCoherent_summand`, obtains a Tor interval using the already
proved `torAmplitudeIn_Q_obj_of_flat`, transfers it through the two explicit
biproduct retracts, and applies the existing pseudo-coherent finite-Tor perfectness
criterion to each summand. The final conversion uses Mathlib's strict-support
characterizations. Updated the docstring and existing node's proof route.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` and
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat` for the bounded-flat
Tor-amplitude theorem and the equivalence of categorical and module flatness.
No definitions, statements, other modules, or public interfaces changed.

The module compiled cleanly through `lcompile.py`. A temporary `#print axioms`
probe reported exactly `[propext, Classical.choice, Quot.sound]`; the probe was
removed before delivery. Bounds use `[min a b, b]`, so the criterion's ordered
interval hypothesis also holds when the original perfect-model witness has
`a > b`. Zero rings, zero summands, and non-free finite projective terms require
no additional hypotheses. The independent localization universe is preserved.

Mathlib searches through `msearch.py` used LeanFinder (direct summand of a perfect
complex: K-projectivity and projective-dimension results only), Loogle
(`DerivedCategory, CategoryTheory.Retract`: zero hits), and grep
(`perfect.*summand|summand.*perfect`: zero hits). Reading the library found the
proved bounded-flat Tor-amplitude theorem and existing retract instance used here.

## Proved and sorry left

Closed 1 of 1 holes: `DerivedCategory.isPerfectRingComplex_summand`
(node `lem-sf-perfect-ring-summand`). Remaining holes: none. Added holes: none.
Split-off statements: none. The theorem's full axiom closure is sorry-free.

## No longer needed

Removed proof-only imports:

- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`, node
  `lem-pc-module-bounded-flat-kflat`: no direct application is needed because
  `torAmplitudeIn_Q_obj_of_flat` packages the bounded-flat computation. This is a
  pruning of this item's direct dependency, not a claim that no other node uses it.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`, node
  `lem-pc-derived-tensor-second-factor-functor`: arbitrary second complexes and
  coefficient changes are unnecessary for Tor tests by modules in degree zero.
  The existing derived monoidal tensor computes these tests directly.

Removed those two obsolete top-level `tool_uses` entries and their direct
`proof_deps` entries. The existing node
`lem-trf-source-bounded-flat-tor-amplitude` records the proved bounded-flat source
lemma replacing these explicit steps. No new nodes or modules were introduced.
All other original proof dependencies remain in use. The concrete Tor-amplitude
retract instance implements the elementary retract step already in the plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The plan's separate
K-flat computation and explicit cohomology retract calculation were already
packaged by proved generic library results. The direct derived-category
`pseudoCoherent_summand` theorem also avoids choosing complex representatives.
The definition of perfectness does not require ordered support bounds, whereas
the final criterion does; widening to `[min a b, b]` resolves this without any
change to either statement. The unit's route remains unchanged.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
