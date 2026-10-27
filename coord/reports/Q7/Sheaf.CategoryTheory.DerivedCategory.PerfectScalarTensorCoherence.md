## What changed

In `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence`, proved
`DerivedCategory.PerfectScalar.perfect_scalar_tensor_coherence_data`. Existence is
obtained by collecting the witnesses of the existing existential coherence theorem.
The new private, fully proved helpers establish uniqueness: cancel the model
comparison isomorphisms, identify tensor, coefficient-unit, tower and identity
components on bounded finite-projective models, and transport the equalities along
the model isomorphisms using naturality. Proof irrelevance handles the record's
propositional fields. The K-flat scalar-extension helper uses the existing
`CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat` theorem.

Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit` and
`WeilConjectures.Algebra.Homology.KFlatModuleBaseChange`. All existing public
imports, statements, definitions, attributes and docstrings are unchanged. No
consumer adaptation or definition change is required. The node retains its
original construction plan and adds the record-uniqueness argument and its
existing K-flat extension dependency.

The final module compiled through `lcompile.py` without errors or warnings
(43.1 seconds). The argument works for the separately quantified localization
universe, and uses actual isomorphisms and K-flatness without a flatness assumption
on the ring homomorphism; zero rings, zero models and identity maps are included.

## Proved and sorry left

Closed 1 of the module's original 2 holes:
`DerivedCategory.PerfectScalar.perfect_scalar_tensor_coherence_data`, attached to
`lem-sf-perfect-scalar-tensor-coherence`. Its uniqueness proof is complete; its
existence part uses the original existential coherence theorem.

Remaining 1 hole:
`DerivedCategory.PerfectScalar.perfect_scalar_tensor_coherence`, attached to
`lem-sf-perfect-scalar-tensor-coherence`. Its original statement, proof docstring
and `sorry` are retained. This is a partial delivery, not a proof of the whole
coherence construction. Added holes: 0. Split-off statements: 0. Every new private
helper is proved; no definition contains `sorry`.

## No longer needed

Removed the direct proof imports
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`, and
`Mathlib.RingTheory.Flat.Basic`. The retained imports already supply the bounded
flat and module-flatness interfaces used by the proof. Uniqueness only transports
along model isomorphisms; it does not require lifting arbitrary derived arrows to
chain maps, so it needs no direct K-projective Hom-bijection import.

No nodes or modules are withdrawn or claimed globally pruned. The original
thirteen-step plan and its dependencies remain needed for the existential theorem
still to be proved. The unit route and existing tool approvals are retained.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The record theorem needs a genuine uniqueness
argument in addition to repackaging existence. That argument can use its already
stated naturality for isomorphisms, rather than repeat the full Hom-bijection
construction. Some available general monoidal derived-functor APIs fix the
localization universe, so they do not directly specialize to this module's
independent universe parameter; the proof uses the existing universe-polymorphic
localization comparison maps instead.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
