## What changed

Proved all five holes in `Sheaf.Paper.InternalSliceDerivedHomComparison`.
The section-ring equality follows from ring and functor extensionality and the native
continuous-pushforward tensor equation. Additivity uses preservation of binary products
by an equivalence. The raw comparison specializes the existing normalized tensor theorem.
The total comparison transports its fixed raw isomorphism through equality of section-ring
presentations, with explicit functor rewrites and uniqueness from heterogeneous equality.
The native derived monoidal equality is reflexivity at an abstract category, specialized
to the slice module category.

Factored the ordinary tensor choice through the proved `sectionTensorWitness` and
`sectionOrdinaryTensorIso`, retaining pure-tensor normalization and the total summand
formula together. This removes unused coherence and flatness clauses from the choice
predicate and avoids expensive repeated kernel type comparisons. Both selected objects
are uniquely fixed by those normalizations. The two choice definitions infer their unchanged canonical endpoint types.
Named proofs of graded tensor coproduct existence and associativity compatibility keep
repeated instance arguments atomic, avoiding expensive kernel comparison of nested proofs. All existing
theorem signatures and the mathematical native constructions are preserved.

Added proof-only imports of `WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal`
and `Mathlib.Algebra.Ring.Ext`; updated the existing node's proof and proof dependencies,
and attached the public normalization and graded-tensor helpers to that definition node.
The generic witness is a projection of an already-stated dependency, with no new mathematical obligation.
Definition-change record: `coord/changes/R2-slice-tensor-choice.md`.

The only downstream consumer, `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`,
has its concrete reflexivity proof of `internalMonoidal_eq_localization` replaced by
application of a private copy of the abstract native equality. Its signature, its main theorem
and its one existing hole are unchanged. The module is unclaimed; this is a compile-time
repair, with no forced adaptation of a held module.
Validation timings are recorded below after the final checks.

## Proved and sorry left

Closed five original holes:

- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sliceSectionRing_eq`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sliceEquivalence_additive`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sliceRawComplexTensorComparison`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sliceTotalComparison_existsUnique`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sliceMonoidal_eq_localization`.

Zero holes remain in the item, zero holes were added, and zero results were split off.
The consumer retains its original hole
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`.
The existing `internal_section_tensor_comparison` remains a declared proof dependency;
this delivery proves its specialization and glue, as required by stage 3.
All helpers are fully proved or constructed. There is no new axiom or
unproved data construction.

## No longer needed

Removed this item's public import of
`Sheaf.Paper.InternalSectionDerivedTensorComparison`: none of its four declarations is
used by the slice interface or these proofs. Its module and node remain needed by
`Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, which imports it directly.
No module or DAG node is withdrawn. The source tensor theorem and its own dependencies
remain needed; discarding clauses from the local choice predicate does not prune them.
The item's earlier proof and proof-dependency lists were empty, so there is no abandoned
numbered proof route or unused planned lemma to remove.

## Where the brief, the DAG or earlier work was wrong

The existing statements were usable and no statement was disputed. The concrete
choice predicate and repeated concrete graded-tensor instance proofs caused repeated
kernel comparison of large dependent monoidal types,
so it needed the definition factorization documented in the change record. Direct
elimination of the concrete section-ring equality also fails dependent elimination;
varying its presentation in a separate family and rewriting by the explicit functor
equality gives the required transport without unfolding native tensors.

The proof applies to zero coefficient rings, arbitrary slice objects and unbounded
complexes; it adds no nonzero, flatness, boundedness or finiteness hypothesis. The unit's
realized statement and step routes are unchanged. No adopted source-library file changes.
No new nodes are necessary: the generic witness theorem is a proved projection of the
existing tensor-comparison dependency and is attached as a helper of the existing
slice-comparison definition.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
