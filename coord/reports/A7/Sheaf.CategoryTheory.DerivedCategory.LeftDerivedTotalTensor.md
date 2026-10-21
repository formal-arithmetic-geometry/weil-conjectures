## What changed

Filled the five theorem proofs in
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor`, preserving all public
signatures, definitions, docstrings, and public imports.

The private bridge proves that an additive endofunctor preserving ordered-integer
colimits preserves countable coproducts. The final functor `Int.toNat` first gives
preservation of natural-number colimits. Mathlib's final sequential functor to the
countable directed preorder of finite subsets then gives preservation of the
finite-subcoproduct diagram. Its finite comparison maps are isomorphisms by additivity;
the colimit comparison is therefore an isomorphism as well. This argument also covers
empty and finite index sets. It supplies the three graded tensor coherence families
required by the existing source K-flat machinery without adding hypotheses.

The two K-flat predicates are definitionally equal. A private preservation instance
therefore connects the given hypothesis to `Functor.derives_kFlat`. The source K-flat
left derivability structure and unary derived calculus prove existence, invertibility
of the canonical counit, and the characterization for arbitrary candidate counits.
Mathlib's canonical total-left-derived instance proves the universal property. The
resolution formula composes the inverse of the localized quasi-isomorphism with the
quotient/localization comparisons and the counit isomorphism.

Added only private proof imports:
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`,
`Mathlib.CategoryTheory.Limits.Constructions.Filtered`, and
`Mathlib.CategoryTheory.Filtered.Final`.
A declaration-scoped unused-section-variable linter setting preserves the original
source derived-category universe hypothesis of the existence theorem, although
its proof only needs the target derived category. No file-wide options were changed.
The item's node now records the countable-coproduct bridge and the conditional
resolution formula actually used. The unit's left-derived-functor route is retained. The change record
`coord/changes/A7-total-tensor-local-proof-instances.md` documents the local
instance attributes and lists all transitive importers; public interfaces are unchanged.

## Proved and sorry left

Closed all five original holes:

- `CategoryTheory.Functor.hasLeftDerivedFunctor_of_preservesTotalTensorKFlatQuasiIso`.
- `CategoryTheory.Functor.isLeftDerivedFunctor_leftDerivedFunctorFromTotalTensor`.
- `CategoryTheory.Functor.isIso_leftDerivedFunctorFromTotalTensorCounit_app`.
- `CategoryTheory.Functor.leftDerivedFunctorFromTotalTensor_obj_resolution`.
- `CategoryTheory.Functor.isLeftDerivedFunctor_iff_isIso_app_of_totalTensorKFlat`.

All have node `def-sfb-left-derived-functor`. No holes remain in the module, and no
holes or axioms were added. Every private helper is proved. This is a proof, not a
split into new admitted statements. The complete module compiled on the project
server cleanly (latest run 6.7 seconds). All three unchanged direct importers
compiled against this sandbox module: `LocallyFreeDerivedScalars` in 2.6 seconds,
`LeftDerivedTotalTensorExact` in 1.9 seconds, and `FlatSingleScalarConventions` in
8.0 seconds. The temporary identical consumer copies were removed after checking.
The final delivery probes the axioms of every declaration.

## No longer needed

The conditional resolution formula does not need
`lem-sfb-unbounded-kflat-resolution-existence`, module
`Sheaf.CategoryTheory.DerivedCategory.UnboundedKFlatResolution`: it already receives
the quasi-isomorphism and K-flatness as arguments. Removed that node from this item's
`proof_deps` and step 4. Resolution existence still enters the source derivability
structure; no claim is made that this node or module is globally unused.

No original import was removed, and no other planned dependency is pruned. The
sequential K-flat derivability, preservation, localization, and unary derived calculus
are all used through the existing source declarations.

## Where the brief, the DAG or earlier work was wrong

The sequential-K-flat-derivability node's current Lean record names the source
instance without giving a module. Its instance is in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`; it has graded tensor
coherence prerequisites in addition to the hypotheses displayed in this item. Those
prerequisites are proved here from the original assumptions, not assumed. No
statement repair or consumer adaptation is necessary.

The planned use of a separate resolution-existence theorem in the conditional
resolution formula was redundant. The explicit isomorphism proves the formula for
every supplied K-flat resolution directly.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
