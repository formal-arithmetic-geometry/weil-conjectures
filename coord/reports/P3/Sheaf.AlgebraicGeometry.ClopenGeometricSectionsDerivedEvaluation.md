## What changed

Completed the two proofs in
`Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation`.
The finite-clopen module-sheaf equivalence is constructed directly, with its
exact derived analogue. It detects K-injectivity componentwise and provides
the zero-complement resolution. The canonical derived adjunction and Yoneda
prove evaluation invertible. The sum-adjunction unit supplies the coproduct
universal property and hence the required biproduct isomorphism; full
faithfulness glues delta and proves its naturality and adjunct equations.
No nonemptiness or boundedness assumption is added.

Pinned the coefficient universe in the standalone global-sections equivalence
clause to `ModuleCat.{u + 1} A`. All public definitions are retained verbatim.
The change record is
`coord/changes/P3-clopen-geometric-sections-coefficient-universe.md`.
The downstream tool reported zero downstream modules; no consumer adaptation
is required. No target declaration or adopted-source declaration changes.

Repaired the return at 4c020aa80 by deleting the duplicate private theorem
`AlgebraicGeometry.module_single_product_projection`. The existing
`AlgebraicGeometry.Etale.singleProjectionIso` is made public in its unclaimed
Sheaf module, with exactly its existing binders and proof. A private proof
import supplies that theorem for all four former calls. No adopted source file
is changed. The visibility change and downstream analysis are recorded in
`coord/changes/P3-clopen-projection-helper-visibility.md`.

Updated the item's node proof and proof dependencies to match the categorical
argument. Added only proved private helpers in this module, with no new module.
The finite-fibre sum normalization required by the unit route is preserved.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Etale.clopenGeometricSections_union`.
- `AlgebraicGeometry.Etale.clopenGeometricSections_derivedEvaluation`.

Actual item hole count: 0. Holes closed: 2 of 2. Holes added: 0.
No split-off statements, no remaining sorry declarations, and no definitions
containing sorry. The repaired two-file packet compiled cleanly with `lcompile.py --all`,
with no warnings. The existing helper's module also contains zero holes;
its proof is unchanged. Delivery preflight supplies the final timing and axiom
checks under the unchanged per-file limit. The final witness-theorem version
compiled in 30.6 seconds; removed its unused coproduct section instance.
After an initial pushed repair reported a timed-out axiom probe, profiling
identified costly elaboration and attribute processing around the private
colimit constructions. Recast `module_clopen_complement_colimit` and
`module_sum_colimit` as proved `Nonempty (IsColimit ...)` theorems. Callers
choose a witness and use its universal property. This avoids exporting large
private data bodies; the public definitions and theorem statements are
unchanged. No existence assertion is left unproved. The attempted
irreducibility/no_expose changes did not solve the timeout and are omitted.


## No longer needed

Removed the following proof imports from the original item:

- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `lem-weil-pbc-kinjective-total-derived` is unnecessary for the direct Hom
  bijection proof using the already constructed canonical derived adjunction.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`:
  `lem-weil-pbc-exact-functor-derived-functor` is unnecessary; degreewise derived
  restriction and its composition comparisons already have the needed API.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`:
  `lem-pc-derived-adjoint-functors` is unnecessary as a separate black box;
  the source library provides the canonical adjunction used by the statement.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `prop-weil-pbc-inverse-image-modules-exact` is unnecessary as a separate
  theorem application; exact inverse image is already an instance in the API.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions` and
  `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`: the existing
  `Abelian.HasKInjectiveResolutions` instance supplies the resolution directly.
- Redundant direct imports of
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, already supplied by
  the retained public imports.

Also no longer used by this proof: `lem-weil-pbc-kinjective-hom-derived` and
`def-weil-pbc-direct-image`. Naturality follows from natural transformations
and full faithfulness, so no representation of derived morphisms by chosen
resolutions is needed. The abelian-valued
`lem-weil-pbc-etale-sheaf-clopen-product` and its module
`WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct` are not imported:
the necessary module-valued argument is proved directly with generic site
lemmas. These dependencies are removed from proof_deps/tool_uses; dependencies
still occurring in the unchanged statement remain recorded in stmt_deps.
No library module is withdrawn or deleted, and no upstream declaration is removed.
The duplicate private product-projection helper is no longer needed: all four
calls use the existing `Etale.singleProjectionIso`. The newly retained proof
import `Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels` supplies only
this categorical fact; its main geometric theorem is not used.

## Where the brief, the DAG or earlier work was wrong

The returned proof duplicated a generic product-projection theorem already
present privately in two modules. An ordinary import could not access either
private declaration. Exposing the existing helper in the unclaimed Sheaf
module resolves that reuse issue without altering its statement or proof.

The original standalone sections-equivalence clause generalized the module
universe independently, although the available geometric-point equivalence
and the rest of the theorem use the project coefficient universe u + 1.
The recorded repair fixes that clause without changing its mathematical content.

The DAG's chain-level computation is longer than needed. Canonical adjunction
naturality supplies the same normalized map directly, and the finite-clopen
restriction equivalence handles all derived morphisms. The unit's required
route through the actual finite etale sum and its specified injections remains.

The resumed sandbox budget metadata reports start 2026-10-23 07:14:11 UTC,
although the item was dispatched on 2026-10-22 and had earlier provider-error
resumptions. The worker did not modify the budget metadata.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
