## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etaleSupportMapCompatibility` with a
proof from the existing normalized compact-support comparison, the right-derived
single-complex H0 comparison, the source library's etale projection theorem, and
one separate graph tensor evaluation lemma. The existing statement and both existing
auxiliary definitions are unchanged. No source-library module was changed.

The proof establishes invertibility of the sheaf comparison by applying H0 to its
homotopy normalization. It proves invertibility of the specified reverse projection
mate by monoidal transport and braiding. An explicit counit/naturality calculation
transposes the graph tensor equation, followed by cancellation. The existing
unbounded refinement normalization and cocycle law prove the final clause.

Updated the parent node's proof, dependencies, proof origin, and obsolete tool-use
entries. Added `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor` and its node.

Validation: the item module compiles through `lcompile.py` in 35.6 seconds, with
no warnings. The graph lemma statement also compiles; its only warning is its
explicit named sorry. Both existing definitions and the theorem signature were
compared verbatim with the repository, and every delivered Lean line is at most
100 characters.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Etale.etaleSupportMapCompatibility`
(`lem-pur-etale-support-map-compatibility`). Its complete combining proof uses the
new lemma below. The item module itself has zero sorry.

Added one hole:
`AlgebraicGeometry.Etale.compactSupportGraph_tensor_evaluation`
(`lem-pur-compact-support-graph-tensor-evaluation`). This isolates the geometric
tensor identity from Step 8 of the original plan. It asserts only the evaluation
identity for a fixed compactification and fixed pair of derived objects, with the
sum tensor mate specified by its adjunction-unit equation. It does not assert
invertibility, exchange compatibility, sheaf normalization, existence of the
comparison families, or refinement compatibility.

This is a decomposition, with one hole closed and one added (net zero), not a
claim of a sorry-free proof. All private helpers are proved. There are no holes
inside definitions and no new axioms.

## No longer needed

Removed the following direct imports from the item module:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.AlgebraicGeometry.EtaleSumStalks`
- `Mathlib.Algebra.DirectSum.Module`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.BaseChange.Etale`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`
- `Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap`
- `Sheaf.Paper.EtaleSumTensorTotalization`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`

The original public imports are retained so that existing importers see the same
statement interface. The list above removes proof-only imports for unused routes.

Removed these direct planned proof dependencies from the parent node:

- `def-amb-etale-compact-support`
- `def-kun-unbounded-exchange`
- `def-weil-pbc-etale-shriek-base-change-map`
- `def-weil-pbc-etale-sum-extension`
- `def-weil-pbc-inverse-image`
- `def-weil-presheaf-modules-sheafification` (retained in the graph tensor lemma's proof plan)
- `lem-amb-etale-adjoint-locality`
- `lem-cbc-proper-support-sheaf-composition`
- `lem-pc-kflat-resolution` (retained in the graph tensor lemma's proof plan)
- `lem-pod-separated-finite-type-base-change`
- `lem-pur-etale-open-derived-tensor` (retained in the graph tensor lemma's proof plan)
- `lem-pur-etale-sheaf-projection-map` (retained in the graph tensor lemma's proof plan)
- `lem-pur-etale-sum-flat-kflat` (retained in the graph tensor lemma's proof plan)
- `lem-pur-etale-sum-tensor-totalization` (retained in the graph tensor lemma's proof plan)
- `lem-sfb-quasifinite-compact-support-exact`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-section-clopen-immersion`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `lem-weil-pbc-etale-underived-exchange-restriction`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-localization-universal-property` (retained in the graph tensor lemma's proof plan)
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-section-separated-closed-immersion`
- `lem-weil-pbc-separated-base-change`
- `lem-weil-pbc-site-derived-tensor-descent` (retained in the graph tensor lemma's proof plan)
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `prop-weil-pbc-inverse-image-modules-exact`

Their sheaf graph and base-change reconstruction is replaced by the existing
normalization fields; projection invertibility uses the already proved source
theorem. This is removal from this proof route, not authorization to delete any
source declaration or globally withdraw a module. Some remain transitive
statement or proof dependencies of imported modules. No module is withdrawn.

Removed these obsolete parent `tool_uses` entries, retaining the order of all
remaining entries:

- `def-weil-pbc-inverse-image`
- `lem-amb-etale-sum-stalks`
- `lem-cbc-proper-support-sheaf-composition`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-pod-separated-finite-type-base-change`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-section-clopen-immersion`
- `lem-weil-pbc-etale-underived-exchange-restriction`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-section-separated-closed-immersion`
- `lem-weil-pbc-separated-base-change`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lemma-weil-pbc-geometric-stalk-conservative`

## Where the brief, the DAG or earlier work was wrong

The original Step 8 contains a genuinely additional geometric equality, not a
consequence merely of invertibility of the projection map. None of its listed
Lean dependencies states that graph-evaluation tensor equality. The new node
records it explicitly rather than treating tensor compatibility of an arbitrary
isomorphism as automatic. Its statement fixes the normalized comparison, preserves
the tensor-factor order, and uses localization in the two sites separately; no
faithfulness of stalks on derived morphisms is assumed.

The sheaf comparison's invertibility need not repeat the graph support argument:
it follows from the supplied derived normalization and the existing H0 theorem.
The existing all-coefficient projection theorem likewise avoids repeating the
sum/stalk/totalization argument solely to establish projection invertibility.

No target statement, definition, or unit route was changed. The assigned unit's
`realized` list is empty. No forced adaptation is needed. The conservative local-command interface check
requires the change record listed below.

## New nodes

`lem-pur-compact-support-graph-tensor-evaluation`, in
`dag/nodes/sec-smooth-purity/lem-pur-compact-support-graph-tensor-evaluation.json`,
realized by `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensor`. It is the
fixed-object graph tensor evaluation identity of Step 8, expanded from Stacks
Tags 0F4L, 0GKF and 0GL5. The docstring gives the sheaf calculation, K-flat
totalization and two-variable localization argument. The unit equation uniquely
specifies the reverse sum tensor mate, so the quantified arrow introduces no
choice of an unconstrained map. Empty schemes and zero objects give the zero
identity; for the identity compactification it reduces to the tensor unit/counit
law. No flatness or boundedness hypotheses have been added.

Change record: `coord/changes/etale-support-proof-local-commands.md`, documenting
the added namespace opening, elaboration options and strictly local attributes.
Existing definitions and public signatures are unchanged.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
