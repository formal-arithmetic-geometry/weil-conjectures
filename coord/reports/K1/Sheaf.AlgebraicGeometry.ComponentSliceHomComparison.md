## What changed

The item now constructs `PullbackData` for W and every U directly from the existing
`component_pullback_unbounded_evaluation` theorem. It assembles its ordinary and derived
clauses from two separate, strictly partial steps, then proves uniqueness directly.
The uniqueness proof uses the inverse section identifications to compare arbitrary
sections on each w-contractible affine basis test. Naturality and the sheaf separation
condition extend equality to arbitrary tests; the module forgetful functor and
natural-transformation extensionality give equality of the isomorphisms.

The existing definitions, records and formulas moved unchanged to
`Sheaf.AlgebraicGeometry.ComponentSliceComparisonData`, publicly reexported by the item.
This avoids circular imports between the theorem and its split-off steps. All original
public dependency imports remain public through that module. The change record is
`coord/changes/component-slice-comparison-data-extraction.md`.

Searches used the prescribed LeanFinder, Loogle, grep and LeanSearch wrappers and scoped
source searches. The existing ordinary and derived component pullback-square statements
were also read: they use pullback presentations with adjunction-mate normalizations,
whereas this item's records demand literal slice restriction with a formula on every
w-contractible basis section. They do not directly supply that compatibility. The
existing ringed-site Hom results use a different sheaf-of-modules encoding, so the
normalization and encoding compatibility cannot be discharged merely by applying them.

Sources read: HRS Proposition 4.3(1), equation (4.2), pp. 8–9; Stacks
`sites-cohomology.tex`, `lemma-section-RHom-over-U`, `lemma-internal-hom`, and
`lemma-restriction-RHom-to-U`; the current blueprint's finite-Tor stability unit and
its internal-Hom proof. The unit route remains intact.

## Proved and sorry left

One original hole is replaced by a complete reduction:
`AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice.component_slice_hom_comparison_test`.
Its statement is unchanged. This is a decomposition, not a sorry-free proof of that
mathematical theorem: 1 original hole closed, 2 new holes added, net -1. The item itself
has 0 holes. The private helpers `pullbackData_nonempty` and `ordinaryComparison_unique`
are completely proved and introduce no holes.

Every remaining hole of this packet is a named public theorem, with source and complete
proof in words in its docstring and its own DAG node:

- `AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice.component_slice_ordinary_monoidal`
  in `Sheaf.AlgebraicGeometry.ComponentSliceOrdinaryMonoidal`, node
  `lem-sfb-component-slice-ordinary-monoidal`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice.component_slice_derived_normalization`
  in `Sheaf.AlgebraicGeometry.ComponentSliceDerivedNormalization`, node
  `lem-sfb-component-slice-derived-normalization`.

The first constructs only the ordinary coefficient/tensor-compatible square from fixed
component evaluation data. The second assumes such a square and constructs only its
normalized derived comparison. Neither constructs both ordinary and derived data, nor
asserts the original universal existence and uniqueness statement under another name.
The completed assembly additionally constructs the two component records and proves
uniqueness on the entire basis by sheaf descent.

Edge cases checked in stating these steps: the empty affine/test is allowed, as is the
zero condensed coefficient ring and zero input complexes. No nonemptiness, nonzero ring,
boundedness, perfectness or dualizability hypothesis is introduced. All integer shifts
remain in the derived comparison. The ordinary tensor structure on the scheme side is
the fixed `schemeCanonicalMonoidal`, whose equality clause is built into OrdinaryMonoidal.

## No longer needed

No module or mathematical node is withdrawn. The following unused plain proof imports
were removed from the item; their mathematics, where needed, remains in the split
steps' dependency plans:

- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`

The weakly contractible basis import is retained for the proved uniqueness argument.
The original node directly needs the existing evaluation and basis nodes and the two
new ordinary/derived steps. Its former other direct proof dependencies are now either
transitive through those steps or unnecessary for its record assembly. In particular
geometric exactness is already packaged in the existing evaluation theorem, so no
separate invocation is needed to construct dW or dU.

## Where the brief, the DAG or earlier work was wrong

The original proof plan calls its recorded
`lem-weil-pbc-ringed-internal-hom-exact-restriction` dependency a slice-Hom theorem, but
that node's current Lean attachment is `RingedHomUniverses.rightShift_existsUnique`,
which supplies a shift structure rather than a slice restriction isomorphism. The
separately stated derived normalization step instead records the existing normalized
slice evaluation/transpose statement as the relevant restriction dependency. No change
to that other node is attempted here.

`blueprint_refs.py ancestor lem-sfb-component-slice-hom-comparison-test` reports
`blueprint.from.node = None`, as already recorded on the source node. New nodes preserve
that null ancestor, the source's exact unit/chapter, and its full inherited via chain.
A whole-blueprint search for component slice returned zero matching blueprint nodes.

## New nodes

`def-sfb-component-slice-comparison-data` records the unchanged record types and formula
predicates extracted from the item. It asserts no existence and has no holes.

`lem-sfb-component-slice-ordinary-monoidal` isolates the construction by gluing normalized
basis section identities and checking pure tensors and the coefficient unit. Its source
is original proof steps 1–3, HRS (4.2), and Stacks 03DH/03EL.

`lem-sfb-component-slice-derived-normalization` assumes that ordinary square and isolates
its derived tensor, evaluation, section and shifted-Hom normalization. Its source is
original proof steps 3–7, HRS Proposition 4.3(1), and Stacks 07A4/08JA/08JB/08J9.

The definition extraction and consumer analysis are recorded in
`coord/changes/component-slice-comparison-data-extraction.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
