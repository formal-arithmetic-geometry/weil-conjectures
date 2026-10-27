## Worker report

The new module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality` states
`AlgebraicGeometry.AlgebraicSpace.flat_proper_fp_locality`. Its sole theorem has
proof `by sorry`. No definitions, auxiliary theorem obligations, new nodes, or
dependency repairs are needed. The source statement is unchanged.

Clause-by-clause correspondence:

- The base scheme and size convention are `{S : Scheme.{u}}`, with explicit
  universes `u w` and `set_option autoImplicit false`. All spaces are the recorded
  `AlgebraicSpace S`, namely the full subcategory of big-fppf sheaves, and all
  morphisms are its actual sheaf morphisms.
- Each property is treated independently: `P : MorphismProperty (AlgebraicSpace S)`
  and `hP` select `MapIsFlat`, `MapIsProper`, or the lambda expressing finite
  presentation. The disjunction is a choice of property, not assumptions that
  flatness, properness, and finite presentation hold together.
- Flatness is the existing `MapIsFlat`: `MapIsLocally (@Flat)` quantifies over
  every compatible pair of representable étale scheme charts. Local finite
  presentation is `MapIsLocallyOfFinitePresentation`, with the same chart test
  using the dependency's `LocallyOfFinitePresentation`.
- Finite presentation is written out as
  `MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
  MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. This includes all three
  conditions, in particular quasi-separatedness; no second notion is introduced.
- `MapIsProper` unfolds to separated, finite type, and universally closed.
  `MapIsSeparated` uses `IsRepresentableWith` for closed immersions of all scheme
  tests of the diagonal. `MapIsFiniteType` is quasi-compactness and the chart
  test of `LocallyOfFiniteType`. `MapIsUniversallyClosed` requires `IsClosedMap`
  on field-valued point classes after every algebraic-space base change.
- The first conclusion universally quantifies over arbitrary `X Y Y'`, `f`, and
  `g : Y' ⟶ Y` and asserts `P f → P (enlargedFibreProductFst g f)`.
  No finiteness, representability, flatness, or separation condition is imposed
  on the base-change arrow. The displayed map is `Y' ×_Y X → Y'`, the canonical
  first projection of the actual sheaf fibre product (the reversed factor order
  is canonically isomorphic to `X ×_Y Y' → Y'`).
- For the locality conclusion, `T : Over S` is an arbitrary scheme over the common
  base and `f : X ⟶ schemeSpace T` is an arbitrary morphism to it. `Tᵢ : I → Over S`
  and `g : ∀ i, Tᵢ i ⟶ T` encode precisely the family over this scheme.
  `Presieve.ofArrows ... ∈ Scheme.fppfPrecoverage T.left` means joint
  surjectivity, flatness, and local finite presentation of the scheme cover maps.
- The conclusion `P f ↔ ∀ i, P (...)` is the requested equivalence. Its pullback
  arrow uses `yoneda.map (g i)` bundled through `ObjectProperty.homMk`, hence is
  exactly the original scheme arrow viewed as a map of representable sheaves.
  Its source is the sheaf fibre product with `X`; it is never assumed to be a
  scheme or replaced by an arbitrary isomorphic carrier.
- Points and topology are the existing `Point`, `mapPoint`, and
  `pointTopologicalSpace`: common-field-extension classes with the final topology
  of representable étale scheme charts. The latter is the quotient topology of
  any surjective étale atlas. The existing `MapIsQuasiCompact` tests compact point
  spaces after affine scheme base changes. This is equivalent to the convention
  in the item, rather than an extra hypothesis: Stacks spaces-properties.tex,
  `lemma-quasi-compact-space` (Tag 03E4), identifies compact point space with a
  quasi-compact surjective étale scheme atlas; spaces-morphisms.tex,
  `definition-quasi-compact` and `lemma-quasi-compact-local` (Tag 03KG), identify
  affine tests with all quasi-compact space tests. For the reverse direction,
  choose a quasi-compact scheme atlas of the test space, cover it by finitely many
  affine opens, apply the affine tests, and compose/assemble their finitely many
  quasi-compact atlases. Conversely any affine test is itself a quasi-compact
  space test. Thus finite type, properness and diagonal quasi-compactness use
  exactly the requested meanings, without a private replacement definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (equivalent stalkwise form).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed`; these scheme meanings underlie the reused space predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`. The theorem uses membership in the generating precoverage,
  which is exactly the given family condition, not just a generated covering sieve.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, with no Hausdorff assumption.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `IsJointlySurjective`; it supplies the point-lifting convention in the proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and the actual sheaf fibre products.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsUniversallyClosed`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, `mapPoint`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` supplies
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, owned by the landed definition
  node `def-trf-scheme-algebraic-space`, and `enlargedFibreProduct` and
  `enlargedFibreProductFst`, owned by the landed definition node
  `def-sfb-space-sheaf-fibre-product`. These are actual Yoneda sheaf and sheaf
  pullback constructions, not data extracted from the enlarged-site theorem.
  The item cites these two definition nodes alongside the landed predicate nodes
  `def-sfb-space-morphism-properties` and `def-sfb-proper-curve-moduli`.

All available stated proof dependencies are imported, preferring upstream modules
for the fpqc flatness and local finite-presentation lemmas. The two proof inputs
`lem-sfb-space-local-properties-chart-test` and
`lem-sfb-space-quasicompact-fppf-local` have no Lean record; they are named in the
full nine-step proof docstring but are not required for elaborating this statement.
The docstring preserves the accepted proof's diagonal scheme-test argument,
chart-composition justification and constituent proof of proper base change.

Edge cases checked before writing and again on the final signature: an empty
index type is allowed (`I : Type w`, no `Nonempty` binder); its covering condition
forces an empty target, hence empty source. Empty atlases and compact empty point
spaces satisfy each property. Identity base change is included. Flatness does not
require finite presentation or properness; the properness case does not assume
flatness of `f`; the finite-presentation case does not assume separatedness.
The scheme target need not be affine or quasi-compact, and the cover need not be
finite or a singleton. No equality of independent universe levels is imposed.

Searches (2026-10-24; msearch outputs also recorded in sandbox searches.jsonl):

- `msearch.py ... leanfinder "Flat proper finite presentation morphisms of algebraic
  spaces stable under base change and fppf local on target"`: eight results,
  including scheme flat/lfp/lft base-change instances and scheme flat descent;
  no algebraic-space result matching the item.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace,
  AlgebraicGeometry.Flat, AlgebraicGeometry.IsProper"`: zero results; unknown
  Mathlib identifier `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py ... grep "AlgebraicSpace|algebraic.space" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Flat proper finite presentation morphisms of
  algebraic spaces are stable under base change and fppf local on the base"`:
  eight scheme/ring/module results, no matching space theorem.
- `rg` in live `lean/WeilConjectures/AlgebraicGeometry` and Mathlib's
  `AlgebraicGeometry` for `AlgebraicSpace|algebraic.space`: no hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id: no declaration.
  Searches for `MapIsFlat|MapIsProper|MapIsQuasiCompact|MapIsFinitePresentation`
  found the reused space definitions; finite presentation is already written
  inline in `AlgebraicSpaceClosedStructureFinitePresentation`, so it stays inline.
  The nearby `four_property_fppf_descent` concerns affine/finite-type/quasi-finite/
  separated, and does not state any of the three properties of this item.
- `rg` for the proposed theorem name in Mathlib, upstream, and Sheaf: no collision.

Validation: prescribed `scompile.py Q149 lem-sfb-space-flat-proper-fp-locality
<module>` passed sandbox and actual-module compilation (12.9 s and 9.3 s), with
no compiler diagnostics. Maximum Lean line length is 88. No statement dispute,
statement correction, missing notion, or dependency repair was found.

## Second reading by Q149

I performed a separate second pass over the unchanged node and final module; no
other agent was started, as required by the dispatcher brief. I checked both
conjuncts, the three alternatives of `hP`, and expanded the reused predicates.
The comparison confirmed that the finite-presentation alternative includes the
quasi-compact diagonal, that properness uses arbitrary-space universal
closedness, and that the cover's flatness/lfp applies only to `g i`.
I traced the bundled Yoneda arrow to `(g i).left` and checked that
`enlargedFibreProductFst g f` projects to the new base, not to `X`. I separately
checked the affine-test/atlas/all-space quasi-compactness equivalence against
the cited Stacks source and recorded the argument above. No mismatch required
a change to the Lean signature or natural-language statement. The node changes
only `lean` and the addition of the four existing landed definition nodes to
`stmt_deps`.


## Repair of returned delivery 1576fb5ca8bd

H2 is repaired: `lem-trf-space-enlarged-etale-ringed-site-model` is removed from
`stmt_deps` and replaced by `def-trf-scheme-algebraic-space` and
`def-sfb-space-sheaf-fibre-product`. I read both landed nodes and their existing
Lean records, then the full docstrings and bodies of `schemeSpace` (line 79),
`enlargedFibreProduct` (line 230) and `enlargedFibreProductFst` (line 236) in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. They are exactly the
representable sheaf, sheaf pullback and first projection used in the signature.
The module now imports `EnlargedEtaleRingedSite` directly in place of
`AtlasEtaleRestriction`.

The saved packet's initial dry run passed (commit ab76145cf77); that mechanical
pass did not resolve the ownership defect found by the independent review.
Compared with the current live node, this packet retains every field except
`lean` and the authorized additions of landed definition nodes to `stmt_deps`.
Compared with the retained returned packet, only the import, those two replacement
dependency references, and this report change. The Lean signature and all nine
proof-docstring steps are unchanged. There are no new nodes or dependency modules.

For the repair self-check I reread the complete theorem and current natural-language
statement. `hP` selects one of the three properties independently; the first
conjunct quantifies over every algebraic-space base change; the second over every
scheme fppf covering with arbitrary `I : Type w`. The actual first projection has
the new base as target in both clauses. The empty, infinite and non-affine cases
remain included; finite presentation still includes quasi-compactness of the
relative diagonal. No mathematical mismatch or further change was found.


Repair validation (2026-10-24): the prescribed `scompile.py` compiled the repaired
module both as a sandbox module (2.2 s) and under its actual library name (2.1 s),
with no diagnostics. The self-check confirms that the recorded signature matches
the source verbatim, there is exactly one `sorry`, all Lean lines fit within 100
characters, and only the allowed `lean`/`stmt_deps` fields differ from the live node.
