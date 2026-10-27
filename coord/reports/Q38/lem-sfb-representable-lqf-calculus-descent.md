## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus` states
all five clauses of the item, with five named theorems whose entire proofs are `sorry`.
There are no new definitions, no dependency repairs, and no statement correction.
The accepted stage-1 proof is preserved. The previous worker's stage-1 live-wins refusal
is inapplicable: the live item is split and reviewed, has no Lean record, and is queued
for stage 2. This is the handoff explicitly covered by brief-stage2 §0.

### Hypotheses and clauses

* The base scheme is `{S : Scheme.{u}}` throughout. Every universe is explicit;
  the independent stack object/morphism universes are `v₁,w₁,v₂,w₂,v₃,w₃`.
  The open-cover index has its own universe `z`, without any bound or nonemptiness
  restriction. These are the size convention's ordinary universe-polymorphic objects.
* Algebraic stacks are the binders `hA`, `hB`, and (where a third stack occurs) `hC`
  of type `IsAlgebraicModuliStack`. The category over the base is `BasedCategory (Over S)`;
  maps are `BasedFunctor` and the actual triple construction is `moduliTwoFiberProduct`.
* Representability of the given maps is `IsRepresentableByAlgebraicSpaces f` (and
  `g` or `q` where appropriate). Every occurrence of representable local quasi-finiteness
  uses `ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite`. This already asserts an
  algebraic-space presentation of every scheme base change with the correct projection,
  and tests every representable étale scheme chart. Its finite-type clause is the
  recorded Stacks predicate, not Mathlib's weaker `LocallyQuasiFinite`.
* `representable_lqf_baseChange`: given `f : A → B` and arbitrary `g : C → B`,
  `hq` asserts the local quasi-finiteness of `f`; the conclusion asserts it for the
  actual projection `moduliTwoFiberFst g f : C ×_B A → C`. There is no property of `g`.
* `representable_lqf_comp`: `hfq` and `hgq` are exactly the local quasi-finiteness of
  the two composable representable maps; its conclusion is that of `f.comp g`.
* `representable_lqf_openCover`: `U : I → OpenModuliSubstack A` is the family of opens.
  `hcover : ∀ x : ModuliFieldObject A, ∃ i, (U i).property x.val` says every field point
  lies in a member. This is equivalent to covering every scheme test: its residue-field
  points detect whether the pulled-back open subschemes cover it. Conversely a field
  scheme has one point, so a covering open contains its entire field-valued object.
  Crucially this does not require a general scheme-valued object to lie in one member.
  The iff compares the original map with every restriction
  `(fullModuliInclusion A (U i).property).comp f`.
* `representable_lqf_fppf_target`: `V : AlgebraicSpace S` is the algebraic-space cover,
  `q : BasedFunctor (discreteModuli V.obj.obj) B` is its actual map, and `hq` is its
  representability. `hs : Function.Surjective (moduliPointMap q)` is surjectivity on
  field-valued point classes: by the field-object arrow equivalence and the CFG
  pullbacks it is precisely field-extension local lifting. `hflat : ModuliSpaceTest
  @Flat q` and `hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q` render flatness
  and local finite presentation on every scheme base change and étale source chart.
  The iff compares `f` with the actual projection `moduliTwoFiberFst q f` over `V`.
  No quasi-compactness or surjectivity of `f` is assumed. Using scheme tests on that
  projection is exactly the specified representable notion of local quasi-finiteness;
  its source is the actual 2-fibre product, not an arbitrary chosen space or map.
* `space_lqf_of_comp`: `A B C : AlgebraicSpace S`, `f : A → B`, and `g : B → C`
  render the final clause. `h : SpaceMapIsLocallyQuasiFinite (f ≫ g)` gives the
  composite property, and `SpaceMapIsLocallyQuasiFinite f` is the conclusion.
  There is no hypothesis on `g` and no hidden representability-by-schemes condition.

### Existing declarations and dependencies

All recorded dependency signatures and docstrings were read in the source. The item
adds only the two already-landed definition-owner nodes needed for the existing APIs:
`def-sfb-dm-stack-morphism-properties` and `def-sfb-open-moduli-substack`.

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `BasedCategory`, `IsFibredInGroupoids`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  with `AlgebraicSpace.IsEtale` for the existing chart tests.
* `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFiniteAtPoint` and `Scheme.Hom.IsLocallyQuasiFinite`.
* `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
* `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `CategoryTheory.ModuliSpaceTest`,
  `ModuliFieldObject`, `moduliPointMap`, and `SpaceMapIsLocallyQuasiFinite`.
  The generic source-local space test is used, not the intrinsic nonrepresentable
  DM local-quasi-finiteness predicate.
* `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `CategoryTheory.OpenModuliSubstack`
  and `fullModuliInclusion`.

Every proof dependency with a recorded module is imported without `public`, unless
already a statement import: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`,
`Sheaf.AlgebraicGeometry.AlgebraicSpace`,
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`,
`Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage`,
`Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource`,
`Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`,
`WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`.
Unstated proof prerequisites are referenced in the complete natural-language proof
in each theorem's docstring; none is needed to elaborate the statement.

### Edge cases and source checks

The empty source and empty open cover are retained: `hcover` can hold for an empty
family exactly when there are no field points, and the restrictions are universally
quantified over the empty index. Nonempty schemes spanning different open members
are retained by the field-point covering condition. Empty targets and identity
base changes are retained. Arbitrary characteristics and independent stack sizes are
retained. An infinite disjoint union of points is allowed, since no quasi-compactness
appears in the fppf cover or the locally-quasi-finite maps. The empty map to Spec(k)
is not assumed surjective. Cancellation allows an arbitrary second map, including a
map which itself is not locally quasi-finite.

Read Stacks `stacks-properties.tex`, lemma-check-property-covering (04XD),
`spaces-morphisms.tex`, lemma-composition-quasi-finite (03XK),
lemma-base-change-quasi-finite (03XL), lemma-permanence-quasi-finite (03XN), and
`descent.tex`, lemma-descending-property-quasi-finite (02VI). In 04XD the proof's
written covering T ×_Y V → T should read T ×_Y W → T; the accepted node's proof
already uses the correct cover, so there is no statement fault or correction here.
The sources support every clause, including the lack of quasi-compactness and the
unrestricted cancellation clause. No STATEMENT-DISPUTED finding.

### Searches

* `msearch.py leanfinder`, query “Representable morphisms of algebraic stacks locally
  quasi finite base change composition open source locality fppf target descent”:
  8 scheme-only hits, including Mathlib composition/base-change instances and
  `LocallyQuasiFinite.of_comp`. These neither cover stacks/spaces nor retain the
  project's finite-type condition by themselves.
* `msearch.py loogle`, query “AlgebraicGeometry.LocallyQuasiFinite,
  CategoryTheory.IsRepresentableByAlgebraicSpaces”: 0 hits, unknown project identifier.
* `msearch.py grep`, query “LocallyQuasiFinite|IsRepresentableByAlgebraicSpaces”,
  Mathlib subdirectory `AlgebraicGeometry`: 10 hits, all scheme material.
* `msearch.py grep`, query “representable_lqf|space_lqf_of_comp|ModuliSpaceTest|
  SpaceMapIsLocallyQuasiFinite”: 0 Mathlib hits.
* `rg` over `lean/WeilConjectures` for the item ID: no match. Concept/name searches
  over both `lean/WeilConjectures` and `lean/Sheaf` found the recorded scheme predicate,
  the generic `ModuliSpaceTest`, the existing chartwise algebraic-space predicate,
  and the open-substack construction. These are reused. The existing
  `StackProperLocallyQuasiFiniteComposition` concerns intrinsic DM properties plus
  properness; it neither gives representable algebraic-stack fppf descent nor this
  unrestricted algebraic-space cancellation theorem. None states this item's bundle.

### Validation

`scompile.py Q38 lem-sfb-representable-lqf-calculus-descent` compiled the delivery
module against the published live library, once under its sandbox name and once
under its actual module name. Both passed with no errors or unexpected warnings
(9.8 s and 4.3 s). The module sets `autoImplicit false`, has no local notations or
private definitions, and every theorem has a source and the complete reviewed
natural-language proof. Only theorem proofs use `sorry`.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
