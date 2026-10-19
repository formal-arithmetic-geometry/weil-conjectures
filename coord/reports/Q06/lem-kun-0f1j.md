## Worker report

The module `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` defines
`AlgebraicGeometry.Etale.punctualTensorBaseChangeMap` and states
`AlgebraicGeometry.Etale.isIso_punctualTensorBaseChangeMap` with proof `sorry`.
The map is the derived mate for the right-hand cartesian square: its source is
`Lp^*E ⊗ᴸ Lf'^*Rg_*F`, its target is `Rh_*(Lh^*Lp^*E ⊗ᴸ Le^*F)`, and its transpose is the
pullback tensor comparison, followed by the square comparison
`Lf'^*Lh^* ≅ Lg^*Le^*`, followed by the derived counit of `g`. The theorem quantifies a
field `K`, a natural number `n` with `1 ≤ n` and `(n : K)` a unit, structure maps of the
six schemes to `Spec K`, pullback squares for `X'` and `Y`, and `[QuasiCompact g]`
`[QuasiSeparated g]`; it assumes `E,F` are bounded-below derived objects over
`ULift (ZMod n)`, an integer `a`, and lower Tor amplitude of `E`, and concludes that the
canonical map is an isomorphism.

The first map signature renders the tensor comparison clause by
`leftDerivedUpperStarTensorComparison`, the right-square clause by
`derivedSquareUpperStarIso ... sq`, and the counit clause by
`derivedUpperStarLowerStarAdjunction ... g).counit`. The theorem signature renders
`K`, `[Field K]`, `n`, `hn : 1 ≤ n`, `hnK : IsUnit (n : K)`, the maps and the two
`IsPullback` hypotheses, the qcqs typeclass hypotheses, `E` and `F` in
`DerivedCategory.Plus`, the integer `a`, and
`DerivedCategory.hasTorAmplitudeGE ... (_root_.DerivedCategory.Plus.ι.obj E)`.
`ULift (ZMod n)` is the universe-lifted form of the coefficient ring required by the
project's `ModuleCat.{u+1}` convention and is definitionally the coefficient ring
`ZMod n` in the node's `ZMod` notation.

Statement dependencies used directly are: `Mathlib.AlgebraicGeometry.Scheme`
(`AlgebraicGeometry.Scheme`), `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
(`CategoryTheory.Limits.pullback`), `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`),
`WeilConjectures.AlgebraicGeometry.DerivedCategories`
(`AlgebraicGeometry.Etale.DerivedCategoryModule`), `Mathlib.AlgebraicGeometry.Sites.Etale`
(`AlgebraicGeometry.Scheme.smallEtaleTopology`),
`WeilConjectures.SixFunctors.Etale.Derived.Tensor`
(`AlgebraicGeometry.Etale.derivedTensor`),
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
(`AlgebraicGeometry.Etale.upperStar`, `lowerStar`, and their adjunction),
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
(`AlgebraicGeometry.etaleInverseImageModulesExact`),
`Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
(`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`). The derived square and
its mate are imported from `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded` and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.

The edge cases checked were `n = 1` (the zero `ZMod 1` coefficient category), the excluded
case `n = 0` via `1 ≤ n`, arbitrary `a` (including negative bounds), and the absence of
any finite-type, proper, or separated hypothesis on `g`; only qcqs is assumed as in Tag
0F1J. The pullback hypotheses are retained separately, so no identity or degenerate
square is silently excluded.

Searches for an existing declaration were: LeanFinder query “Etale base change tensor
bounded below tor amplitude field” (top hits were unrelated Kähler/tensor base-change
results); Loogle query `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`
(no hits in the search service); grep in `AlgebraicGeometry` for
`punctual|ProjectionMap|projection.*base.*change` (no matching declaration). Repository
searches for `lem-kun-0f1j` and `punctualTensorBaseChangeMap` found no existing project
module. The exact existing generic ingredients were read in their source modules before
writing this statement.

## Earlier second reading (a previous round; superseded)

I independently compared the node and file. The field, integer invertibility, two
cartesian squares, qcqs hypothesis, bounded-below objects, lower Tor-amplitude bound,
and isomorphism conclusion all appear in the theorem signature. The map's source and
target render the node's `p⁻¹E`, `(f')⁻¹Rg_*F`, `h⁻¹p⁻¹E`, and `e⁻¹F` using the recorded
derived tensor, inverse-image, and direct-image declarations. The right-square
`CommSq e h g f'` has equation `e ≫ g = h ≫ f'`, exactly the diagram's commutativity;
`derivedSquareUpperStarIso` then has the required direction. No hypothesis was added to
or removed from the node, and the left pullback square is retained as an explicit
`IsPullback` hypothesis.

## Second reading by Q06

I reread the unit statement in `dag/nodes/sec-smooth-purity/lem-kun-0f1j.json`, the
worker module, and Stacks Project Tag 0F1J (the `lemma-punctual-base-change-upgrade`
lemma at `literature/stacks-project/etale-cohomology.tex`). The item-by-item match is:

* The field `K` and the hypotheses `[Field K]`, `n : ℕ`, `hn : 1 ≤ n`, and
  `hnK : IsUnit (n : K)` are rendered by the first four binders of
  `isIso_punctualTensorBaseChangeMap`. Thus `n = 1` is included and `n = 0` is excluded,
  exactly as in the node.
* The five schemes `X`, `X'`, `Y`, `S'`, `T`, their structure maps `aX` and `aS` to
  `Spec (CommRingCat.of K)`, and the maps `p`, `h`, `e`, `f'`, and `g` are the scheme
  and morphism binders in the same order as the diagram. The hypothesis
  `left : IsPullback p f' aX aS` renders `X' = X ×_{Spec K} S'`; the hypothesis
  `right : IsPullback e h g f'` renders `Y = X' ×_{S'} T`. No finite-type, proper, or
  separated condition is introduced. `[QuasiCompact g] [QuasiSeparated g]` is exactly
  the source's qcqs assumption.
* `E` and `F` are objects of `DerivedCategory.Plus` on the small étale sites of `X`
  and `T`, with coefficients `ModuleCat (ULift (ZMod n))`. This is the recorded
  `D⁺(X_et, Z/n)` and `D⁺(T_et, Z/n)` encoding; `ULift` only supplies the prescribed
  coefficient universe.
* The integer `a` and
  `hE : DerivedCategory.hasTorAmplitudeGE ... a (Plus.ι.obj E)` render the condition
  that `E` has tor amplitude in `[a, ∞)`. There is no lower-bound hypothesis on `F`.
* `punctualTensorBaseChangeMap ... right.toCommSq ...` has source
  `Lp^*E ⊗ᴸ Lf'^*Rg_*F` and target
  `Rh_*(Lh^*Lp^*E ⊗ᴸ Le^*F)`. Its definition is the mate of the pullback tensor
  comparison, the derived square isomorphism, and the counit of `g`, which is the
  canonical map specified by the node. The theorem concludes `IsIso` of exactly this
  map, with no additional clause or weakened conclusion.

The empty schemes and zero coefficient objects are admitted by the scheme and sheaf
binders; the zero object cases are therefore covered. Arbitrary integer `a`, including
negative values, is admitted. The pullback hypotheses are explicit and do not exclude
identity or degenerate squares. The source imposes no characteristic restriction beyond
invertibility of `n`, which is exactly `hnK`.

I searched for duplicate notions using LeanFinder, Loogle, and repository/Mathlib grep.
LeanFinder returned only unrelated étale algebra and Kähler base-change declarations;
Loogle found no `punctualTensorBaseChangeMap` or matching projection map; grep found no
existing `punctualTensorBaseChange` declaration in `WeilConjectures` or `Sheaf`.
The dependency declarations were opened: `pullback` supplies the fibre-product object,
`DerivedCategoryModule` and `Plus` supply the stated étale derived categories,
`derivedTensor` is the unbounded K-flat derived tensor, and `hasTorAmplitudeGE` tests
all degree-zero module sheaves as required by the node's tor-amplitude definition.

No mismatch was found, so no source or node change was made. The module compiles cleanly
with `scompile.py`; its only postponed proof is the required theorem `sorry`.
