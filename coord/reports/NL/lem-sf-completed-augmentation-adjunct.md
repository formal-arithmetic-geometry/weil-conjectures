## Worker report

`Sheaf.Paper.SfCompletedAugmentationAdjunct` states
`AlgebraicGeometry.Scheme.ExactPullbackNormalization.completed_augmentation_adjunct`.
Its sole postponed theorem has proof `sorry`; the five helper constructions have real data.
The item statement, its dependency lists, and its stage-1 proof are unchanged.

The previous worker's stated obstruction concerned a stage-1 re-split. This delivery is
stage 2 and only adds `lean` to the live reviewed split. No re-split is attempted.
There is no repair note for this item and no statement dispute was found.

Hypotheses and objects, matched to the node:

- `X Y : Scheme.{u}`, `g : Y ⟶ X` give the named schemes and morphism. All sheaves
  are on the actual `Scheme.ProEt` small sites. The sites retain object universe `u+1`
  and morphism universe `u`; no equality of these universes is imposed.
- `A : Type (u+1)`, `[CommRing A]`, `d : AdicCoefficientDatum A` supply the Noetherian
  adic datum, finite perfect quotients and torsion residue assumed by the recorded
  coefficient convention. `pbcAdicCompletion T d` is its actual inverse-limit ring.
  The published index `n : ℕ` denotes the positive exponent `n+1`.
- `[IsIso (completedCoefficientMap g d)]` is exactly invertibility of the map defined
  by inverse-image projections into the coefficient limit.
- The exact pullback interface is the dependency's `moduleFunctor d g`: inverse image
  with scalar action transported by the inverse coefficient map. Its tensor-generator
  isomorphism `m` in `ModuleComparisonSpec` sends `x tensor b` to `b x`. It identifies
  this functor with the node's tensor pullback, including the quotient maps. Thus the
  module isomorphism changes presentation only, not the coefficients or the functor.
  This is the same presentation used by the published parent mate-factorization.
- `[(moduleFunctor d g).Additive]`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`
  state the assumed additivity and exactness. The tower exactness instances are the
  dependency's instances, not new assumptions. `mapDerivedCategory` and `towerFunctor`
  are the termwise exact descents `H` and `H̃`. `counit_normalization` identifies them
  with the actual left-derived pullbacks by their original universal counits.
- `pbcModules`, `pbcTowers`, and `DerivedCategory` are the published module sheaves,
  actual strict functor-category towers, and unbounded derived categories. There are
  no boundedness, completeness, product-preservation, or K-injective-preservation binders.

Every conclusion clause:

- `completedReductionTowerUnit d X` is the specified strict quotient augmentation `i_K`.
  `constantIso.hom` is `j_K⁻¹`, with its ordinary constant-tower identity and exact
  localization comparisons. The helper `pulledAugmentation` is their composite, `a_K`.
- `exactAugmentation d g K` is the actual ambient comparison after the counit-normalized
  identifications, by `counit_normalization` and its explicit square with
  `completedPullbackComparison`. It is not a freely supplied comparison morphism.
- The first conjunct equates that actual morphism to the unit of
  `d.constantRlimAdjunction Y` followed by `(completedTowerRlim d Y).map a_K`.
  Lean composes left to right, so this is precisely `alpha = L_Y(a_K) v_{Y,HK}`.
  The two units are separately constructed: `exactAugmentation` uses the published
  projection-defined `completedConstantRlimUnit`; the right side uses the canonical
  derived-adjunction unit. This equality is not a reflexive restatement of a definition.
- The second conjunct quantifies over every derived `f : K ⟶ K'` and gives the full
  square using the derived quotient-tower functor's map and the target Rlim map.
- The third conjunct quantifies over every `CbcStrictKFlatRepresentative d X`, so its
  complex is K-flat with flat terms as required. `pulledReductionComplex` is exactly
  termwise F of the actual quotient complex. `J` is any target tower complex and
  `r` any quasi-isomorphism to it with `[J.IsKInjective]`.
- `pulledChainAugmentation` is obtained from the ordinary `compConstIso` and the actual
  quotient unit. `resolvedChainAugmentation` is its composite with `r`, transposed by
  the ordinary constant/limit adjunction on complexes. Its data use no existence choice.
  The per-degree/per-level formula says its projection is F of the quotient augmentation
  followed by `r_n`, exactly the node's `r_n F(P → P_n)`.
- `pulledResolutionComparison` uses the original reduction universal counit, the exact
  localization factorization, and `Q(r)`. Its invertibility is part of the theorem.
  The final equality identifies the actual augmentation, after this canonical target
  comparison, with `Q(resolvedChainAugmentation)` followed by the canonical Rlim
  comparison on J, after the canonical source localization isomorphism.
- Independence of representatives and resolutions is expressed by the universal
  quantification over P, J, r: each formula computes the same already fixed actual
  derived morphism after invertible canonical comparisons. Any isomorphism `Q(P) ≅ K`
  transports this formula to K; the second conjunct gives compatibility with every such
  derived isomorphism as well as arbitrary derived maps. No projection detection in a
  derived category is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and topology.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, its strict complex
  construction, its original `completedReductionTowerComplexCounit`, and datum fields.
- `Sheaf.Paper.PbcQbarCompletedPullback`: recorded dependency module; its public imports
  retain `CompletedTowerPullback` and the actual integral completed pullback. We use
  `completedCoefficientMap`, `completedReductionTowerUnit`, and the normalization
  dependency's `exactAugmentation` built from `completedPullbackComparison`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, a transparent abbreviation
  for Mathlib `SheafOfModules`; the coefficient categories here are the published
  `pbcModules` specialization of precisely that category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and `DerivedCategory.Q`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` supplies the recorded
  strict inverse systems; the existing coefficient towers use that construction.
- `Sheaf.Paper.SfExactPullbackCounitNormalization`: `moduleFunctor`, `towerFunctor`,
  `constantIso`, `exactAugmentation`, and `counit_normalization`; no duplicate of them.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, imported for the unbounded
  K-injective derived-limit proof step.
- `Sheaf.CategoryTheory.DerivedTowerCounitProjections`: `derived_tower_counit_projections`,
  imported for the canonical adjunction normalization.
- `Sheaf.CategoryTheory.ExactSquareDerivedCounit`: `exactSquare_derived_counit`, imported
  for the identity-square transpose formula in proof step 2.
- `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.constantRlimAdjunction`.
- `Sheaf.Paper.StrictQuotientPullbackComputation`: `CbcStrictKFlatRepresentative` and
  `cbcStrictAugmentation`, used without replacing the flatness or augmentation notion.
- `Sheaf.Paper.CompletedRlimFunctor`: `completedRlimUnit`, the same inverse-limit
  universal derived comparison; supplied by the normalization module's public imports.

Sources opened: the current blueprint's localization unit at its recorded source path;
`literature/stacks-project/derived.tex`, labels
`lemma-pre-derived-adjoint-functors-general` (0FND) and `lemma-derived-adjoint-functors`
(09T5), including their complete statements and proofs; and the full live stage-1 proof.
The module theorem docstring carries all four proof steps, with their DAG citations.

Edge cases checked before writing:

- K=0 and arbitrary unbounded shifts: the statement retains all unbounded derived objects.
- g=id: the ordinary constant-tower identity and quotient unit have the expected direction.
- Empty schemes and the zero coefficient ring: no nonemptiness, nonzero, or invertibility
  of a coefficient prime has been introduced.
- A noncomplete K (for example a coefficient-inverted object with vanishing quotient
  tower): no invertibility of a completion unit is required; the target and augmentation
  may vanish while the source does not.
- Arbitrary resolution r and P: F is not applied to J, and J need not be preserved
  K-injectively by F; no products pass through F.
- The component equation lives in the category of complexes before localization.

Searches (launcher msearch, group NL and this item):

- `leanfinder`, query “The specified completed augmentation from an exact pullback to the
  derived inverse limit equals the adjunction unit followed by the pulled quotient
  augmentation”: eight hits, including `SimplicialObject.cechNerveAdjunction`,
  `IsAdicComplete.StrictMono.of_lift`, `AdicCompletion.map_exact`, and condensed/Cech
  declarations. None states the actual completed sheaf augmentation equality.
- `loogle`, query `CategoryTheory.Adjunction.derived_unit, CategoryTheory.Limits.constLimAdj`:
  zero hits; separate query `CategoryTheory.Adjunction.derived_unit`: one hit, the general
  derived unit formula. It does not include the actual quotient augmentation or resolutions.
- `leansearch`, query “Derived constant tower inverse limit adjunction unit computes an
  augmented complex using any K injective tower resolution”: eight hits, including
  `Limits.constLimAdj`, `Adjunction.derivedη`, and limit-cone formulas. These provide
  general tools, not this statement with its canonical completed pullback.
- `grep`, query `completed.*[Aa]ugment|exactAugmentation|derived_unit`: zero Mathlib hits
  from the wrapper. Direct `rg` on both project trees for `exactAugmentation`,
  `completedAugmentationAdjunct`, and the item id found the normalization module and
  the parent mate-factorization module only. The latter states a different factorization
  and projection formulas and does not supply this node's resolved chain-map assertion.
  All new full declaration names were also checked in Mathlib and both project trees.

Validation: server single-file compilation by the prescribed `scompile.py`; the first
compile found that the quotient module tower's additivity must be installed explicitly
inside the chain-map definition. It now uses the existing
`completedReductionModuleTowerFunctor_additive`, just as `cbcStrictAugmentation` does.
No new instance or additional hypothesis was introduced. The final `scompile.py` run
compiled both sandbox and actual module cleanly (19.6 s and 22.3 s), with no warnings
or errors. Delivery preflight results are recorded below after they finish.

Delivery validation: `deliver2.py NL lem-sf-completed-augmentation-adjunct --no-push`
printed `OK (dry run)` for commit `52ec0772874`: maintainer preflight and server
per-file compilation passed. Exactly the report, this node's `lean` field, and its
single statement module form the packet.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
