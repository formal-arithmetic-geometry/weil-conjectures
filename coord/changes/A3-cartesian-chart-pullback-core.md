# cartesianChartClassPullback and cartesianChartCohomologyLift

## Reason

The stage-naturality proof exceeded the 60-second bound because equality transports expanded
its derived pullback expression. Introduce the real, irreducible four-factor construction
`cartesianChartClassPullbackCore`, and have the chart pullback precompose it with the existing
free-source comparison. The naturality proof keeps this head intact while transporting scheme-map
equalities, then unfolds it for the categorical calculation. Its proofs remain in the item module.
A proved zero-class API in the new CartesianChartClassPullbackZero module lets the vanishing
caller use the construction without expanding it. Its import in the caller is proof-only.
The stage lift uses the existing `rawRestrictedCohomologyClass`, exactly the uniquely determined
inverse evaluation class used before. No witness of arbitrary existence is selected.

All existing public declaration types and visibility are unchanged. The only public signature
text change is whitespace: three long coefficient-expression lines in chartExchange_finish are
wrapped to obey the delivery checker's 100-character limit. This formatting change is declared
here and in the report; no tokens or hypotheses change. The private chart_pull_comp_core and
chart_pull_comp helper statements abbreviate the same explicit composites using the new core. Unfolding the new core and
`rawRestrictedCohomologyClass.eq_def` gives the old construction (up to associativity and proof
irrelevance). No mathematical meaning or degree range changes; empty schemes and degree zero
use the same formulas. Target statement review is reopened for any target using these definitions;
the intended definitions and all target texts are unchanged.

## Old

```lean
/-- Pull back a chart class, with the free-sheaf source transported from a given
pullback test object. All factors are the specified composition, single-functor,
and shift comparisons of exact inverse image.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-class-pullback). -/
noncomputable def cartesianChartClassPullback {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (V : B.Etale) (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree T').obj U) ⟶
      ((D+((b)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} b a a' ha).hom.app
        ((abelianComparisonFree B).obj V)) ≫
    (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((b)^*[AddCommGrpCat.{u + 1}])).map z ≫
    (D+((b)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K

/-- The actual stage lift for the chart diagram; it uses the inverse of the
canonical raw cohomology comparison, the chart adjunction, and pullback of the
resulting derived class. No representative or lift is selected by choice.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-cartesian-chart-cohomology-lift). -/
noncomputable def cartesianChartCohomologyLift
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree c.pt.left).obj U) ⟶
      ((D+(((c.π.app j.left).left)^*[AddCommGrpCat.{u + 1}])).obj
        (cartesianDerivedImage f (D.obj j.left).hom
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧ := by
  let h := pullback.snd ((D.map j.hom).left) (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let G := (((pullback.snd ((D.map j.hom).left)
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
  letI := isIso_rawRestrictedCohomologyComparison h q G V
  let z := (asIso (rawRestrictedCohomologyComparison h q G V)).inv x
  exact cartesianChartClassPullback (D.map j.hom).left (c.π.app j.left).left
    (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm V U r hr _ (q : ℤ)
    ((cartesianChartRawAdjunctionIso f (D.obj i).hom (D.map j.hom).left
      (D.obj j.left).hom (Over.w (D.map j.hom)).symm F q V).hom z)

```

## New

```lean
/-- The derived inverse-image action on a class with a pulled-back source.
All factors are the canonical composition, single and shift comparisons.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-class-pullback-core). -/
@[irreducible]
noncomputable def cartesianChartClassPullbackCore {B T T' : Scheme.{u}}
    (h : T ⟶ B) (a : T' ⟶ T) (s : T' ⟶ B) (hs : s = a ≫ h)
    (M : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj M) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[AddCommGrpCat.{u + 1}]).obj M) ⟶
        ((D+((a)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h s hs).hom.app M) ≫
    (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K

/-- Pull back a chart class, with the free-sheaf source transported from a given
pullback test object. All factors are the specified composition, single-functor,
and shift comparisons of exact inverse image.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-class-pullback). -/
noncomputable def cartesianChartClassPullback {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (V : B.Etale) (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree T').obj U) ⟶
      ((D+((b)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫
    cartesianChartClassPullbackCore a b a' ha ((abelianComparisonFree B).obj V) K q z

/-- The actual stage lift for the chart diagram; it uses the inverse of the
canonical raw cohomology comparison, the chart adjunction, and pullback of the
resulting derived class. No representative or lift is selected by choice.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-cartesian-chart-cohomology-lift). -/
noncomputable def cartesianChartCohomologyLift
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree c.pt.left).obj U) ⟶
      ((D+(((c.π.app j.left).left)^*[AddCommGrpCat.{u + 1}])).obj
        (cartesianDerivedImage f (D.obj j.left).hom
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧ := by
  let h := pullback.snd ((D.map j.hom).left) (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let G := (((pullback.snd ((D.map j.hom).left)
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
  let z := rawRestrictedCohomologyClass h q G V x
  exact cartesianChartClassPullback (D.map j.hom).left (c.π.app j.left).left
    (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm V U r hr _ (q : ℤ)
    ((cartesianChartRawAdjunctionIso f (D.obj i).hom (D.map j.hom).left
      (D.obj j.left).hom (Over.w (D.map j.hom)).symm F q V).hom z)

```

The separately proved zero API is in
`lean/Sheaf/AlgebraicGeometry/CartesianChartClassPullbackZero.lean`; it has no existing
signature to alter, and is imported only by the vanishing caller's proof.

## Users

This is the complete transitive downstream list from `tools/downstream.py`, together with the
changed definition module. Every user's signature and mathematical statement is preserved.
The five source adaptations below are in unclaimed modules and change only proofs (plus line
wrapping). Their original failures and necessary edits are recorded in the report.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartClassPullback | unclaimed | constructive factorization; cached inverse evaluation class |
| Sheaf.AlgebraicGeometry.CartesianChartClassPullbackZero | new | proved zero API in its own module |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeConclusion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCore | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeFinal | unclaimed | unfold the new core in the existing postcomposition calculation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeFinish | unclaimed | identify the canonical raw class by evaluation injectivity |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality | unclaimed | use the cached raw class directly; remove the inverse conversion |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeSource | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | A3 | naturalty proof completed using the named core; existing signature unchanged |
| Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineComplexPresentation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageChartComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageGermDescent | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageGermVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageRawAffineDescent | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing | unclaimed | use the zero-class API of the cached construction |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartData | unclaimed | unfold the core in postcomposition and the raw class in lift evaluation |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartNaturality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartRepresentative | R2 | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.LimitDerivedDirectImageExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.LimitHigherDirectImageExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.RawDerivedClassAffineDescent | A2 | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| TargetsCheck | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Composition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.WeilSheaf.Localization | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | unchanged signatures and mathematical meanings; no source adaptation |

## Status

landed 20261015T161927-L-300524 2026-10-15 (merge of deliver/A3/Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality)
