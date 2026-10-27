# CoherentExactMorphism and the concrete descent interfaces

## Reason

Separate finite-stage coefficient-family construction and exchange compatibility
from common-stage descent. The new input modules need these existing definitions
without importing their consumer, PbcDescentFunctors. Relocating and publicly
re-exporting them removes the import cycle. No value or signature changes, and
no Challenge target changes meaning. No WeilConjectures file is edited.

## Old

In lean/Sheaf/Paper/PbcDescentFunctors.lean, in their existing namespaces:

```lean
/-- A family of exact finite-stage functors with scalar-extension comparisons.
The `base` field contains the stage functors `Φ_E`, comparisons `β_{F/E}`, and
their associator coherence.  The remaining fields record additivity,
compatibility with shifts of the stage functors and comparisons, and
preservation of distinguished triangles at every stage. On the normalized PBC
stage systems, the unit equation follows from associator coherence at repeated
stages: the resulting idempotent isomorphism component is the identity.
Source: blueprint main-20261015, order 1312
(blueprint: prop-weil-pbc-descent-functors). -/
structure CoherentExactMorphism {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    (S : StageSystem C) (S' : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (C i)] [∀ i, HasZeroObject (D i)]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (C i)] [∀ i, Pretriangulated (D i)]
    [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ (i j : I) (h : i ≤ j), (S'.T h).CommShift ℤ] where
  base : StageSystem.Morphism S S'
  additive : ∀ i, (base.Φ i).Additive
  [commShift : ∀ i, (base.Φ i).CommShift ℤ]
  betaCommShift : ∀ {i j : I} (h : i ≤ j),
    NatTrans.CommShift (base.β h).hom ℤ
  triangulated : ∀ i, (base.Φ i).IsTriangulated

namespace Morphism

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {S' : StageSystem D}
    [Preadditive S.PairCategory] [Preadditive S'.PairCategory]
    [HasZeroObject S.PairCategory] [HasZeroObject S'.PairCategory]
    [HasShift S.PairCategory ℤ] [HasShift S'.PairCategory ℤ]
    [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
    [∀ n : ℤ, (shiftFunctor S'.PairCategory n).Additive]
    [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]

/-- The rational finite-stage direct image is the restriction of the actual ringed
pro-etale derived direct image followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (h E) (pbcStageUniformizer.{u} l Ω E)

/-- The rational finite-stage pullback is the restriction of the actual completed
ringed pro-etale pullback followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (h E)
    (pbcStageUniformizer.{u} l Ω E)

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

section CanonicalBeta
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- Direct-image β is the localized canonical scalar mate, conjugated by the
integral/scalar comparisons, including equal coefficient stages. The right-hand
side is the unique comparison characterized by the localized ambient mate in
`pbcScalarDirectImage_rational`, at the canonical small coefficient fields.
The endpoint equalities are already concluded separately for every stage;
quantification over their proofs does not impose an additional assumption.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcDirectImageBetaSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Rf.Φ E = pbcDescentDirectImage l Ω f pres E)
    (eF : Rf.Φ F = pbcDescentDirectImage l Ω f pres F)
    (K : pbcIntegralStage l Ω X E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Rf.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).obj K) ≫
        β.hom.app (ScalarLocalization.mk K) ≫
        (pbcDescentDirectImage l Ω f pres F).map
          ((pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app K))
      (((pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) f
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))

/-- Pullback β inverse is the localized canonical completed scalar comparison,
conjugated by the integral/scalar comparisons, including equal stages. The
right-hand side is the unique comparison characterized by the localized
completed tensor comparison in `pbcScalarCompletedPull_rational`, at the small
coefficient fields. Its orientation is opposite to `Morphism.β`. Endpoint
identifications are concluded separately, so this predicate fixes every β.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcPullbackBetaSpec (g : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Lg.Φ E = pbcDescentPullback l Ω g pres E)
    (eF : Lg.Φ F = pbcDescentPullback l Ω g pres F)
    (K : pbcIntegralStage l Ω Y E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Lg.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcDescentPullback l Ω g pres F).map
          ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app K) ≫
        β.inv.app (ScalarLocalization.mk K) ≫
        (pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (pres E)).obj K))
      (((pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) g
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))
```

## New

The same five declaration blocks, verbatim, in lean/Sheaf/Paper/PbcDescentInterfaces.lean.
PbcDescentFunctors adds `public import Sheaf.Paper.PbcDescentInterfaces`.

```lean
/-- A family of exact finite-stage functors with scalar-extension comparisons.
The `base` field contains the stage functors `Φ_E`, comparisons `β_{F/E}`, and
their associator coherence.  The remaining fields record additivity,
compatibility with shifts of the stage functors and comparisons, and
preservation of distinguished triangles at every stage. On the normalized PBC
stage systems, the unit equation follows from associator coherence at repeated
stages: the resulting idempotent isomorphism component is the identity.
Source: blueprint main-20261015, order 1312
(blueprint: prop-weil-pbc-descent-functors). -/
structure CoherentExactMorphism {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    (S : StageSystem C) (S' : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (C i)] [∀ i, HasZeroObject (D i)]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (C i)] [∀ i, Pretriangulated (D i)]
    [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ (i j : I) (h : i ≤ j), (S'.T h).CommShift ℤ] where
  base : StageSystem.Morphism S S'
  additive : ∀ i, (base.Φ i).Additive
  [commShift : ∀ i, (base.Φ i).CommShift ℤ]
  betaCommShift : ∀ {i j : I} (h : i ≤ j),
    NatTrans.CommShift (base.β h).hom ℤ
  triangulated : ∀ i, (base.Φ i).IsTriangulated

namespace Morphism

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {S' : StageSystem D}
    [Preadditive S.PairCategory] [Preadditive S'.PairCategory]
    [HasZeroObject S.PairCategory] [HasZeroObject S'.PairCategory]
    [HasShift S.PairCategory ℤ] [HasShift S'.PairCategory ℤ]
    [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
    [∀ n : ℤ, (shiftFunctor S'.PairCategory n).Additive]
    [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]

/-- The rational finite-stage direct image is the restriction of the actual ringed
pro-etale derived direct image followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (h E) (pbcStageUniformizer.{u} l Ω E)

/-- The rational finite-stage pullback is the restriction of the actual completed
ringed pro-etale pullback followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (h E)
    (pbcStageUniformizer.{u} l Ω E)

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

section CanonicalBeta
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- Direct-image β is the localized canonical scalar mate, conjugated by the
integral/scalar comparisons, including equal coefficient stages. The right-hand
side is the unique comparison characterized by the localized ambient mate in
`pbcScalarDirectImage_rational`, at the canonical small coefficient fields.
The endpoint equalities are already concluded separately for every stage;
quantification over their proofs does not impose an additional assumption.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcDirectImageBetaSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Rf.Φ E = pbcDescentDirectImage l Ω f pres E)
    (eF : Rf.Φ F = pbcDescentDirectImage l Ω f pres F)
    (K : pbcIntegralStage l Ω X E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Rf.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).obj K) ≫
        β.hom.app (ScalarLocalization.mk K) ≫
        (pbcDescentDirectImage l Ω f pres F).map
          ((pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app K))
      (((pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) f
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))

/-- Pullback β inverse is the localized canonical completed scalar comparison,
conjugated by the integral/scalar comparisons, including equal stages. The
right-hand side is the unique comparison characterized by the localized
completed tensor comparison in `pbcScalarCompletedPull_rational`, at the small
coefficient fields. Its orientation is opposite to `Morphism.β`. Endpoint
identifications are concluded separately, so this predicate fixes every β.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcPullbackBetaSpec (g : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Lg.Φ E = pbcDescentPullback l Ω g pres E)
    (eF : Lg.Φ F = pbcDescentPullback l Ω g pres F)
    (K : pbcIntegralStage l Ω Y E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Lg.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcDescentPullback l Ω g pres F).map
          ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app K) ≫
        β.inv.app (ScalarLocalization.mk K) ≫
        (pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (pres E)).obj K))
      (((pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) g
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))
```

## Users

The table includes every transitive importer reported by downstream.py, the item,
and the new direct consumers. Textual uses are in NormalizedCoefficientFamilies,
A1QbarOpenClosedCohomology, PbcQbarCompletedPullback and AdicHeartPullbackFibres.
All retain the same names and definition bodies through public re-export.
No existing consumer needs an edit; there are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | unchanged via public re-export |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | unchanged via public re-export |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | unchanged via public re-export |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | unchanged via public re-export |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | unchanged via public re-export |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | unchanged via public re-export |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | unchanged via public re-export |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | unchanged via public re-export |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | unchanged via public re-export |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | unchanged via public re-export |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPurityObjects | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineLineInvariance | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | unchanged via public re-export |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ArithmeticRoots | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryQMaps | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BoundaryQTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CanonicalOpenRestrictionModel | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ChernFlagFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | B4 | unchanged via public re-export |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompactificationRefinementLocalizing | D4 | unchanged via public re-export |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CondensedERealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CondensedTateRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | unchanged via public re-export |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | unchanged via public re-export |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FdPullbackComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FlagLocalComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FourierTraceFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.HomFiniteProjective | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralCompletedTowerPullbackUniverses | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | unchanged via public re-export |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | unchanged via public re-export |
| Sheaf.Paper.InternalHomPullback | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | unchanged via public re-export |
| Sheaf.Paper.IteratedWeilMap | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LissePointNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseRationalRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalizedTopChern | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | unchanged via public re-export |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.MateOpenRestriction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | unchanged via public re-export |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OpenRestrictionCompleteness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | unchanged via public re-export |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PbcDescentFunctors | A4 | public re-export and assembly proof |
| Sheaf.Paper.PbcDescentInterfaces | A4 (new) | new interface or finite-stage input |
| Sheaf.Paper.PbcDirectImageCoherentFamily | A4 (new) | new interface or finite-stage input |
| Sheaf.Paper.PbcExchangeCompatibleFamily | A4 (new) | new interface or finite-stage input |
| Sheaf.Paper.PbcExchangeStageSquare | A4 (new) | new interface or finite-stage input |
| Sheaf.Paper.PbcPullbackCoherentFamily | A4 (new) | new interface or finite-stage input |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperHeartBound | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PulledReductionNormalizationComparison | E9 | unchanged via public re-export |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityChernClasses | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityCoprojection | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityGysinStructure | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PuritySourceTransports | unclaimed | unchanged via public re-export |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | unchanged via public re-export |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | unchanged via public re-export |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RationalStalkExact | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealWeights | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealizationAdjointComparisons | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealizationCompletedPullData | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealizationPullOrdinarySystem | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RealizationPullRationalDescent | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | unchanged via public re-export |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfExactPullbackCounitNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorDatum | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SmoothPurityMap | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | unchanged via public re-export |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SmoothTrace | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | unchanged via public re-export |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFixedScheme | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TwConventions | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | unchanged via public re-export |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | unchanged via public re-export |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundlePurity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundleThom | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.VerdierExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilGenericLissity | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WfTateTwist | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | unchanged via public re-export |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | unchanged via public re-export |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | unchanged via public re-export |
| Sheaf.Paper.ZlShriekComposition | unclaimed | unchanged via public re-export |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | unchanged via public re-export |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | unchanged via public re-export |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | unchanged via public re-export |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | unchanged via public re-export |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | unchanged via public re-export |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | unchanged via public re-export |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | unchanged via public re-export |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | unchanged via public re-export |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | unchanged via public re-export |
| WeilConjectures | unclaimed | unchanged via public re-export |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | unchanged via public re-export |

| Sheaf.Paper.PbcDirectImageFamilyExact | A4 (new) | new finite-stage exactness input |

| Sheaf.Paper.PbcDirectImageStageExact | A4 (new) | Uses the unchanged interfaces to construct uniquely normalized exact stage shifts. |
| Sheaf.Paper.PbcDirectImageFamilyShiftCompatible | A4 (new) | Uses the unchanged interfaces for the scalar-shift compatibility equation. |

## Status

landed 20261022T113810-L-253425 2026-10-22 (merge of deliver/A4/Sheaf.Paper.PbcDescentFunctors)
