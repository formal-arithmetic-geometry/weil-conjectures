/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralPullbackShiftCoordinates
public import Sheaf.Paper.CompletedScalarShiftCoordinates

import Sheaf.Paper.IntegralComparisonPullbackRealizationShifts
import Sheaf.Paper.IntegralComparisonScalarRealizationShifts
import Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts

/-!
# The normalized completed pullback scalar comparison commutes with shifts

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures and rational-stage
paragraphs; Stacks Tags 011G, 014E, 0941 and 099N(5)
(blueprint: lem-sf-framework-theta-shift-compatibility).

The shift data below are fixed by the existing signed cochain coordinate and
representative-descent predicates. Theta is lambda followed by mu inverse for
the whole-system counit realization, rather than an arbitrary isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe d u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The stipulated canonical shifts, with their signed whole-tower normalization.
These fields retain actual cochain shifts and their descent through the defining
K-flat comparison; none is an arbitrary choice of shift on a derived functor.
Source: Stacks 011G, 014E, 0941; blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
structure SfFrameworkThetaShifts where
  /-- The cochain shift on the E-pullback Roos construction. -/
  pullChainE : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ
  /-- Its unsigned/signed mapping-cocone coordinates. -/
  pullCoordinatesE : IntegralCompletedComparison.ShiftCoordinates l E f pullChainE
  /-- Its descent to completed E-pullback. -/
  pullE : (integralDerivedPullback l E f).CommShift ℤ
  /-- The retained comparison on every good representative fixes that descent. -/
  pullDescentE : IntegralCompletedComparison.ShiftDescent l E f pullChainE pullE
  /-- The cochain shift on the L-pullback Roos construction. -/
  pullChainL : (integralOperationsPullbackComplexFunctor l L f).CommShift ℤ
  /-- Its unsigned/signed mapping-cocone coordinates. -/
  pullCoordinatesL : IntegralCompletedComparison.ShiftCoordinates l L f pullChainL
  /-- Its descent to completed L-pullback. -/
  pullL : (integralDerivedPullback l L f).CommShift ℤ
  /-- The retained comparison on every good representative fixes that descent. -/
  pullDescentL : IntegralCompletedComparison.ShiftDescent l L f pullChainL pullL
  /-- Cochain scalar shift on the source scheme. -/
  scalarChainX : (integralScalarComplexFunctor l E L ι X).CommShift ℤ
  /-- Its signed coordinates with actual quotient transitions. -/
  scalarCoordinatesX : ∀ (P : CochainComplex (integralTowerModules l E X) ℤ) (m : ℤ),
    completedScalarShiftConeFormula ι X scalarChainX P m
  /-- Its derived descent on the source scheme. -/
  scalarX : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ
  /-- The retained K-flat comparison fixes this descent. -/
  scalarDescentX : completedScalarShiftIntegralNormalization ι X scalarChainX scalarX
  /-- Cochain scalar shift on the target scheme. -/
  scalarChainY : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ
  /-- Its signed coordinates with actual quotient transitions. -/
  scalarCoordinatesY : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ),
    completedScalarShiftConeFormula ι Y scalarChainY P m
  /-- Its derived descent on the target scheme. -/
  scalarY : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ
  /-- The retained K-flat comparison fixes this descent. -/
  scalarDescentY : completedScalarShiftIntegralNormalization ι Y scalarChainY scalarY

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The source composite T_X F_{f,E}, using the recorded constructible restrictions.
Source: blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
abbrev sfFrameworkThetaSource :=
  constructibleIntegralPullback l E f ⋙ integralComparisonConstructibleScalar l E L ι X

/-- The target composite F_{f,L} T_Y with the same integral scalar functor.
Source: blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
abbrev sfFrameworkThetaTarget :=
  integralComparisonConstructibleScalar l E L ι Y ⋙ constructibleIntegralPullback l L f

/-- The comparison prescribed by the normalized whole-system counit realization.
Source: Stacks 099N(5), 0941; blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
def sfFrameworkTheta (D : IntegralComparisonSystem.{u} l)
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfFrameworkThetaSource l E L ι f).obj K ≅
      (sfFrameworkThetaTarget l E L ι f).obj K :=
  ObjectProperty.isoMk _ (integralComparisonScalar l E L ι D f K)

/-- Composite shift: apply T_X to the E-pullback shift, then the T_X shift.
Source: Stacks 011G, 014E; blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
def sfFrameworkThetaSourceShift (S : SfFrameworkThetaShifts l E L ι f)
    (K : sfIntegralConstructibleCategory l E Y) (m : ℤ) :
    (sfFrameworkThetaSource l E L ι f).obj (K⟦m⟧) ≅
      ((sfFrameworkThetaSource l E L ι f).obj K)⟦m⟧ :=
  ObjectProperty.isoMk _
    ((integralScalarExtension l E L ι X).mapIso
        ((integralDerivedPullback l E f).mapIso
          (((sfIntegralConstructible l E Y).ι.commShiftIso m).app K) ≪≫
        (Functor.commShiftIso (integralDerivedPullback l E f)
          (self := S.pullE) m).app K.obj) ≪≫
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι X)
        (self := S.scalarX) m).app ((integralDerivedPullback l E f).obj K.obj) ≪≫
      (((sfIntegralConstructible l L X).ι.commShiftIso m).app
        ((sfFrameworkThetaSource l E L ι f).obj K)).symm)

/-- Composite shift: apply F_{f,L} to the T_Y shift, then the L-pullback shift.
Source: Stacks 011G, 014E; blueprint Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
def sfFrameworkThetaTargetShift (S : SfFrameworkThetaShifts l E L ι f)
    (K : sfIntegralConstructibleCategory l E Y) (m : ℤ) :
    (sfFrameworkThetaTarget l E L ι f).obj (K⟦m⟧) ≅
      ((sfFrameworkThetaTarget l E L ι f).obj K)⟦m⟧ :=
  ObjectProperty.isoMk _
    ((integralDerivedPullback l L f).mapIso
        ((integralScalarExtension l E L ι Y).mapIso
          (((sfIntegralConstructible l E Y).ι.commShiftIso m).app K) ≪≫
        (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y)
          (self := S.scalarY) m).app K.obj) ≪≫
      (Functor.commShiftIso (integralDerivedPullback l L f)
        (self := S.pullL) m).app ((integralScalarExtension l E L ι Y).obj K.obj) ≪≫
      (((sfIntegralConstructible l L X).ι.commShiftIso m).app
        ((sfFrameworkThetaTarget l E L ι f).obj K)).symm)

attribute [local irreducible] integralComparisonSequenceScalarModel
  integralComparisonPullbackCounit integralComparisonScalarCounit
  integralDerivedPullback integralComparisonDerivedSequencePullback
  integralComparisonDerivedSequenceScalar coefficientSequenceLimit

private theorem reduced_realization_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (H : A ⥤ C) (T : C ⥤ D) (L : D ⥤ B) (R : B ⥤ D)
    [F.CommShift ℤ] [H.CommShift ℤ] [T.CommShift ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ]
    (e : F ⟶ H ⋙ T ⋙ L) (c : L ⋙ R ⟶ 𝟭 D)
    [NatTrans.CommShift e ℤ] [NatTrans.CommShift c ℤ] :
    NatTrans.CommShift (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) ℤ := by
  let t := Functor.whiskerRight e R ≫ (Functor.associator H (T ⋙ L) R).hom ≫
    Functor.whiskerLeft H ((Functor.associator T L R).hom ≫
      Functor.whiskerLeft T c ≫ T.rightUnitor.hom)
  have ht : NatTrans.CommShift t ℤ := by dsimp [t]; infer_instance
  have he : t = (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) := by
    ext X
    simp [t]
  exact he ▸ ht

private theorem comparison_shift_of_realizations
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F G R : A ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ] [R.CommShift ℤ]
    (α : F ⟶ R) (β : G ⟶ R) [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ]
    (K K' : A) (m : ℤ) (e : K' ≅ K⟦m⟧)
    (a : F.obj K ≅ G.obj K) (a' : F.obj K' ≅ G.obj K')
    (ha : a.hom ≫ β.app K = α.app K)
    (ha' : a'.hom ≫ β.app K' = α.app K') [IsIso (β.app K)] :
    a'.hom ≫ G.map e.hom ≫ (G.commShiftIso m).hom.app K =
      F.map e.hom ≫ (F.commShiftIso m).hom.app K ≫ a.hom⟦m⟧' := by
  have square (H : A ⥤ B) [H.CommShift ℤ] (t : H ⟶ R)
      [NatTrans.CommShift t ℤ] :
      H.map e.hom ≫ (H.commShiftIso m).hom.app K ≫ (t.app K)⟦m⟧' =
        t.app K' ≫ R.map e.hom ≫ (R.commShiftIso m).hom.app K := by
    rw [NatTrans.shift_app_comm, ← t.naturality_assoc]
  apply (cancel_mono ((shiftFunctor B m).mapIso (asIso (β.app K))).hom).1
  change (a'.hom ≫ G.map e.hom ≫ (G.commShiftIso m).hom.app K) ≫
      (β.app K)⟦m⟧' =
    (F.map e.hom ≫ (F.commShiftIso m).hom.app K ≫ a.hom⟦m⟧') ≫
      (β.app K)⟦m⟧'
  simp only [Category.assoc]
  rw [square G β, ← Category.assoc a'.hom, ha']
  rw [← square F α, ← ha, Functor.map_comp]

private def thetaLambda
    (D : IntegralComparisonSystem.{u} l) :
    integralDerivedPullback l E f ⋙ integralScalarExtension l E L ι X ⟶
      ((D.coefficient E).system Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E L ι X ⋙
        coefficientSequenceLimit l L X :=
  Functor.whiskerLeft (integralDerivedPullback l E f)
      ((D.scalar E L ι).model X).realization.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (integralComparisonPullbackCounit l E f
        ((D.coefficient E).system Y) ((D.coefficient E).system X)
        ((D.coefficient E).roos X) ((D.coefficient E).pullback f)) _ ≫
    (Functor.associator _ _ _).hom

private def thetaMu
    (D : IntegralComparisonSystem.{u} l) :
    integralScalarExtension l E L ι Y ⋙ integralDerivedPullback l L f ⟶
      ((D.coefficient E).system Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E L ι X ⋙
        coefficientSequenceLimit l L X :=
  Functor.whiskerLeft (integralScalarExtension l E L ι Y)
      ((D.coefficient L).pullback f).realization.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (integralComparisonScalarCounit l E L ι Y
        ((D.coefficient E).system Y) ((D.coefficient L).system Y)
        ((D.coefficient L).roos Y) ((D.scalar E L ι).model Y)) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((D.coefficient E).system Y).reduction
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι f).inv _ ≫
        (Functor.associator _ _ _).hom)

private theorem thetaLambda_app
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (thetaLambda l E L ι f D).app K.obj = (integralComparisonLambda l E L ι D f K).hom := by
  simp only [thetaLambda, integralComparisonLambda, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem thetaMu_app
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (thetaMu l E L ι f D).app K.obj = (integralComparisonMu l E L ι D f K).hom := by
  simp only [thetaMu, integralComparisonMu, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, asIso_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem theta_comp_mu
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E L ι D f K).hom ≫ (thetaMu l E L ι f D).app K.obj =
      (thetaLambda l E L ι f D).app K.obj := by
  rw [thetaMu_app, thetaLambda_app]
  simp only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The prescribed comparison, its inverse, and both raw rationalizations commute
with every integer shift for the stipulated representative-normalized comparisons.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures and rational-stage
paragraphs; Stacks Tags 011G, 014E, 0941 and 099N(5)
(blueprint: lem-sf-framework-theta-shift-compatibility).

Proof:
1. Use the whole-tower normalization of lem-trf-integral-pullback-comparison-realization:
   theta_K = lambda_K followed by mu_K inverse, both landing in Rlim Q(P).
2. Take a flat-term K-flat representative P of K by lem-pc-kflat-resolution. Its integer
   shift is good by lem-weil-completed-scalar-shift-descent. All finite quotient complexes
   and their pullbacks shift degreewise; their differentials acquire the same (-1)^m.
3. The balanced maps (x tensor a) tensor b to x tensor i(a)b and
   b tensor (x tensor a) to (1 tensor x) tensor b phi(a), the action x tensor a to ax,
   and the augmentation x to x tensor 1 are unchanged by that reindexing. They commute
   with actual quotient transitions, by lem-pur-cochain-pullback-tensor-coherence.
4. By lem-weil-roos-comm-shift the whole-tower Roos shift is (y,x) to ((-1)^m y,x).
   The normalized K-injective bridge z to (0,z) commutes with this shift, by
   lem-pur-injective-tower-roos-shifts. The completion augmentation has zero signed
   coordinate, so it commutes too.
5. Compute the entire-tower counit on a K-injective tower resolution. Shifting the
   resolution shifts its strict limit cone and leaves it a K-injective resolution.
   Therefore epsilon on the shifted tower is shifted epsilon after the limit shift.
6. Apply the normalized derived coefficient changes and their action counits. Their
   shift squares are lem-pur-coefficient-scalar-shifts, lem-pur-coefficient-associator-shifts
   and lem-pur-coefficient-pullback-shifts; lem-pur-derived-change-of-rings identifies
   these with the balanced representative maps, without any coefficient-flatness bound.
7. Paste these whole-diagram squares in lambda and mu. Realizing gives
   sigma lambda_shift = shifted_lambda chi_source and
   sigma mu_shift = shifted_mu chi_target. Independence of representatives transports
   both equations to every constructible K.
8. Substitute theta = lambda followed by mu inverse and cancel mu and sigma to obtain
   the forward equation below. Multiplying by theta inverses gives the inverse equation.
   The full-subcategory inclusion comparisons inserted in the definitions transport
   exactly these ambient equations and preserve their order.
9. Raw rationalization sends an integral arrow to its tensor with one and preserves
   composition and inverses. Apply it to the two equations. Its objects are precisely
   the integral objects, so these two localized equations cover every rational input;
   they are the comparisons prescribed by def-weil-derived-pullback-tensor-hom. -/
theorem sfFrameworkThetaShiftCompatibility
    (_D₀ : FiniteFieldDatum.{d}) (_hl : l ≠ _D₀.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (eE : E →ₐ[ℚ_[l]] Ω) (eL : L →ₐ[ℚ_[l]] Ω) (_hι : eL.comp ι = eE)
    (D : IntegralComparisonSystem.{u} l) (S : SfFrameworkThetaShifts l E L ι f)
    (K : sfIntegralConstructibleCategory l E Y) (m : ℤ) :
    ((sfFrameworkTheta l E L ι f D (K⟦m⟧)).hom ≫
        (sfFrameworkThetaTargetShift l E L ι f S K m).hom =
      (sfFrameworkThetaSourceShift l E L ι f S K m).hom ≫
        (sfFrameworkTheta l E L ι f D K).hom⟦m⟧') ∧
    ((sfFrameworkTheta l E L ι f D (K⟦m⟧)).inv ≫
        (sfFrameworkThetaSourceShift l E L ι f S K m).hom =
      (sfFrameworkThetaTargetShift l E L ι f S K m).hom ≫
        (sfFrameworkTheta l E L ι f D K).inv⟦m⟧') ∧
    ((sfRationalConstructibleLocalization l L X).map
          (sfFrameworkTheta l E L ι f D (K⟦m⟧)).hom ≫
        (sfRationalConstructibleLocalization l L X).map
          (sfFrameworkThetaTargetShift l E L ι f S K m).hom =
      (sfRationalConstructibleLocalization l L X).map
          (sfFrameworkThetaSourceShift l E L ι f S K m).hom ≫
        (sfRationalConstructibleLocalization l L X).map
          ((sfFrameworkTheta l E L ι f D K).hom⟦m⟧')) ∧
    ((sfRationalConstructibleLocalization l L X).map
          (sfFrameworkTheta l E L ι f D (K⟦m⟧)).inv ≫
        (sfRationalConstructibleLocalization l L X).map
          (sfFrameworkThetaSourceShift l E L ι f S K m).hom =
      (sfRationalConstructibleLocalization l L X).map
          (sfFrameworkThetaTargetShift l E L ι f S K m).hom ≫
        (sfRationalConstructibleLocalization l L X).map
          ((sfFrameworkTheta l E L ι f D K).inv⟦m⟧')) := by
  let := S.pullE
  let := S.pullL
  let := S.scalarX
  let := S.scalarY
  let : (integralScalarExtension l E L ι X).CommShift ℤ := S.scalarX
  let : (integralScalarExtension l E L ι Y).CommShift ℤ := S.scalarY
  let := integralComparisonLimitShift l E X
  let := integralComparisonLimitShift l L X
  let := integralComparisonLimitShift l L Y
  let := integralComparisonReductionShift l E X ((D.coefficient E).system X)
  let := integralComparisonReductionShift l E Y ((D.coefficient E).system Y)
  let := integralComparisonReductionShift l L X ((D.coefficient L).system X)
  let := integralComparisonReductionShift l L Y ((D.coefficient L).system Y)
  let := integralComparisonSequencePullbackShift l E f
  let := integralComparisonSequencePullbackShift l L f
  let := integralComparisonSequenceScalarShift l E L ι X
  let := integralComparisonSequenceScalarShift l E L ι Y
  have : NatTrans.CommShift ((D.coefficient E).pullback f).realization.hom ℤ :=
    integralComparisonPullbackRealization_commShift l E f
    ((D.coefficient E).system Y) ((D.coefficient E).roos X)
    ((D.coefficient E).pullback f) S.pullChainE S.pullCoordinatesE S.pullE S.pullDescentE
  have : NatTrans.CommShift ((D.coefficient L).pullback f).realization.hom ℤ :=
    integralComparisonPullbackRealization_commShift l L f
    ((D.coefficient L).system Y) ((D.coefficient L).roos X)
    ((D.coefficient L).pullback f) S.pullChainL S.pullCoordinatesL S.pullL S.pullDescentL
  have : NatTrans.CommShift ((D.scalar E L ι).model X).realization.hom ℤ :=
    integralComparisonScalarRealization_commShift l E L ι X
    ((D.coefficient E).system X) ((D.coefficient L).roos X)
    ((D.scalar E L ι).model X) S.scalarChainX S.scalarCoordinatesX
    S.scalarX S.scalarDescentX
  have : NatTrans.CommShift ((D.scalar E L ι).model Y).realization.hom ℤ :=
    integralComparisonScalarRealization_commShift l E L ι Y
    ((D.coefficient E).system Y) ((D.coefficient L).roos Y)
    ((D.scalar E L ι).model Y) S.scalarChainY S.scalarCoordinatesY
    S.scalarY S.scalarDescentY
  have hAdjEX : ((D.coefficient E).system X).adjunction.CommShift ℤ :=
    ((D.coefficient E).system X).adjunction.commShift_of_rightAdjoint ℤ
  have : ((D.coefficient L).system X).adjunction.CommShift ℤ :=
    ((D.coefficient L).system X).adjunction.commShift_of_rightAdjoint ℤ
  have hAdjLY : ((D.coefficient L).system Y).adjunction.CommShift ℤ :=
    ((D.coefficient L).system Y).adjunction.commShift_of_rightAdjoint ℤ
  have : NatTrans.CommShift ((D.coefficient E).system X).adjunction.counit ℤ :=
    hAdjEX.commShift_counit
  have : NatTrans.CommShift ((D.coefficient L).system Y).adjunction.counit ℤ :=
    hAdjLY.commShift_counit
  have : NatTrans.CommShift
      (integralComparisonPullbackCounit l E f
        ((D.coefficient E).system Y) ((D.coefficient E).system X)
        ((D.coefficient E).roos X) ((D.coefficient E).pullback f)) ℤ := by
    unfold integralComparisonPullbackCounit
    exact reduced_realization_commShift (integralDerivedPullback l E f)
      ((D.coefficient E).system Y).reduction
      (integralComparisonDerivedSequencePullback l E f) (coefficientSequenceLimit l E X)
      ((D.coefficient E).system X).reduction ((D.coefficient E).pullback f).realization.hom
      ((D.coefficient E).system X).adjunction.counit
  have : NatTrans.CommShift
      (integralComparisonScalarCounit l E L ι Y
        ((D.coefficient E).system Y) ((D.coefficient L).system Y)
        ((D.coefficient L).roos Y) ((D.scalar E L ι).model Y)) ℤ := by
    unfold integralComparisonScalarCounit
    exact reduced_realization_commShift (integralScalarExtensionOfUniverses l E L ι Y)
      ((D.coefficient E).system Y).reduction
      (integralComparisonDerivedSequenceScalar l E L ι Y) (coefficientSequenceLimit l L Y)
      ((D.coefficient L).system Y).reduction ((D.scalar E L ι).model Y).realization.hom
      ((D.coefficient L).system Y).adjunction.counit
  have : NatTrans.CommShift (integralComparisonSystemScalarPullback l E L ι f).hom ℤ :=
    integralComparisonSystemScalarPullback_commShift l E L ι f
  have : NatTrans.CommShift (thetaLambda l E L ι f D) ℤ := by
    unfold thetaLambda
    infer_instance
  have : NatTrans.CommShift (thetaMu l E L ι f D) ℤ := by
    unfold thetaMu
    infer_instance
  have : IsIso ((thetaMu l E L ι f D).app K.obj) := by
    rw [thetaMu_app]
    infer_instance
  have hAmbient := comparison_shift_of_realizations _ _ _
    (thetaLambda l E L ι f D) (thetaMu l E L ι f D)
    K.obj (K⟦m⟧).obj m (((sfIntegralConstructible l E Y).ι.commShiftIso m).app K)
    (integralComparisonScalar l E L ι D f K)
    (integralComparisonScalar l E L ι D f (K⟦m⟧))
    (theta_comp_mu l E L ι f D K)
    (theta_comp_mu l E L ι f D (K⟦m⟧))
  have h : (sfFrameworkTheta l E L ι f D (K⟦m⟧)).hom ≫
      (sfFrameworkThetaTargetShift l E L ι f S K m).hom =
    (sfFrameworkThetaSourceShift l E L ι f S K m).hom ≫
      (sfFrameworkTheta l E L ι f D K).hom⟦m⟧' := by
    apply (sfIntegralConstructible l L X).ι.map_injective
    apply (cancel_mono
      (((sfIntegralConstructible l L X).ι.commShiftIso m).hom.app
        ((sfFrameworkThetaTarget l E L ι f).obj K))).1
    simp only [Functor.map_comp]
    simp only [Category.assoc]
    rw [Functor.commShiftIso_hom_naturality]
    simp only [sfFrameworkTheta, sfFrameworkThetaSourceShift,
      sfFrameworkThetaTargetShift, ObjectProperty.ι_map, ObjectProperty.isoMk,
      ObjectProperty.homMk, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.commShiftIso_comp_hom_app,
      Functor.comp_map] at hAmbient ⊢
    erw [Category.comp_id]
    exact hAmbient
  have hi : (sfFrameworkTheta l E L ι f D (K⟦m⟧)).inv ≫
      (sfFrameworkThetaSourceShift l E L ι f S K m).hom =
    (sfFrameworkThetaTargetShift l E L ι f S K m).hom ≫
      (sfFrameworkTheta l E L ι f D K).inv⟦m⟧' := by
    apply (cancel_epi (sfFrameworkTheta l E L ι f D (K⟦m⟧)).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, h, Category.assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  refine ⟨h, hi, ?_, ?_⟩
  · simpa only [Functor.map_comp] using
      congrArg (sfRationalConstructibleLocalization l L X).map h
  · simpa only [Functor.map_comp] using
      congrArg (sfRationalConstructibleLocalization l L X).map hi

end WeilConjectures
