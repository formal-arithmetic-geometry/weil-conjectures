/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.SmoothPurityTowerGluingData
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
import Sheaf.Paper.FiniteNormalizedOrientationScalar
import Sheaf.Paper.CoefficientUnitTowerNormalized
import all Sheaf.AlgebraicGeometry.IntrinsicRealizationTensorComplex
import all Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Sheaf.SecSmoothPurity.ReductionCompatibilities
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-! # Finite diagonal orientations at the unit and under reduction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (1)--(3)
(blueprint: lem-sp-finite-orientation-reduction).

The natural index n means the positive coefficient exponent n+1. All ordinary-etale
arrows below are the recorded presentations of the finite pro-etale arrows, with
coefficient units identified by their multiplication and pullback constraints.
An orientation parameter is constrained by the dependency's diagonal/DNC normalization;
it is a presentation of the specified orientation, never a freely chosen endpoint iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

/-- The positive-level uniformizer presentation; it keeps the fixed field and extension.
Source: gamma proof (1), R_n=A_(E,en)
(blueprint: lem-sp-finite-orientation-reduction). -/
def setting (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e) (n : ℕ) :
    PurityFiniteSetting.{u} :=
  { P with level := e * (n + 1), level_pos := Nat.mul_pos he (Nat.succ_pos n) }

/-- Equality of the actual quotient ideals, including ramification.
Source: gamma proof (1), ell=u varpi^e
(blueprint: lem-sp-finite-orientation-reduction).
Proof: the unit factor generates the unit ideal. Thus (ell)=(varpi)^e.
Raise this equality to n+1 and use the ideal-power multiplication formula. -/
theorem coefficient_ideal (P : PurityFiniteSetting.{u}) (e : ℕ)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (_hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e) (n : ℕ) :
    spEllIdeal P.coefficients.l P.extension ^ (n + 1) =
      Padic.coefficientExtensionIdeal P.coefficients.l P.extension (e * (n + 1)) := by
  unfold spEllIdeal Padic.coefficientExtensionIdeal
  rw [_hv, Ideal.span_singleton_mul_left_unit v.isUnit,
    ← Ideal.span_singleton_pow, ← pow_mul]

/-- The canonical coefficient equivalence, induced by the identity on O_E.
Source: gamma proof (1), quotient identification
(blueprint: lem-sp-finite-orientation-reduction). -/
def coefficientEquiv (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e) (n : ℕ) :
    SpTowerShriek.R P.coefficients.l P.extension n ≃+* (setting P e he n).Ring :=
  Ideal.quotEquivOfEq (coefficient_ideal P e v hv n)

/-- The inverse diagonal comparison with the tensor unit as coefficient object.
Only the canonical single-complex unit comparison changes the source coordinates.
Source: gamma proof (1), finite diagonal orientation
(blueprint: lem-sp-finite-orientation-reduction). -/
def ordinaryOrientation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    (alpha : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d) :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalTwistEtale X d :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    (PurityFiniteSetting.smoothPurityUnitIso P.Coefficient Y).symm ≪≫ alpha

private theorem tensor_mate_unit
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)] (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (hπ : π (R.obj (𝟙_ D)) (𝟙_ D) ≫
      L.map (R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom) =
        (ρ_ (L.obj (R.obj (𝟙_ D)))).hom) :
    adj.projectionTensorMap π (𝟙_ D) (𝟙_ D) ≫ R.map (λ_ (𝟙_ D)).hom =
      R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom := by
  apply Adjunction.ext_of_comp_counit (adj := adj)
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [Adjunction.map_projectionTensorMap_comp_counit_assoc]
  apply (cancel_epi (π (R.obj (𝟙_ D)) (𝟙_ D))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hπ]
  simpa only [Functor.comp_obj, Functor.id_obj, unitors_equal] using
    (rightUnitor_naturality (adj.counit.app (𝟙_ D)))

private theorem braided_tensor_mate
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (P W : C) (K : D) (Q : D)
    (π : F.obj (W ⊗ P) ⟶ Q ⊗ K) (ε : Q ⟶ 𝟙_ D) :
    adj.homEquiv _ _ (F.map (β_ P W).hom ≫ π ≫
        (β_ Q K).hom ≫ (K ◁ ε) ≫ (ρ_ K).hom) =
      (β_ P W).hom ≫ (adj.homEquiv _ _ (π ≫ (ε ▷ K)) ≫ G.map (λ_ K).hom) := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private theorem gamma_unit
    {C : Type*} [Category* C] [MonoidalCategory C]
    {P W L : C} (u : P ≅ 𝟙_ C) (alpha : W ≅ L) (theta : P ⊗ W ⟶ W)
    (h : u.inv ▷ W ≫ theta = (λ_ W).hom) :
    (λ_ L).inv ≫ u.inv ▷ L ≫ P ◁ alpha.inv ≫ theta = alpha.inv := by
  rw [← whisker_exchange_assoc, h]
  simp

universe uA
section
open AlgebraicGeometry.Etale
open scoped AlgebraicGeometry.Etale
variable {A : Type uA} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [(Etale.rightDerivedLowerShriek A f).IsLeftAdjoint]
  [IsIso (Etale.projectionMap A f)]

private theorem tensor_unit :
    Etale.dualizingComplexTensorMapOfIsIso f (𝟙_ _) =
      (Etale.dualizingComplex A f) ◁ (Etale.leftDerivedUpperStarUnitIso A f).hom ≫
        (ρ_ (Etale.dualizingComplex A f)).hom := by
  exact tensor_mate_unit (Etale.rightDerivedUpperShriekAdjunction A f)
    (fun M N ↦ ((Etale.projectionMap A f).app M).app N)
    (Etale.leftDerivedUpperStarUnitIso A f) (Etale.projectionMap_rightUnitality A f _)
private theorem smooth_tensor_eq
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    let := Etale.derivedBraidedCategory A X
    Etale.smoothTensorDualityMap A f inferInstance K =
      (β_ ((Etale.upperStar A f).leftDerivedFunctor.obj K) (Etale.dualizingComplex A f)).hom ≫
        Etale.dualizingComplexTensorMapOfIsIso f K := by
  let := Etale.derivedBraidedCategory A X
  let := Etale.derivedBraidedCategory A Y
  exact braided_tensor_mate (Etale.rightDerivedUpperShriekAdjunction A f) _ _ K _
    (inv (((Etale.projectionMap A f).app _).app K))
    ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app _)

private theorem tensor_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : K ⟶ K') :
    ((Etale.derivedTensor A X).obj (Etale.dualizingComplex A f)).map
        ((Etale.upperStar A f).leftDerivedFunctor.map g) ≫
        Etale.dualizingComplexTensorMapOfIsIso f K' =
      Etale.dualizingComplexTensorMapOfIsIso f K ≫
        (Etale.rightDerivedUpperShriek A f).map g := by
  let := Etale.derivedBraidedCategory A X
  have h := Adjunction.projectionTensorMap_naturality_right
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (fun M N ↦ ((Etale.projectionMap A f).app M).app N)
    (Etale.projectionMap_app_app_naturality_right f) (𝟙_ _) g
  dsimp only [Etale.dualizingComplexTensorMapOfIsIso]
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ _ ≫ (Etale.rightDerivedUpperShriek A f).map k)
    (leftUnitor_naturality g)

private theorem smooth_tensor_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : K ⟶ K') :
    ((Etale.upperStar A f).leftDerivedFunctor.map g) ▷ Etale.dualizingComplex A f ≫
        Etale.smoothTensorDualityMap A f inferInstance K' =
      Etale.smoothTensorDualityMap A f inferInstance K ≫
        (Etale.rightDerivedUpperShriek A f).map g := by
  let := Etale.derivedBraidedCategory A X
  rw [smooth_tensor_eq, smooth_tensor_eq]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  change _ ≫ ((Etale.derivedTensor A X).obj (Etale.dualizingComplex A f)).map
    ((Etale.upperStar A f).leftDerivedFunctor.map g) ≫ _ = _
  rw [tensor_naturality]
  simp only [Category.assoc]

private theorem smooth_tensor_unit :
    (Etale.leftDerivedUpperStarUnitIso A f).inv ▷ Etale.dualizingComplex A f ≫
      Etale.smoothTensorDualityMap A f inferInstance (𝟙_ _) =
      (λ_ (Etale.dualizingComplex A f)).hom := by
  let := Etale.derivedBraidedCategory A X
  rw [smooth_tensor_eq, tensor_unit]
  simp only [← BraidedCategory.braiding_naturality_left_assoc]
  simp

end

/-- At the coefficient unit the specified theta is the identity, and gamma is the
inverse orientation, after the canonical pullback-unit and tensor-unit identifications.
Source: gamma proof (2), coefficient-unit tensor transpose
(blueprint: lem-sp-finite-orientation-reduction).
Proof: the compactification projection map at the coefficient unit is the identity.
Its proper factor is the counit-defined projection mate of
lem-weil-pbc-ringed-projection-mate-exact; its open factor sends m tensor a to m tensor a,
as in lem-cbc-extension-zero-projection-formula. The free degree-zero coefficient
unit computes its own derived tensor. The defining transpose is consequently the
adjunct of the exceptional counit, hence the identity by the triangle identity.
Inserting this in gamma=(1 tensor alpha inverse) followed by theta gives alpha inverse.
The displayed pullback-unit and left unitor write out those source identifications. -/
theorem coefficient_unit_purity (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X)
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L) :
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).inv ▷
        Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≫
      Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f
        (Etale.isIso_projectionMap_of_finite A f) (𝟙_ _) =
      (λ_ (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)).hom ∧
    (λ_ L).inv ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).inv ▷ L ≫
        Etale.FiniteSmoothPurity.gamma A f L alpha (𝟙_ _) = alpha.inv := by
  have ht := smooth_tensor_unit (A := ModuleCat.{u + 1} A) f
  refine ⟨ht, ?_⟩
  exact gamma_unit (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f) alpha
    (Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (Etale.isIso_projectionMap_of_finite A f) (𝟙_ _)) ht


/-- The fixed-ring source identification at the coefficient unit: pull back the
single-complex unit, identify the pulled-back unit, then apply the left unitor.
Source: gamma proof (2), tensor-unit identifications
(blueprint: lem-sp-finite-orientation-reduction). -/
def sourceUnitIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Etale.DerivedCategoryModule A X) :
    ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.ordinaryFinitePullback A f).obj (Etale.ordinaryFiniteUnit A Y))).obj L ≅ L :=
  ((Etale.ordinaryFiniteTensor A X).mapIso
    ((Etale.ordinaryFinitePullback A f).mapIso
      (PurityFiniteSetting.smoothPurityUnitIso A Y) ≪≫
      Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f)).app L ≪≫ λ_ L

private theorem etale_theta_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    PurityFiniteSetting.smoothPurityEtaleTheta A f (Etale.ordinaryFiniteUnit A Y) =
      (sourceUnitIso A f
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.ordinaryFiniteUnit A Y))).hom := by
  let U := PurityFiniteSetting.smoothPurityUnitIso A Y
  let H := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f
  let P := (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let W := Etale.dualizingComplex (ModuleCat.{u + 1} A) f
  let V := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f
  have ht := smooth_tensor_unit (A := ModuleCat.{u + 1} A) f
  have hn := smooth_tensor_naturality (A := ModuleCat.{u + 1} A) f U.hom
  have hs : Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      inferInstance (𝟙_ _) = V.hom ▷ W ≫ (λ_ W).hom := by
    apply (cancel_epi (V.inv ▷ W)).1
    simpa only [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
      id_whiskerRight, Category.id_comp] using ht
  have he : PurityFiniteSetting.smoothPurityEtaleTheta A f
      (Etale.ordinaryFiniteUnit A Y) =
      (P.obj (Etale.ordinaryFiniteUnit A Y) ◁ H.map U.hom) ≫
        Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f inferInstance
          (Etale.ordinaryFiniteUnit A Y) := by
    rw [smooth_tensor_eq]
    rfl
  rw [he]
  apply (cancel_mono (H.map U.hom)).1
  simp only [Category.assoc]
  rw [← hn]
  dsimp only [W] at hs
  rw [hs]
  erw [whisker_exchange_assoc, whisker_exchange_assoc]
  change _ ≫ _ ≫ (𝟙_ _ ◁ H.map U.hom) ≫ (λ_ _).hom = _
  rw [leftUnitor_naturality]
  simp only [sourceUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

/-- The recorded pro-etale purity map at the coefficient unit is precisely the
inverse of the recorded canonical diagonal isomorphism. The displayed source
identification uses only its specified pullback and monoidal site comparisons.
Source: gamma proof (1)--(2), a_n=gamma_(f,R_n)(R_(n,Y))
(blueprint: lem-sp-finite-orientation-reduction).
Proof: smoothPurityTensorMapInPresentation tensors the actual inverse diagonal
comparison and applies smoothPurityTheta. At the unit the ordinary theta is the
identity by coefficient_unit_purity. Naturality of the site tensor comparison
moves the inverse diagonal map past the source comparison; the two comparison
adjunction triangle identities cancel the origin unit/counit. The resulting
arrow is the displayed source identification followed by diagonalDualizingObject.inv.
The reassociation in smoothPurityMap is its prescribed tau, so the same equality
is the node's gamma equality under the Tate/unit source identifications. -/
theorem canonical_purity_at_unit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasCompactification f] :
    P.smoothPurityTensorMapInPresentation f d aY
        (finiteGeneralRingUnit P.Coefficient Y) (Etale.ordinaryFiniteUnit P.Coefficient Y)
        (Iso.refl _) =
      (((PurityFiniteSetting.smoothPurityTensor P.Coefficient X).mapIso
        (P.smoothPurityPullbackComparison f (finiteGeneralRingUnit P.Coefficient Y)
          (Etale.ordinaryFiniteUnit P.Coefficient Y) (Iso.refl _))).app
            (P.diagonalTwist X d)).hom ≫
      (PurityFiniteSetting.smoothPurityComparisonTensor P.Coefficient X
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) (P.diagonalTwistEtale X d)).inv ≫
      (Etale.FiniteSmoothPurity.comparison P.Coefficient X).map
        (sourceUnitIso P.Coefficient f (P.diagonalTwistEtale X d)).hom ≫
      (P.diagonalDualizingObject d f aY).inv := by
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let K := Etale.ordinaryFiniteUnit P.Coefficient Y
  let M := (Etale.ordinaryFinitePullback P.Coefficient f).obj K
  let T := Etale.ordinaryFiniteTensor P.Coefficient X
  let S := PurityFiniteSetting.smoothPurityTensor P.Coefficient X
  let w := P.diagonalDualizingComparison f
  let p := P.smoothPurityPullbackComparison f (finiteGeneralRingUnit P.Coefficient Y)
    K (Iso.refl _)
  let c (V : Etale.DerivedCategoryModule P.Coefficient X) :=
    PurityFiniteSetting.smoothPurityComparisonTensor P.Coefficient X M V
  obtain ⟨e, _, he⟩ := (P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec
  have he' : P.diagonalDualizingObject d f aY = w ≪≫ F.mapIso e := he
  have hc : (S.obj (F.obj M)).map (F.map e.inv) ≫
      (c (P.diagonalOrdinaryDualizing f)).inv =
      (c (P.diagonalTwistEtale X d)).inv ≫ F.map ((T.obj M).map e.inv) :=
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) M).inv.naturality e.inv
  have hp := (S.map p.hom).naturality (F.map e.inv ≫ w.inv)
  have hu : (T.obj M).map e.inv ≫
      (sourceUnitIso P.Coefficient f (P.diagonalOrdinaryDualizing f)).hom =
      (sourceUnitIso P.Coefficient f (P.diagonalTwistEtale X d)).hom ≫ e.inv := by
    dsimp only [sourceUnitIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app]
    rw [← Category.assoc, NatTrans.naturality]
    simp only [Category.assoc]
    change _ ≫ (𝟙_ _ ◁ e.inv) ≫ (λ_ _).hom = _
    rw [leftUnitor_naturality]
  let H := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f
  let R := (ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let η := (ProEtale.derivedComparisonAdjunction
    (ModuleCat.{u + 1} P.Coefficient) Y).unit.app K
  have hw : F.map (H.map (η ≫ R.map (𝟙 _))) = w.inv := by
    change F.map (H.map (η ≫ R.map (𝟙 _))) = F.map (H.map η)
    rw [R.map_id]
    exact congrArg (fun z ↦ F.map (H.map z)) (Category.comp_id η)
  have ht : P.smoothPurityTheta f (finiteGeneralRingUnit P.Coefficient Y) K
      (Iso.refl _) =
      (S.map p.hom).app (P.diagonalDualizing f) ≫
        (S.obj (F.obj M)).map w.hom ≫ (c (P.diagonalOrdinaryDualizing f)).inv ≫
        F.map (sourceUnitIso P.Coefficient f (P.diagonalOrdinaryDualizing f)).hom ≫
        w.inv := by
    simp only [PurityFiniteSetting.smoothPurityTheta,
      PurityFiniteSetting.smoothPurityTensorComparison, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    rw [etale_theta_unit]
    simp only [PurityFiniteSetting.smoothPurityExceptionalComparison, Iso.app_inv,
      Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
    change (S.map p.hom).app _ ≫ (S.obj (F.obj M)).map w.hom ≫
      (c _).inv ≫ F.map (sourceUnitIso P.Coefficient f
        (P.diagonalOrdinaryDualizing f)).hom ≫
      F.map (H.map (η ≫ R.map (𝟙 _))) ≫ 𝟙 _ = _
    rw [hw, Category.comp_id]
  have hm : (S.obj (F.obj M)).map (F.map e.inv ≫ w.inv) ≫
      (S.obj (F.obj M)).map w.hom = (S.obj (F.obj M)).map (F.map e.inv) := by
    rw [← Functor.map_comp]
    rw [Category.assoc, w.inv_hom_id, Category.comp_id]
  rw [PurityFiniteSetting.smoothPurityTensorMapInPresentation, ht, he']
  simp only [Iso.trans_inv, Functor.mapIso_inv]
  change (S.obj _).map (F.map e.inv ≫ w.inv) ≫
    (S.map p.hom).app _ ≫ (S.obj (F.obj M)).map w.hom ≫
    (c _).inv ≫ F.map _ ≫ w.inv =
    (S.map p.hom).app _ ≫ (c _).inv ≫ F.map _ ≫ F.map e.inv ≫ w.inv
  rw [reassoc_of% hp]
  rw [reassoc_of% hm, reassoc_of% hc]
  rw [← F.map_comp_assoc, hu, F.map_comp]
  simp only [Category.assoc]
  rfl


/-- The ordinary commutative ring structure on the lifted ell-power quotient, cached
once to keep its finite derived-category signatures small.
Source: gamma proof (1), coefficient convention
(blueprint: lem-sp-finite-orientation-reduction). -/
@[instance_reducible]
def towerCoefficientCommRing (P : PurityFiniteSetting.{u}) (n : ℕ) :
    CommRing (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l P.extension n)) :=
  inferInstance

attribute [local instance] towerCoefficientCommRing

/-- Direct finite-ring orientation and the uniformizer-level diagonal construction
are the same, under the identity-induced coefficient equivalence and canonical Tate map.
The two normalization predicates specify the actual maps used by the dependencies.
Source: gamma proof (1)--(2), general-ring agreement
(blueprint: lem-sp-finite-orientation-reduction).
Proof: det-sp-finite-general-ring (2) identifies scalar extension with the direct
orientation: diagonal base change, the unique t=1-normalized Rees comparison and
Kummer-normalized vector integration all commute with the coefficient map.
At the uniformizer level thm-pur-diagonal-dualizing-object has the same coordinate
normalization. Its uniqueness identifies the orientations. Taking inverses gives
this equation, whose coefficient map is the actual exceptional counit mate at the unit.
No isomorphism of dualizing objects is chosen independently. -/
theorem uniformizer_orientation_agreement
    (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ)
    (alphaP : (setting P e he n).diagonalOrdinaryDualizing f ≅
      (setting P e he n).diagonalTwistEtale X d)
    (_hP : (setting P e he n).DiagonalOrientationNormalization d f
      (Y ↘ Spec (.of P.field.k)) alphaP)
    (hR : ((P.coefficients.l ^ (n + 1) : ℕ) :
      ULift.{u + 1} (SpTowerShriek.R P.coefficients.l P.extension n)) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaR : Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (SpTowerShriek.R P.coefficients.l P.extension n))) f ≅
      Etale.FiniteSmoothPurity.line _ (P.coefficients.l ^ (n + 1)) hR X d)
    (_hR : Etale.FiniteSmoothPurity.OrientationNormalized _ _
      (pow_pos P.coefficients.prime.out.pos _) hR f d geometry
      (({ P with level := n + 1, level_pos := Nat.succ_pos n } :
        PurityFiniteSetting).diagonalExponent_isUnit (X ↘ Spec (.of P.field.k))) alphaR)
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom)
      (setting P e he n).diagonalExponent (P.coefficients.l ^ (n + 1))
      (setting P e he n).diagonalExponent_annihilates hR X) :
    (Etale.FiniteSmoothPurity.ordinaryScalar
      (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) X).map
        (ordinaryOrientation (setting P e he n) f d alphaP).inv ≫
      Etale.ExceptionalCoefficients.dualizingScalarMap
        (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) f =
    (t.tensorPower d).hom ≫ alphaR.inv := by
  sorry

/-- The lifted quotient-ring structure, cached with explicit prime and extension.
This is the existing structure, named once for checking and exported premise indices.
Source: gamma proof (3), coefficient convention
(blueprint: lem-sp-finite-orientation-reduction). -/
@[instance_reducible]
def quotientCoefficientCommRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    CommRing (ULift.{u + 1} (SpTowerShriek.R l E n)) := inferInstance

section QuotientOrientation
attribute [local instance] quotientCoefficientCommRing


/-- The actual quotient equation for the inverse diagonal orientations. The exponent
n denotes n+1 and m denotes m+1, so the equation includes equal levels and level one.
The Tate comparison retains its power-map and scalar/root-generator normalizations.
Source: gamma proof (3), specialized to the coefficient unit
(blueprint: lem-sp-finite-orientation-reduction).
Proof: specialize normalizedOrientation_scalar, whose proof unpacks the supplied
diagonal/DNC normalizations. Invertibility of the
normal-section comparison and the integration adjunct expresses each orientation
as its diagonal base-change factor followed by integratedSpecialization. The
coefficient square for the first factor is finiteSmoothDiagonalScalar. The square
for the second factor is integratedSpecialization_scalar; its root exponent
divisibility is l^(m+1) dividing l^(n+1). The quotient map carries hN to the
common-exponent annihilation of the target ring. Compose the two squares to obtain
dualizingScalarMap followed by alphaM.hom equal to scalar extension of alphaN.hom
followed by t.tensorPower d. Cancel the two orientation isomorphisms to obtain the
inverse-orientation equation. These are the actual unit-normalized exceptional
coefficient maps throughout.
No flatness of the quotient is assumed, including in ramified extensions. -/
theorem finite_orientation_reduction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (m n : ℕ) (hmn : m ≤ n)
    (hN : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (SpTowerShriek.R l E n)) = 0)
    (hM : ((l ^ (m + 1) : ℕ) : ULift.{u + 1} (SpTowerShriek.R l E m)) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaN : Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) f ≅
      Etale.FiniteSmoothPurity.line _ (l ^ (n + 1)) hN X d)
    (alphaM : Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E m))) f ≅
      Etale.FiniteSmoothPurity.line _ (l ^ (m + 1)) hM X d)
    (_hn : Etale.FiniteSmoothPurity.OrientationNormalized _ _
      (pow_pos (Fact.out : l.Prime).pos _) hN f d geometry
      ((finiteGeneralRingPrimeSetting D l hl (n + 1) (Nat.succ_pos n)).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaN)
    (_hm : Etale.FiniteSmoothPurity.OrientationNormalized _ _
      (pow_pos (Fact.out : l.Prime).pos _) hM f d geometry
      ((finiteGeneralRingPrimeSetting D l hl (m + 1) (Nat.succ_pos m)).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaM)
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift (SpTowerCalculus.quotient l E hmn))
      (l ^ (n + 1)) (l ^ (m + 1)) hN hM X) :
    (Etale.FiniteSmoothPurity.ordinaryScalar
      (RingHom.ulift (SpTowerCalculus.quotient l E hmn)) X).map alphaN.inv ≫
      Etale.ExceptionalCoefficients.dualizingScalarMap
        (RingHom.ulift (SpTowerCalculus.quotient l E hmn)) f =
      (t.tensorPower d).hom ≫ alphaM.inv := by
  exact Etale.FiniteSmoothPurity.normalizedOrientation_scalar
    (RingHom.ulift (SpTowerCalculus.quotient l E hmn))
    (l ^ (n + 1)) (l ^ (m + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (pow_pos (Fact.out : l.Prime).pos _) (pow_dvd_pow l (Nat.add_le_add_right hmn 1))
    hN hM ((finiteGeneralRingPrimeSetting D l hl (n + 1)
      (Nat.succ_pos n)).diagonalExponent_isUnit (Y ↘ Spec (.of D.k))) f d geometry
    ((finiteGeneralRingPrimeSetting D l hl (n + 1)
      (Nat.succ_pos n)).diagonalExponent_isUnit (X ↘ Spec (.of D.k)))
    ((finiteGeneralRingPrimeSetting D l hl (m + 1)
      (Nat.succ_pos m)).diagonalExponent_isUnit (X ↘ Spec (.of D.k)))
    alphaN alphaM _hn _hm t


end QuotientOrientation

/-- The general-ring and uniformizer purity comparisons agree on every allowed input.
The maps are the recorded inverse-orientation/tensor-transpose composites, with the
canonical pullback and Tate balancing rather than an arbitrary source isomorphism.
Source: gamma proof (2), general-ring purity identification
(blueprint: lem-sp-finite-orientation-reduction).
Proof: uniformizer_orientation_agreement identifies the inverse orientations by
finite-general-ring (2). Clause (3) uses the same inverse compact-support projection
and counit to define both gamma maps. Their scalar compatibility is
reduction-compatibilities (3): transpose both paths, apply the compactification
proper/open scalar-projection square and the defining counit equation of coefficient
change. Substitute the inverse-orientation equation. All input and output
identifications are exactly pullbackTwistComparison and mateMap. -/
theorem uniformizer_purity_agreement
    (P : PurityFiniteSetting.{u}) (e : ℕ) (he : 1 ≤ e)
    (v : (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)ˣ)
    (hv : (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension) = v *
        Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^ e)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ)
    (alphaP : (setting P e he n).diagonalOrdinaryDualizing f ≅
      (setting P e he n).diagonalTwistEtale X d)
    (_hP : (setting P e he n).DiagonalOrientationNormalization d f
      (Y ↘ Spec (.of P.field.k)) alphaP)
    (hR : ((P.coefficients.l ^ (n + 1) : ℕ) :
      ULift.{u + 1} (SpTowerShriek.R P.coefficients.l P.extension n)) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaR : Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (SpTowerShriek.R P.coefficients.l P.extension n))) f ≅
      Etale.FiniteSmoothPurity.line _ (P.coefficients.l ^ (n + 1)) hR X d)
    (_hR : Etale.FiniteSmoothPurity.OrientationNormalized _ _
      (pow_pos P.coefficients.prime.out.pos _) hR f d geometry
      (({ P with level := n + 1, level_pos := Nat.succ_pos n } :
        PurityFiniteSetting).diagonalExponent_isUnit (X ↘ Spec (.of P.field.k))) alphaR)
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom)
      (setting P e he n).diagonalExponent (P.coefficients.l ^ (n + 1))
      (setting P e he n).diagonalExponent_annihilates hR X)
    (K : Etale.DerivedCategoryModule (setting P e he n).Coefficient Y)
    (_hK : Etale.DerivedCategory.boundedConstructibleFiniteTor
      (setting P e he n).Coefficient Y K) :
    (Etale.FiniteSmoothPurity.ordinaryScalar
      (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) X).map
        (Etale.FiniteSmoothPurity.gamma (setting P e he n).Coefficient f _
          (ordinaryOrientation (setting P e he n) f d alphaP) K) ≫
      Etale.ExceptionalCoefficients.mateMap
        (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) f K =
    (Etale.FiniteSmoothPurity.pullbackTwistComparison f d t K).hom ≫
      Etale.FiniteSmoothPurity.gamma _ f _ alphaR
        ((Etale.FiniteSmoothPurity.ordinaryScalar
          (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) Y).obj K) := by
  exact Etale.FiniteSmoothPurity.ordinaryGammaCoefficient
    (RingHom.ulift (coefficientEquiv P e he v hv n).symm.toRingHom) f
    _ _ _ _ d t (ordinaryOrientation (setting P e he n) f d alphaP) alphaR
    (uniformizer_orientation_agreement P e he v hv f d n alphaP _hP hR geometry
      alphaR _hR t) K

end AlgebraicGeometry.ProEtale.SpFiniteOrientation

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

private def tensorUnitIso
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) : F.obj (𝟙_ C) ≅ 𝟙_ D :=
  let K := F.objPreimage (𝟙_ D)
  let k := F.objObjPreimageIso (𝟙_ D)
  (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) k.symm ≪≫
    (e.app (𝟙_ C, K)).symm ≪≫ F.mapIso (λ_ K) ≪≫ k

private theorem intrinsic_tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a z : ℤ)
    (h : HasProEtaleTorAmplitude T A K a z) : HasProEtaleTorAmplitude T A L a z := by
  refine ⟨h.1, ?_⟩
  rintro C P ⟨eC⟩ f hf hP M i hi
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_unit_bounds (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    let U := (DerivedCategory.singleFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) 0).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing T A)))
    (∀ i : ℤ, (i < 0 ∨ 0 < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj U)) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ i).obj U)) ∧
    HasProEtaleTorAmplitude T A U 0 0 := by
  let C := Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))
  let F := finiteCoefficientIntrinsicRealization T A
  let := (finiteCoefficientIntrinsicRealization_exact T A).1
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
  obtain ⟨t⟩ := intrinsicTensorNatIso T A
  let eU := tensorUnitIso F t
  let K := (DerivedCategory.singleFunctor C 0).obj (𝟙_ C)
  let e : F.mapDerivedCategory.obj K ≅ _ :=
    (F.mapDerivedCategorySingleFunctor 0).app (𝟙_ C) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eU
  have hz (i : ℤ) (hi : i < 0 ∨ 0 < i) :
      IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE K 0 i hi
    · exact DerivedCategory.isZero_of_isLE K 0 i hi
  let G := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  have hbc : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
    refine ⟨(DerivedCategory.singleFunctor _ 0).obj (𝟙_ _),
      Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0, ⟨?_⟩⟩
    exact (G.mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
      (DerivedCategory.singleFunctor C 0).mapIso (Functor.Monoidal.εIso G).symm
  have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic K hbc
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (F.map_isZero (hz i hi)).of_iso
      (((F.mapDerivedCategoryHomologyFunctorIso i).app K) ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    apply intrinsicConstructible_of_iso T A
      (((F.mapDerivedCategoryHomologyFunctorIso i).app K) ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e)
    exact (intrinsicRealization_constructible_iff T A _).2 (hc.2 i)
  · apply intrinsic_tor_iso T A e 0 0
    apply (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T 0 0 le_rfl K).2
    exact DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.flat_of_isDualizable isDualizable_unit)


private def pushforwardUnitIso
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u})
    (S : Sheaf J RingCat.{u})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (SheafOfModules.pushforward.{u} (eqToHom h)).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  subst S
  exact Iso.refl _


private def evaluationUnitIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (SpTowerShriek.ev l E T n).obj (SpTowerClasses.coefficient T
      (SpTowerClasses.Arings l E T)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T (SpTowerShriek.R l E n))) := by
  exact pushforwardUnitIso _ _ _
    (SemilinearSections.evaluation_ring (ProEt.topology T)
      (fun n ↦ SpTowerShriek.B l E T n) (SpTowerShriek.tau l E T) n).symm

private theorem evaluation_unit_single
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) (n : ℕ) : Nonempty
    ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
        (SpTowerClasses.unit T (SpTowerClasses.Arings l E T))) ≅
    (DerivedCategory.singleFunctor
      (proEtaleRingModules T (proEtaleConstantRing T (SpTowerShriek.R l E n))) 0).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing T (SpTowerShriek.R l E n))))) := by
  let := (q.abelian T).hasDerived
  let U := SpTowerClasses.unit T (SpTowerClasses.Arings l E T)
  let R := SpTowerCalculus.realization l E b T (q.abelian T)
  refine ⟨(SpTowerCalculus.levelComparison l E b q T n).symm.app (R.inverse.obj U) ≪≫
    (SpTowerShriek.Ev l E T n).mapIso (R.counitIso.app U) ≪≫ ?_⟩
  exact ((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app
    (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (evaluationUnitIso l E T n)


/-- The coefficient unit belongs to the uniform finite-Tor constructible tower domain.
The term is the specified inverse realization of the actual strict coefficient system,
not a diagram in a derived category.
Source: gamma proof (1), coefficient tower and its common [0,0] bounds
(blueprint: lem-sp-finite-orientation-reduction).
Proof: every finite evaluation is the constant free rank-one module in degree zero.
Its cohomology and Tor intervals are both [0,0], uniformly in the positive level.
The rank-one constant sheaf is constructible on the single stratum T. Exact evaluation
and the section-normalized realization preserve these identifications. -/
theorem unit_tower_mem
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) :
    spConstructibleTorTowers l E T (q.abelian T)
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
        (SpTowerClasses.unit T (SpTowerClasses.Arings l E T))) := by
  let K := (SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
    (SpTowerClasses.unit T (SpTowerClasses.Arings l E T))
  have hlevel (n : ℕ) :
      (∀ i : ℤ, (i < 0 ∨ 0 < i) → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj
          ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K))) ∧
      (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T (SpTowerShriek.R l E n)
        ((DerivedCategory.homologyFunctor _ i).obj
          ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K))) ∧
      HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K) 0 0 := by
    obtain ⟨e⟩ := evaluation_unit_single l E b q T n
    obtain ⟨hz, hc, ht⟩ := finite_unit_bounds T (SpTowerShriek.R l E n)
    refine ⟨fun i hi ↦ (hz i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e), ?_,
      intrinsic_tor_iso T (SpTowerShriek.R l E n) e.symm 0 0 ht⟩
    intro i
    exact intrinsicConstructible_of_iso T (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor _ i).mapIso e.symm) (hc i)
  refine ⟨fun n ↦ ?_, 0, 0, 0, 0, le_rfl, le_rfl,
    fun n ↦ ⟨(hlevel n).1, (hlevel n).2.2⟩⟩
  exact ⟨⟨0, 0, le_rfl, (hlevel n).1⟩, (hlevel n).2.1,
    0, 0, (hlevel n).2.2⟩

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app L)] : IsIso (τ.app K) := by
  exact IsIso.of_isIso_fac_right (τ.naturality e.hom).symm

private theorem isIso_app_of_equivalence
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ E} (τ : F ⟶ G) (R : C ≌ D) {K : C} {U : D}
    (e : R.functor.obj K ≅ U) [IsIso (τ.app (R.inverse.obj U))] :
    IsIso (τ.app K) :=
  isIso_app_of_iso τ (R.unitIso.app K ≪≫ R.inverse.mapIso e)

private theorem map_homMk_hom_inv
    {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (F : P.FullSubcategory ⥤ Q.FullSubcategory)
    {K L : P.FullSubcategory} (f : K.obj ⟶ L.obj) [IsIso f] :
    (F.map (ObjectProperty.homMk f)).hom ≫
        (F.map (ObjectProperty.homMk (inv f))).hom = 𝟙 _ := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp]
  have h : ObjectProperty.homMk f ≫ ObjectProperty.homMk (inv f) = 𝟙 K := by
    ext
    exact IsIso.hom_inv_id f
  rw [h, F.map_id, ObjectProperty.FullSubcategory.id_hom]

private theorem square_comp_right_inverse
    {C : Type*} [Category* C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (k : A ⟶ E) (r : E ⟶ D) (s : D ⟶ E)
    (h : k ≫ r = f ≫ g) (hrs : r ≫ s = 𝟙 E) : f ≫ g ≫ s = k := by
  rw [← Category.assoc, ← h, Category.assoc, hrs, Category.comp_id]

/-- The actual dualizing-tower reduction is the finite coefficient mate at the unit.
`identification` is a whole strict-tower identification with the coefficient system.
The inverse input reduction writes out the canonical scalar-unit identification.
Source: gamma proof (1) and (3), finite evaluations and actual tower reductions
(blueprint: lem-sp-finite-orientation-reduction).
Proof: the unit tower has actual quotient transitions. Linearizing them sends
b tensor a to b*q(a), the canonical scalar unit. It computes its own derived scalar
extension, since it is free of rank one in degree zero. Its reduction is therefore
invertible; naturality transports this assertion through identification of whole
towers, which already preserves all transitions. det-sp-tower-gluing (3) evaluates
the exceptional reduction as the specified coefficientMate followed by G_m of this
input reduction. Cancel that canonical unit identification. The result is precisely
the displayed equality, so the finite-orientation quotient equation is compatibility
with the genuine reductions of omega, rather than with an independently chosen family. -/
theorem unit_tower_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj)
    (K : SpTowerCalculus.C l E b q Y)
    (_identification : (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K.obj ≅
      SpTowerClasses.unit Y (SpTowerClasses.Arings l E Y))
    (m n : ℕ) (h : m ≤ n) :
    ∃ hi : IsIso (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj),
      SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj ≫
          ((lv.comparison m).hom.app K).hom ≫
          ((lv.right m).map (ObjectProperty.homMk
            (@inv _ _ _ _
              (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj)
              hi))).hom =
        (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).map
            ((lv.comparison n).hom.app K).hom ≫
          (SpTowerGluing.coefficientMate l E b c m n h
            (lv.finite_closed n) (lv.finite_closed m) (lv.scalarX m n h) (lv.scalarY m n h)
            (lv.right n) (lv.right m) (lv.adjunction n) (lv.adjunction m)
            ((SpTowerGluing.level l E b q Y n).obj K)
            (lv.direct_image_iso m n h ((SpTowerGluing.level l E b q Y n).obj K))).hom := by
  let R := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let τ := (q.abelian Y).reduction h
  have hu : IsIso (τ.app (R.inverse.obj
      (SpTowerClasses.unit Y (SpTowerClasses.Arings l E Y)))) :=
    coefficient_unit_tower_normalized l E b q Y m n h
  have : IsIso (τ.app K.obj) := isIso_app_of_equivalence τ R _identification
  have hi : IsIso (SpTowerCalculus.reduction l E Y (q.abelian Y) h
      (q.scalar Y h) K.obj) := by
    dsimp only [SpTowerCalculus.reduction]
    infer_instance
  refine ⟨hi, ?_⟩
  exact square_comp_right_inverse _ _ _ _ _
    ((Category.assoc _ _ _).trans (lv.reduction m n h K))
    (map_homMk_hom_inv (lv.right m)
      (K := (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
        (lv.scalarY m n h)).obj ((SpTowerGluing.level l E b q Y n).obj K))
      (L := (SpTowerGluing.level l E b q Y m).obj K)
      (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))

end AlgebraicGeometry.ProEtale.SpFiniteOrientation
