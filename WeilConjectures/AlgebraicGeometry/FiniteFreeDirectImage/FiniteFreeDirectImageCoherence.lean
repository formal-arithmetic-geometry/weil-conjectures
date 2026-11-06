/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreePresentedScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeOrdinaryPullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImagePullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageColumns
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedFiniteFreeScalarCoordinates

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarModels
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite-free direct-image coefficient coherence

Source: Stacks Project, Tags 0B56 and 0944
(blueprint: lem-sp-finite-free-direct-image-coherence).

All module and derived categories are the existing ones. The auxiliary records bundle
coefficient squares and normalized presentations of the existing scalar functors.
Balancing is the conjugate of the canonical restriction/direct-image comparison, and
its right mate is the specified counit-tensor map. No arbitrary comparison is bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

/-- The identity equation for the actual direct-image mate.
Source: Stacks Project, Tags 0B56 and 0D6D.
(blueprint: lem-sp-finite-free-direct-image-coherence).

Proof: whisker the balancing square by the scalar multiplication units. Balancing
coherence identifies this square with the identity square. Whiskering commutes
with the mates correspondence, and the mate of the identity square is the identity.
Evaluating this equality gives the displayed equation. -/
private theorem finiteFreeDirectImageUnit {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z) (R : Coefficients q)
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    (sW.unit R.target).inv.app
        ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
      (comparison sW sZ (CoefficientMap.id R)).app M ≫
      (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
        ((sZ.unit R.source).hom.app M) = 𝟙 _ := by
  let adj := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let L := proEtaleRingDerivedPullback q R.target R.source R.identification
  let α := TwoSquare.mk _ _ _ _ (balancing sW sZ (CoefficientMap.id R)).hom
  have heq : (α.whiskerTop (sW.unit R.target).inv).whiskerBottom (sZ.unit R.source).hom =
      TwoSquare.mk (𝟭 _) L L (𝟭 _)
        ((Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv) := by
    ext K
    simpa [α, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using
      (finiteFreeDirectImageBalancingCoherence q sW sZ).1 R K
  have h := mateEquiv_whiskerTop_whiskerBottom adj adj α
    (sW.unit R.target).inv (sZ.unit R.source).hom
  rw [heq, mateEquiv_unitors] at h
  have hc := congrArg (fun t ↦ t.natTrans.app M) h
  simpa [comparison, α, TwoSquare.whiskerRight, TwoSquare.whiskerLeft] using hc.symm

/-- The coefficient tower equation for the actual direct-image mate.
Source: Stacks Project, Tags 0B56 and 0D6D.
(blueprint: lem-sp-finite-free-direct-image-coherence).

Proof: horizontally paste the two balancing squares and whisker by the inverse
target associator and source associator. Balancing coherence identifies this with
the single square for the composite ring map. Mate pasting identifies its mate
with the vertical paste of the two direct-image comparisons. Compatibility of
whiskering with mates supplies the two displayed associators. -/
private theorem finiteFreeDirectImageTower {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    (comparison sW sZ (a.comp b)).app M =
      (sW.normalization.derived a.target b.target).inv.app
          ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
        (sW.presentation b.target).derived.map ((comparison sW sZ a).app M) ≫
        (comparison sW sZ b).app ((sZ.presentation a.source).derived.obj M) ≫
        (proEtaleRingDerivedDirectImage q B.target B.source B.identification).map
          ((sZ.normalization.derived a.source b.source).hom.app M) := by
  let ar := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let as' := proEtaleRingDerivedAdjunction q S.target S.source S.identification
  let ab := proEtaleRingDerivedAdjunction q B.target B.source B.identification
  let α := TwoSquare.mk _ _ _ _ (balancing sW sZ a).hom
  let β := TwoSquare.mk _ _ _ _ (balancing sW sZ b).hom
  have heq : TwoSquare.whiskerBottom
      ((TwoSquare.hComp α β).whiskerTop (sW.normalization.derived a.target b.target).inv)
      (sZ.normalization.derived a.source b.source).hom =
      TwoSquare.mk _ _ _ _ (balancing sW sZ (a.comp b)).hom := by
    ext K
    simpa [α, β, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using
      ((finiteFreeDirectImageBalancingCoherence q sW sZ).2 R S B a b K).symm
  have h := mateEquiv_whiskerTop_whiskerBottom ar ab (TwoSquare.hComp α β)
    (sW.normalization.derived a.target b.target).inv
    (sZ.normalization.derived a.source b.source).hom
  rw [heq, mateEquiv_vcomp ar as' ab] at h
  have hc := congrArg (fun t ↦ t.natTrans.app M) h
  simpa [comparison, α, β, ar, as', ab, CoefficientMap.comp, TwoSquare.vComp,
    TwoSquare.whiskerRight,
    TwoSquare.whiskerLeft, Category.assoc] using hc

/-- Finite-free scalar change commutes canonically with ordinary unbounded derived
pushforward, as an isomorphism of exact functors, with input-shift, identity and tower
coherence. All equalities take place in the enlarged coefficient module category.
The existential scalar models only present the recorded universal derived functors;
their ordinary tensors, derived counits, units, adjunctions and associators are normalized.
In particular neither a balancing isomorphism nor a shift structure is an extra hypothesis.

Source: Stacks Tags 0B56 and 0944; shift and coefficient-tower coherences are extracted
from the counit-tensor construction (blueprint: lem-sp-finite-free-direct-image-coherence).

Proof:
1. Construct normalized scalar models by transporting the recorded restriction models
through their localization factorizations. Multiplication is the counit for identity
scalars; its universal localization gives the derived unit.
2. The inverse mate of exact restriction's factorization is the universal scalar counit
on flat-term K-flat complexes, hence on all complexes by resolving and naturality.
It commutes with shifts. The left adjoint of triangulated restriction is triangulated.
3. The finite-basis column calculation gives two biproduct coordinate isomorphisms.
Biproduct extensionality identifies the restricted comparison with the inverse
mapBiproduct comparison followed by the direct image of the source coordinates.
This is invertible, including for the empty biproduct. Conservative restriction
reflects its invertibility.
4. The canonical derived geometric adjunctions commute with their canonical shifts.
The restriction/direct-image comparison is the mate of the termwise restriction/
pullback comparison. Conjugating and taking its mate therefore proves the required
shift compatibility for the specified comparison.
5. Whisker balancing by the multiplication units. Its coherence equation identifies
this square with the identity square. Compatibility of mates with whiskering and
the mate of the identity square give the displayed identity equation.
6. Horizontally paste the two balancing squares and whisker with the two scalar
associators. Balancing coherence identifies this with the composite coefficient
square. Mate pasting gives the displayed tower equation in the stated factor order.
-/
theorem finiteFreeDirectImageCoherence {Z W : Scheme.{u}} (q : Z ⟶ W) :
    ∃ (sW : ScalarModel W) (sZ : ScalarModel Z),
      (∀ {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S),
        (sW.presentation a).derived.IsTriangulated ∧
          NatTrans.CommShift (sW.presentation a).counit ℤ) ∧
      (∀ {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S),
        (sZ.presentation a).derived.IsTriangulated ∧
          NatTrans.CommShift (sZ.presentation a).counit ℤ) ∧
      (∀ (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ),
        Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))) →
        IsIso (comparison sW sZ a) ∧ NatTrans.CommShift (comparison sW sZ a) ℤ ∧
          (proEtaleRingDerivedDirectImage q R.target R.source R.identification ⋙
            (sW.presentation a.target).derived).IsTriangulated ∧
          ((sZ.presentation a.source).derived ⋙
            proEtaleRingDerivedDirectImage q S.target S.source S.identification).IsTriangulated) ∧
      (∀ (R : Coefficients q) (M : DerivedCategory (proEtaleRingModules Z R.source)),
        (sW.unit R.target).inv.app
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
          (comparison sW sZ (CoefficientMap.id R)).app M ≫
          (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
            ((sZ.unit R.source).hom.app M) = 𝟙 _) ∧
      (∀ (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
        (d e : ℕ),
        Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))) →
        Nonempty ((proEtaleRingRestrictScalars b.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)
            (ULift.{u + 1} (Fin e))) →
        ∀ M : DerivedCategory (proEtaleRingModules Z R.source),
          (comparison sW sZ (a.comp b)).app M =
            (sW.normalization.derived a.target b.target).inv.app
                ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≫
              (sW.presentation b.target).derived.map ((comparison sW sZ a).app M) ≫
              (comparison sW sZ b).app ((sZ.presentation a.source).derived.obj M) ≫
              (proEtaleRingDerivedDirectImage q B.target B.source B.identification).map
                ((sZ.normalization.derived a.source b.source).hom.app M))  := by
  obtain ⟨sW⟩ := finiteFreeDirectImageScalarModels W
  obtain ⟨sZ⟩ := finiteFreeDirectImageScalarModels Z
  refine ⟨sW, sZ, ?_, ?_, ?_, ?_, ?_⟩
  · intro R S a
    exact finiteFreeDirectImageScalarShift sW a
  · intro R S a
    exact finiteFreeDirectImageScalarShift sZ a
  · intro R S a d hfree
    have hW := (finiteFreeDirectImageScalarShift sW a.target).1
    have hZ := (finiteFreeDirectImageScalarShift sZ a.source).1
    let := hW
    let := hZ
    have hi (M : DerivedCategory (proEtaleRingModules Z R.source)) :
        IsIso ((comparison sW sZ a).app M) :=
      comparison_isIso_app q sW sZ R S a d hfree M
    exact ⟨NatIso.isIso_of_isIso_app _, finiteFreeDirectImageShift sW sZ a,
      inferInstance, inferInstance⟩
  · exact finiteFreeDirectImageUnit q sW sZ
  · intro R S B a b d e ha hb M
    exact finiteFreeDirectImageTower q sW sZ R S B a b M

set_option maxHeartbeats 800000 in
-- The inlined coordinate construction exceeded 200000 heartbeats at the derived square.
private theorem comparison_isIso_app {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    IsIso ((comparison sW sZ a).app M) := by
  classical
  have hcolumns : ∃ (eW : (⨁ fun _ : Fin d ↦
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≅
        (proEtaleRingRestrictScalars a.target).mapDerivedCategory.obj
          ((sW.presentation a.target).derived.obj
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M)))
      (eZ : (⨁ fun _ : Fin d ↦ M) ≅
        (proEtaleRingRestrictScalars a.source).mapDerivedCategory.obj
          ((sZ.presentation a.source).derived.obj M)),
      ∀ i : Fin d,
        biproduct.ι _ i ≫ eW.hom ≫
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
            ((comparison sW sZ a).app M) ≫
          (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm).hom.app
              ((sZ.presentation a.source).derived.obj M) =
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
          (biproduct.ι _ i ≫ eZ.hom) := by
    let θ := basisPowerIso W R.target d ≪≫ hfree.some.symm
    obtain ⟨θZ, hcoord⟩ := finiteFreeDirectImage_coefficientPullback R S a d θ
    obtain ⟨φW, _, _, hεW, hW⟩ :=
      finiteFreeDirectImage_presentedScalarCoordinates W sW a.target d θ
    obtain ⟨φZ, _, _, hεZ, hZ⟩ := finiteFreeDirectImage_presentedScalarCoordinates Z sZ a.source d
      θZ
    have hordinary (M : proEtaleRingModules W R.target) :
      (proEtaleRingModulePullback q R.target R.source R.identification).map (φW.hom.app M) ≫
        (PreservesProduct.iso (proEtaleRingModulePullback q R.target R.source R.identification)
          (fun _ : Fin d ↦ M)).hom =
      (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).app
          ((sW.presentation a.target).ordinary.obj M) ≫
        (proEtaleRingRestrictScalars a.source).map ((ordinaryBalancing sW sZ a).hom.app M) ≫
        φZ.hom.app ((proEtaleRingModulePullback q R.target R.source R.identification).obj M) := by
      let F := proEtaleRingModulePullback q R.target R.source R.identification
      let adj := proEtaleRingModuleAdjunction q R.target R.source R.identification
      apply limit.hom_ext
      rintro ⟨i⟩
      change (F.map (φW.hom.app M) ≫ (PreservesProduct.iso F (fun _ : Fin d ↦ M)).hom) ≫
          Pi.π (fun _ : Fin d ↦ F.obj M) i = _
      rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, ← F.map_comp]
      apply (adj.homEquiv _ _).injective
      simp only [Adjunction.homEquiv_unit]
      erw [← adj.unit.naturality (φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i)]
      apply presentedTensor_hom_ext W sW a.target d θ
      intro V b m
      change ((adj.unit.app M).val.app V)
          ((φW.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
            (sectionTensor (sW.presentation a.target) M V b m)) =
        (φZ.hom.app (F.obj M) ≫ Pi.π (fun _ : Fin d ↦ F.obj M) i).val.app
          ((proEtaleBaseChange q).op.obj V)
          (((ordinaryBalancing sW sZ a).hom.app M).val.app ((proEtaleBaseChange q).op.obj V)
            (((proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
              a.target a.source R.identification S.identification a.comm).app
                ((sW.presentation a.target).ordinary.obj M)).val.app
                  ((proEtaleBaseChange q).op.obj V)
                    ((adj.unit.app _).val.app V
                      (sectionTensor (sW.presentation a.target) M V b m))))
      erw [hW M V b m i]
      erw [((adj.unit.app M).val.app V).hom.map_smul]
      erw [restrictionPullback_unit R S a ((sW.presentation a.target).ordinary.obj M) V
        (sectionTensor (sW.presentation a.target) M V b m)]
      erw [ordinaryBalancing_pure sW sZ a M V b m]
      erw [hZ (F.obj M) ((proEtaleBaseChange q).op.obj V)
        ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b)
        ((adj.unit.app M).val.app V m) i, hcoord V b i]
      rfl
    let T := (sW.presentation a.target).ordinary
    let T' := (sZ.presentation a.source).ordinary
    let U := proEtaleRingRestrictScalars a.target
    let U' := proEtaleRingRestrictScalars a.source
    let F := proEtaleRingModulePullback q R.target R.source R.identification
    let G := proEtaleRingModulePullback q S.target S.source S.identification
    let E := (sW.presentation a.target).derived
    let E' := (sZ.presentation a.source).derived
    let εh := (sW.presentation a.target).counit
    let εh' := (sZ.presentation a.source).counit
    let (H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ)) :
        IsIso (εh.app H) := hεW H
    let : IsIso εh := NatIso.isIso_of_isIso_app _
    let (H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ)) :
        IsIso (εh'.app H) := hεZ H
    let : IsIso εh' := NatIso.isIso_of_isIso_app _
    let ε : DerivedCategory.Q ⋙ E ⟶
        T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      { app := fun K ↦ εh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
        naturality := by
          intro X Y f
          exact εh.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
    let ε' : DerivedCategory.Q ⋙ E' ⟶
        T'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      { app := fun K ↦ εh'.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
        naturality := by
          intro X Y f
          exact εh'.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
    have : IsIso ε := by
      have (K : CochainComplex (proEtaleRingModules W R.target) ℤ) : IsIso (ε.app K) :=
        inferInstanceAs (IsIso (εh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
      exact NatIso.isIso_of_isIso_app _
    have : IsIso ε' := by
      have (K : CochainComplex (proEtaleRingModules Z R.source) ℤ) : IsIso (ε'.app K) :=
        inferInstanceAs (IsIso (εh'.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
      exact NatIso.isIso_of_isIso_app _
    let χ := ordinaryBalancing sW sZ a
    let := proEtaleRingRestrictionPullbackInv_isIso q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm
    let ρ := asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)
    let Φ := SheafOfModules.RingedTensor.coordinateDescent T U d E ε φW
    let Φ' := SheafOfModules.RingedTensor.coordinateDescent T' U' d E' ε' φZ
    let β := SheafOfModules.RingedTensor.scalarComparisonDescent T F G T' E ε E' ε' χ
    let ρD := Functor.mapDerivedCategoryCompIso U F ≪≫
      Functor.mapDerivedCategoryNatIso ρ ≪≫ (Functor.mapDerivedCategoryCompIso G U').symm
    let τ := Functor.whiskerLeft E ρD.hom ≫
      Functor.whiskerRight β.hom U'.mapDerivedCategory
    have hρD : ρD.hom = (proEtaleRingRestrictionDerivedPullback q R.target S.target
        R.source S.source a.target a.source R.identification S.identification a.comm).inv := by
      simp only [ρD, proEtaleRingRestrictionDerivedPullback,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
      rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq]
    have hsquare (M : proEtaleRingModules W R.target) :
        F.map (φW.hom.app M) ≫ (SheafOfModules.RingedTensor.powerComparison F d).hom.app M =
          ρ.hom.app (T.obj M) ≫ U'.map (χ.hom.app M) ≫ φZ.hom.app (F.obj M) := by
      unfold SheafOfModules.RingedTensor.powerComparison
      exact hordinary M
    have hτ (X : DerivedCategory (proEtaleRingModules W R.target)) :
        F.mapDerivedCategory.map (Φ.hom.app X) ≫
          (SheafOfModules.RingedTensor.powerComparison F.mapDerivedCategory d).hom.app X =
        τ.app X ≫ Φ'.hom.app (F.mapDerivedCategory.obj X) := by
      simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.assoc] using
        SheafOfModules.RingedTensor.derivedCoordinateSquare T U d F G T' U' E ε E' ε' χ
        ρ φW φZ hsquare Φ Φ'
        (SheafOfModules.RingedTensor.coordinateDescent_normalized T U d E ε φW)
        (SheafOfModules.RingedTensor.coordinateDescent_normalized T' U' d E' ε' φZ) X
    let eW (X : DerivedCategory (proEtaleRingModules W R.target)) :=
      biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ.app X).symm
    let eZ (X : DerivedCategory (proEtaleRingModules Z R.source)) :=
      biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ'.app X).symm
    have hβ : BalancingComputed sW sZ a β := by
      have hF (K : CochainComplex (proEtaleRingModules W R.target) ℤ) :
          F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
            F.mapDerivedCategoryFactors.hom.app K := by
        rw [F.mapDerivedCategoryFactorsh_hom_app]
        change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app K ≫
          𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
        erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
        simp only [Category.id_comp]
        exact Category.comp_id _
      have hG (K : CochainComplex (proEtaleRingModules W S.target) ℤ) :
          G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
            G.mapDerivedCategoryFactors.hom.app K := by
        rw [G.mapDerivedCategoryFactorsh_hom_app]
        change G.mapDerivedCategory.map (𝟙 _) ≫ G.mapDerivedCategoryFactors.hom.app K ≫
          𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
        erw [G.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
        simp only [Category.id_comp]
        exact Category.comp_id _
      intro H
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
      rw [hF]
      erw [hG]
      have h := SheafOfModules.RingedTensor.scalarComparisonDescent_normalized T F G T'
        E ε E' ε' χ K
      have hh : DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
            (χ.hom.mapHomotopyCategory (.up ℤ)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) =
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
              (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K) := by
        simp only [Functor.map_comp]
        rfl
      rw [hh]
      exact h
    have heq : β = balancing sW sZ a :=
      finiteFreeDirectImage_balancingComputed sW sZ a β hεZ hβ
    have hnat {X Y : DerivedCategory (proEtaleRingModules Z R.source)} (f : X ⟶ Y)
        (i : Fin d) :
        biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom ≫
            U'.mapDerivedCategory.map (E'.map f) =
          f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫ (eZ Y).hom := by
      simpa only [eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        Functor.comp_map, Category.assoc] using
        coordinateInjection_naturality d (E' ⋙ U'.mapDerivedCategory) Φ' f i
    have hpull (X : DerivedCategory (proEtaleRingModules W R.target)) (i : Fin d) :
        F.mapDerivedCategory.map (biproduct.ι _ i ≫ (eW X).hom) ≫
            (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
              a.target a.source R.identification S.identification a.comm).inv.app (E.obj X) ≫
            U'.mapDerivedCategory.map (β.hom.app X) =
          biproduct.ι _ i ≫ (eZ (F.mapDerivedCategory.obj X)).hom := by
      have h := coordinateInjection_square d F.mapDerivedCategory
        (E ⋙ U.mapDerivedCategory) (E' ⋙ U'.mapDerivedCategory) Φ Φ' τ hτ X i
      simpa only [τ, eW, eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.assoc, hρD] using h
    refine ⟨eW _, eZ M, fun i ↦ ?_⟩
    simpa only [comparison, heq, Category.assoc] using mate_columns
      (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
      (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
      (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm)
      β
      (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm)
      (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
        a.target a.source R.identification S.identification a.comm).2.2
      (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eW X).hom)
      (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom)
      (fun {X Y} f i ↦ by simpa only [Category.assoc] using hnat f i) hpull M i
  obtain ⟨eW, eZ, hcol⟩ := hcolumns
  let G := proEtaleRingDerivedDirectImage q R.target R.source R.identification
  let U := (proEtaleRingRestrictScalars a.target).mapDerivedCategory
  let δ := proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let f := (comparison sW sZ a).app M
  have heq : eW.hom ≫ U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M) =
      (Functor.mapBiproduct G (fun _ : Fin d ↦ M)).inv ≫ G.map eZ.hom := by
    apply biproduct.hom_ext'
    intro i
    simpa only [Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      ← G.map_comp] using hcol i
  have : IsIso (eW.hom ≫ U.map f ≫
      δ.hom.app ((sZ.presentation a.source).derived.obj M)) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M)) :=
    IsIso.of_isIso_comp_left eW.hom _
  have : IsIso (U.map f) := IsIso.of_isIso_comp_right _
    (δ.hom.app ((sZ.presentation a.source).derived.obj M))
  have : U.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.1
  exact isIso_of_reflects_iso f U

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
