/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralReductionTensorStrength
import Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteTensorMonoidal
import all WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Associativity of the normalized reduction tensor strength

Source: Stacks 06YY, 07A4 and 0FPT; integral Hom reduction, paragraphs 1--2.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe d t u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem nativeScalarTensorStrength_transpose
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S) (e : T ≅ tensor C) (X Z : C) :
    F.map ((nativeScalarTensorStrength T S adj mu e).app (X, Z)) ≫
        adj.counit.app (F.obj (X ⊗ Z)) =
      F.map (e.inv.app (X, U.obj (F.obj Z))) ≫
        mu.hom.app (X, U.obj (F.obj Z)) ≫
        S.map (Prod.mkHom (𝟙 (F.obj X)) (adj.counit.app (F.obj Z))) ≫
        mu.inv.app (X, Z) ≫ F.map (e.hom.app (X, Z)) := by
  have h : (nativeScalarTensorStrength T S adj mu e).app (X, Z) =
      adj.homEquiv _ _
        (F.map (e.inv.app (X, U.obj (F.obj Z))) ≫
          mu.hom.app (X, U.obj (F.obj Z)) ≫
          S.map (Prod.mkHom (𝟙 (F.obj X)) (adj.counit.app (F.obj Z))) ≫
          mu.inv.app (X, Z) ≫ F.map (e.hom.app (X, Z))) := by
    dsimp only [nativeScalarTensorStrength, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.prod_obj, Functor.id_obj, Functor.comp_obj]
    rw [scalarTensorStrength_app]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
      ← adj.unit_naturality_assoc]
  rw [h]
  exact (adj.homEquiv _ _).symm_apply_apply _

private theorem tensorMate_assoc {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} {U : D ⥤ C}
    [F.Monoidal] (adj : F ⊣ U)
    (p : ∀ X Z : C, X ⊗ U.obj (F.obj Z) ⟶ U.obj (F.obj (X ⊗ Z)))
    (hp : ∀ X Z : C, F.map (p X Z) ≫ adj.counit.app (F.obj (X ⊗ Z)) =
      Functor.OplaxMonoidal.δ F X (U.obj (F.obj Z)) ≫
        F.obj X ◁ adj.counit.app (F.obj Z) ≫ Functor.LaxMonoidal.μ F X Z)
    (X V Z : C) :
    (α_ X V (U.obj (F.obj Z))).hom ≫ X ◁ p V Z ≫ p X (V ⊗ Z) =
      p (X ⊗ V) Z ≫ U.map (F.map (α_ X V Z).hom) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.counit_naturality, hp X (V ⊗ Z),
    reassoc_of% hp (X ⊗ V) Z]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, hp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc]
  rw [← associator_naturality_right_assoc]
  simp only [Functor.id_obj]
  rw [← Functor.LaxMonoidal.associativity]
  rw [← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Functor.Monoidal.δ_μ,
    id_whiskerRight, Category.id_comp]

private theorem transportedTensorMate_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (T : C × C ⥤ C) (S : D × D ⥤ D) {F : C ⥤ D} {U : D ⥤ C}
    (adj : F ⊣ U) (mu : T ⋙ F ≅ F.prod F ⋙ S)
    (e : T ≅ tensor C) (f : S ≅ tensor D) (core : F.CoreMonoidal)
    (hm : ∀ X Z, (core.μIso X Z).inv = F.map (e.inv.app (X, Z)) ≫
      mu.hom.app (X, Z) ≫ f.hom.app (F.obj X, F.obj Z)) (X V Z : C) :
    let p := nativeScalarTensorStrength T S adj mu e
    X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ (F ⋙ U).map (α_ X V Z).inv =
      (α_ X V ((F ⋙ U).obj Z)).inv ≫ p.app (X ⊗ V, Z) := by
  let := core.toMonoidal
  let mun : tensor C ⋙ F ≅ F.prod F ⋙ tensor D :=
    Functor.isoWhiskerRight e.symm F ≪≫ mu ≪≫ Functor.isoWhiskerLeft (F.prod F) f
  have hiso (A B : C) : (core.μIso A B).symm = mun.app (A, B) := Iso.ext (hm A B)
  have hδ (A B : C) : Functor.OplaxMonoidal.δ F A B =
      F.map (e.inv.app (A, B)) ≫ mu.hom.app (A, B) ≫
        f.hom.app (F.obj A, F.obj B) := hm A B
  have hμ (A B : C) : Functor.LaxMonoidal.μ F A B =
      f.inv.app (F.obj A, F.obj B) ≫ mu.inv.app (A, B) ≫ F.map (e.hom.app (A, B)) := by
    change (core.μIso A B).hom = _
    simpa only [mun, Iso.app_inv, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.prod_obj, Category.assoc] using
      congrArg Iso.inv (hiso A B)
  let p := nativeScalarTensorStrength T S adj mu e
  have hp (A B : C) : F.map (p.app (A, B)) ≫ adj.counit.app (F.obj (A ⊗ B)) =
      Functor.OplaxMonoidal.δ F A (U.obj (F.obj B)) ≫
        F.obj A ◁ adj.counit.app (F.obj B) ≫ Functor.LaxMonoidal.μ F A B := by
    rw [nativeScalarTensorStrength_transpose, hδ, hμ]
    have hn := (f.hom.naturality
      (Prod.mkHom (𝟙 (F.obj A)) (adj.counit.app (F.obj B)))).symm
    dsimp only [tensor_map] at hn
    simp only [id_tensorHom] at hn
    simp only [Category.assoc]
    rw [reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc]
  have h := tensorMate_assoc adj (fun A B ↦ p.app (A, B)) hp X V Z
  change X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ U.map (F.map (α_ X V Z).inv) =
    (α_ X V (U.obj (F.obj Z))).inv ≫ p.app (X ⊗ V, Z)
  apply (cancel_epi (α_ X V (U.obj (F.obj Z))).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp only [← U.map_comp, ← F.map_comp, Iso.hom_inv_id,
    Functor.map_id, Category.comp_id]

end CategoryTheory

namespace WeilConjectures.IntegralHom

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted totalTensor coefficientTotalTensor
  completedIntegralCommRingSheaf integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralDerivedReduction scalarReductionSourceDerived scalarReductionTargetDerived
  integralReductionSourceHasDerivedCategory integralReductionTargetHasDerivedCategory
  coefficientFiniteHasDerived coefficientFiniteDerivedExtension derivedCategory
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nativeIso_representative
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : TensorPresentation.{t, u} Y R)
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat Y R P) (hQ : flat Y R Q) :
    a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        (tensorPresentationNativeIso Y R a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (RingedDerivedNative.comparison.{t + 1, t, u, max u (t + 1) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let i := coefficientKFlatInclusion.{u, t + 1, t} J R
  let L := i ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).inverseImage i
  let := tensorPresentationKFlatLocalization Y R
  let ff := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W)
    (Derived.{t, u} Y R)
  have he := congrArg (fun z ↦ z.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (ff.map_preimage (a.representative.symm ≪≫
      RingedDerivedNative.comparison.{t + 1, t, u, max u (t + 1) + 1} J R).hom)
  change (tensorPresentationNativeIso Y R a).hom.app
    (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  all_goals rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem normalizedBeta_eq (n : ℕ)
    (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
      (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
        (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q))
    [IsIso beta]
    (hbeta : ∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (beta.f (i + j)).val.app U
        (totalPair Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
          i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
            ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
      (reductionUnit l E Y D hl n
        ((((totalTensor Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
          (i + j))).val.app U
        (totalPair Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) :
    (asIso beta).symm = coefficientScalarTensorIso l E Y n P Q := by
  sorry

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem nativeReductionMonoidal
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n) :
    let J := AlgebraicGeometry.Scheme.ProEt.topology Y
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let S := integralCoefficientCommRingSheaf l E Y n
    let : MonoidalCategory (Derived.{t, u} Y R) :=
      RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J R
    let : MonoidalCategory (Derived.{t, u} Y S) :=
      RingedDerivedNative.monoidal.{t + 1, t, u, max u (t + 1) + 1} J S
    let F : Derived.{t, u} Y R ⥤ Derived.{t, u} Y S := by
      with_unfolding_all exact integralDerivedReduction l E Y D hl n
    let e := tensorPresentationNativeIso Y R a
    let f := tensorPresentationNativeIso Y S m.target
    ∃ core : F.CoreMonoidal, ∀ X Z,
      (core.μIso X Z).inv = F.map (e.inv.app (X, Z)) ≫
        m.mu.hom.app (X, Z) ≫ f.hom.app (F.obj X, F.obj Z) := by
  sorry

-- Comparing the fixed localization models requires many definitional equalities.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A native tensor comparison transports the normalized scalar tensor mate to
an associative tensor strength. No invertibility of that mate is asserted here.

Source: Stacks 06YY, 07A4 and 0FPT; integral Hom reduction, paragraphs 1--2.
Proof: choose the unique tensor comparison whose pullback to the product of
K-flat localization functors is a.representative inverse followed by the native
comparison. On three K-flat complexes the normalization field of m identifies
mu with the balanced scalar tensor map. Its associativity is tested on a local
homogeneous generator ((x tensor y) tensor z): both routes insert the same scalar
unit and multiply the two coefficient factors. Sheafification and coproduct
summands detect equality. The native associator square identifies the localized
chain reassociation with the derived associator. Transposing by the normalized
scalar adjunction gives the displayed strength associativity. Resolve the
restricted scalar extension in its occurrence as a tensor input, cancel the
quasi-isomorphisms by K-flatness, and descend the equality through the product
localization. Naturality then extends the equation to arbitrary derived inputs.
All coefficient and site universes remain independent; zero rings and empty
sites satisfy the same generator equations.
(blueprint: lem-sf-reduction-tensor-strength-associativity). -/
theorem reductionTensorStrength_associativity
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    letI : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) := by
      with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
        max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
    let e : a.tensor ≅ tensor (completedIntegralDerivedCategory l E Y D hl) := by
      with_unfolding_all exact tensorPresentationNativeIso Y R a
    let B := integralDerivedReduction l E Y D hl n ⋙ scalarReductionDerivedRestriction l E Y n
    let p := nativeScalarTensorStrength
      (C := completedIntegralDerivedCategory l E Y D hl) a.tensor m.target.tensor
      (derivedScalarExtensionRestrictionAdjunction l E Y n).choose m.mu e
    ∀ X V Z : completedIntegralDerivedCategory l E Y D hl,
      X ◁ p.app (V, Z) ≫ p.app (X, V ⊗ Z) ≫ B.map (α_ X V Z).inv =
        (α_ X V (B.obj Z)).inv ≫ p.app (X ⊗ V, Z) := by
  let R := completedIntegralCommRingSheaf l E Y D hl
  let S := integralCoefficientCommRingSheaf l E Y n
  let : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) := by
    with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
      max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
  let : MonoidalCategory
      (DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n))) := by
    with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
      max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) S
  let e : a.tensor ≅ tensor (completedIntegralDerivedCategory l E Y D hl) := by
    with_unfolding_all exact tensorPresentationNativeIso Y R a
  let f := tensorPresentationNativeIso Y S m.target
  obtain ⟨core, hcore⟩ := nativeReductionMonoidal l E Y D hl a n m
  exact (CategoryTheory.transportedTensorMate_assoc
    (C := completedIntegralDerivedCategory l E Y D hl)
    (D := DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)))
    a.tensor m.target.tensor
    (derivedScalarExtensionRestrictionAdjunction l E Y n).choose m.mu e f core hcore)

end WeilConjectures.IntegralHom
