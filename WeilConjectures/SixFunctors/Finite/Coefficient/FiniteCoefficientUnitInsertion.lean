/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion

/-! # Adjunction formula for normalized regular scalar units

Source: the regular-unit quotient compatibility in
lem-coef-integral-finite-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory

namespace WeilConjectures

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

-- Use abstract categories to share the monoidal data in the normalization equation.
private theorem normalized_unit_hom
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _)
    (hn : Etale.ExceptionalCoefficients.UnitNormalizationAux F E rep e) :
    e.hom = rep (𝟙_ _) ≫ _root_.DerivedCategory.Q.map
      (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) := by
  have hεC : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C)) = 𝟙 _ := by
    change ((𝟙 _ ≫ (_root_.DerivedCategory.Qh (C := C)).map
      (𝟙 (𝟙_ (HomotopyCategory C (.up ℤ))))) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
    exact (_root_.DerivedCategory.Qh (C := C)).map_id _
  have hεD : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D)) = 𝟙 _ := by
    change ((𝟙 _ ≫ (_root_.DerivedCategory.Qh (C := D)).map
      (𝟙 (𝟙_ (HomotopyCategory D (.up ℤ))))) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
    exact (_root_.DerivedCategory.Qh (C := D)).map_id _
  change E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map
        (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
      e.hom ≫ Functor.LaxMonoidal.ε _root_.DerivedCategory.Q at hn
  rw [hεC, hεD, E.map_id, Category.id_comp, Category.comp_id] at hn
  exact hn.symm

-- Keep the representative formula uniform in the complex; specialize to the unit here.
private theorem unit_eq_insertion_aux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (U : D ⥤ C) [U.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    (a : F ⊣ U) (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (ad : E ⊣ U.mapDerivedCategory)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _)
    (hn : Etale.ExceptionalCoefficients.UnitNormalizationAux F E rep e)
    (hrep : ∀ P : CochainComplex C ℤ, rep P = (ad.homEquiv _ _).symm
      (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ U)) (.up ℤ)).inv.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (η : 𝟙_ C ⟶ U.obj (𝟙_ D))
    (hη : a.homEquiv _ _ (Functor.OplaxMonoidal.η F) = η) :
    e.hom = SheafExactDegreeZero.adjointInsertion U ad η := by
  have hc := Etale.FiniteSmoothPurity.scalarSingleMap_cochain F U a E ad (𝟙_ C)
  change E.map (𝟙 _) ≫ _ ≫ _ ≫ 𝟙 _ = _ at hc
  rw [E.map_id, Category.id_comp, Category.comp_id] at hc
  rw [normalized_unit_hom F E rep e hn,
    Functor.OplaxMonoidal.mapHomologicalComplexη, _root_.DerivedCategory.Q.map_comp,
    ← Category.assoc, hrep]
  erw [hc]
  have hi := Etale.FiniteSmoothPurity.single_insertion_abstract F U a ad
    (𝟙_ C) (𝟙_ D) (Functor.OplaxMonoidal.η F)
  rw [hη] at hi
  exact hi

/-- The normalized derived scalar unit is the exact adjunction insertion of the
ordinary restriction lax unit.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, regular-unit quotient compatibility.
(blueprint: lem-sf-finite-coefficient-unit-insertion)

Proof: expand the representative normalization; both localization unit comparisons
are identities. On the regular sheaf in degree zero, scalarSingleMap_cochain
identifies the representative followed by the complex-single comparison with the
ordinary-to-derived adjunction comparison. Naturality of the adjunction moves the
ordinary oplax unit through this comparison. Its ordinary adjunct is the restriction
lax unit by the definition of the sheafified left-adjoint oplax structure. This proves
the claimed insertion formula without finiteness or flatness assumptions. -/
theorem finiteCoefficient_unit_eq_scalarInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) :
    (Etale.ExceptionalCoefficients.unitIso φ S).hom =
      SheafExactDegreeZero.scalarAdjointInsertion S.smallEtaleTopology φ
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars S.smallEtaleTopology φ)) := by
  let F := ProEtale.etaleSheafExtendScalars φ S
  let U := Sheaf.restrictScalars S.smallEtaleTopology φ
  let L := Etale.scalarExtension φ S
  let a := ProEtale.etaleSheafExtendScalarsAdjunction φ S
  let ad : L ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  unfold SheafExactDegreeZero.scalarAdjointInsertion
  refine unit_eq_insertion_aux F U a L ad (Etale.scalarExtensionRepresentative φ S)
    (Etale.ExceptionalCoefficients.unitIso φ S)
    (Etale.ExceptionalCoefficients.unitIso_existsUnique φ S).choose_spec.1 (fun _ => rfl)
    (Functor.LaxMonoidal.ε U) ?_
  change (a.homEquiv _ _) ((a.homEquiv _ _).symm
    (Functor.LaxMonoidal.ε U)) = _
  exact Equiv.apply_symm_apply _ _

end WeilConjectures
