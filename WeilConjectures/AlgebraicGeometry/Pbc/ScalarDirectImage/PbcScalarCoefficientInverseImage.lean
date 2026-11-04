/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualPullProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # The completed scalar inclusion commutes with coefficient inverse image

Source: blueprint proper base change, order 1307; Milne, Section 19.
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteCoefficientMap_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y q) ≫ completedFiniteCoefficientMap g dB n =
      completedFiniteCoefficientMap g dA n ≫ AdicCoefficients.coefficientMap X q := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hinv : AdicCoefficients.coefficientMap Y q ≫
      (pbcLevelConstantComparison Y dB n).inv =
    (pbcLevelConstantComparison Y dA n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) := by
    apply (Iso.eq_inv_comp _).2
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq _).2
    exact (scalarLevelConstantComparison_naturality Y dA dB n q).symm
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = _
  rw [← L.map_comp_assoc, hinv, L.map_comp, Category.assoc]
  erw [reassoc_of% (proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom q))]
  simp only [Category.assoc]
  rw [scalarLevelConstantComparison_naturality]

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed scalar inclusion commutes with the inverse-image coefficient isomorphisms.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: apply every finite target projection; both paths become the inverse image of a
residue map followed by the finite coefficient comparison, and these commute. -/
theorem pbcScalarCoefficientMap_inverseImage :
    (pbcActualCoefficientIso g (pbcIntegralDatum l E)).hom ≫ pbcScalarCoefficientMap l E F i X =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcScalarCoefficientMap l E F i Y) ≫
        (pbcActualCoefficientIso g (pbcIntegralDatum l F)).hom := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  change completedCoefficientMap g dE ≫ c X = L.map (c Y) ≫ completedCoefficientMap g dF
  symm
  apply limit.hom_ext
  intro n
  change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
      pbcAdicProjection X dF n.unop =
    (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
  simp only [Category.assoc, hc]
  rw [coefficientMap_projection]
  rw [← Category.assoc (completedCoefficientMap g dE), coefficientMap_projection]
  rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
    (finiteCoefficientMap_naturality g dE dF n.unop
      (pbcScalarQuotientMap l E F i n.unop))

end AlgebraicGeometry.Scheme
