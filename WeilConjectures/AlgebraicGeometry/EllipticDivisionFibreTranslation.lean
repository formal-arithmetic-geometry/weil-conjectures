/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
import WeilConjectures.AlgebraicGeometry.FiniteSchemeFieldPointsConstant

/-! # Detection of translations in a single elliptic division fibre -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry

private theorem finite_division_fixed {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] (E : Over (Spec (.of k))) [GrpObj E] [IsCommMonObj E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left]
    (g : Spec (.of L) ⟶ Spec (.of k))
    (x y : Over.mk g ⟶ E) (hxy : x ≫ (𝟙 E ^ n) = y ≫ (𝟙 E ^ n))
    (σ : Over.mk g ⟶ Over.mk g) (hy : σ ≫ y = y) : σ ≫ x = x := by
  have : IsFinite (GrpObj.ker (𝟙 E ^ n)).hom :=
    MorphismProperty.of_isPullback
      ((GrpObj.isPullback_kerι (𝟙 E ^ n)).map (Over.forget _))
      (show IsFinite (𝟙 E ^ n).left from inferInstance)
  have hδ : (x * y⁻¹) ≫ (𝟙 E ^ n) = toUnit _ ≫ η[E] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    rfl
  let d := GrpObj.kerLift (𝟙 E ^ n) (x * y⁻¹) hδ
  obtain ⟨d₀, hd₀⟩ := finiteSchemeFieldPointsConstant (GrpObj.ker (𝟙 E ^ n)) g d
  have hd : σ ≫ d = d := by rw [← hd₀, comp_toUnit_assoc]
  have h := congrArg (fun z ↦ z ≫ GrpObj.kerι (𝟙 E ^ n)) hd
  dsimp only [d] at h
  rw [Category.assoc, GrpObj.kerLift_kerι,
    MonObj.comp_mul, GrpObj.comp_inv, hy] at h
  exact mul_right_cancel h


private theorem field_spec_epi {k L : Type u} [Field k] [Field L]
    (g : Spec (.of L) ⟶ Spec (.of k)) : Epi g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  let : Algebra k L := φ.hom.toAlgebra
  have h : Flat (Spec.map φ) ∧ Surjective (Spec.map φ) :=
    (flat_and_surjective_SpecMap_iff φ).mpr (by
      change (algebraMap k L).FaithfullyFlat
      exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have := h.1
  have := h.2
  exact Flat.epi_of_flat_of_surjective _


/-- A Galois automorphism fixing one point of a generic multiplication fibre cannot
translate another point of that fibre by a nonidentity constant point.

The quotient x*y^(-1) is n-torsion, since [n]x=[n]y. Lift it through the
kernel scheme E[n]. The kernel is finite etale over the algebraically closed
field k, so all its points over a field extension are constant k-points. This
is proved directly on coordinate rings: the image of the finite algebra is
integral over k, so its map to the field factors through k.
Consequently sigma fixes x*y^(-1). Since it fixes y, it also fixes x.
Cancel x in the translation identity; then descend equality of the two
constant points along the field extension from k to the separable generic
field. The translation point a must be the identity.

Source: the last paragraph of the counterexample in
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-elliptic-division-fibre-translation) -/
theorem ellipticDivisionFibreTranslation
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left] [Etale (𝟙 E ^ n).left]
    (x y : (Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E)
    (hx : x ≫ (𝟙 E ^ n) = Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl)
    (hy : y ≫ (𝟙 E ^ n) = Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl)
    (σ : SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
      SeparableClosure E.left.functionField)
    (a : Scheme.specAlgebraicClosure k ⟶ E)
    (hσx : (Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
        (Scheme.ProEt.genericPointSepAut E.left σ)) ≫ x =
      x * (toUnit ((Over.map E.hom).obj
        ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))) ≫
          inv (toUnit (Scheme.specAlgebraicClosure k)) ≫ a))
    (hσy : (Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
      (Scheme.ProEt.genericPointSepAut E.left σ)) ≫ y = y) : a = 1 := by
  let T := (Over.map E.hom).obj
    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))
  let σT : T ⟶ T := (Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
    (Scheme.ProEt.genericPointSepAut E.left σ))
  have hxfix : σT ≫ x = x :=
    finite_division_fixed E n T.hom x y (hx.trans hy.symm) σT hσy
  have hc : toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k)) ≫ a = 1 := by
    apply mul_left_cancel (a := x)
    rw [_root_.mul_one]
    exact hσx.symm.trans hxfix
  have : Epi (toUnit T) := by
    have : Epi (toUnit T).left := by
      change Epi T.hom
      exact field_spec_epi T.hom
    exact Over.epi_of_epi_left _
  apply (cancel_epi (toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k)))).mp
  simpa only [Category.assoc, MonObj.comp_one] using hc

end AlgebraicGeometry
