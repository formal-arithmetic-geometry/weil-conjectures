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

/-! # Constant differences of generic division points -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry

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


/-- Two points in a generic multiplication fibre differ by a unique constant
n-torsion point. Their difference factors through the finite kernel of [n].
The finite-scheme constancy theorem expresses that point as a ground-field
point. Pull it back to the chosen algebraic closure of k. Faithful flatness
of the generic field over k makes constant-point pullback injective, giving
both the n-torsion identity and uniqueness.
Source: the constant-torsion argument in step 2 of the scope counterexample.
(blueprint: lem-sf-elliptic-division-difference) -/
theorem ellipticDivisionDifference
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left]
    (x y : (Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E)
    (hxy : x ≫ (𝟙 E ^ n) = y ≫ (𝟙 E ^ n)) :
    ∃! a : Scheme.specAlgebraicClosure k ⟶ E,
      a ^ n = 1 ∧ y = x * (toUnit ((Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))) ≫
        inv (toUnit (Scheme.specAlgebraicClosure k)) ≫ a) := by
  classical
  let T := (Over.map E.hom).obj
    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))
  let c := toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k))
  have : Epi (toUnit T) := by
    have : Epi (toUnit T).left := by
      change Epi T.hom
      exact field_spec_epi T.hom
    exact Over.epi_of_epi_left _
  have hc : Function.Injective (fun a : Scheme.specAlgebraicClosure k ⟶ E ↦ c ≫ a) :=
    fun a b hab ↦ (cancel_epi c).mp hab
  have : IsFinite (GrpObj.ker (𝟙 E ^ n)).hom :=
    MorphismProperty.of_isPullback
      ((GrpObj.isPullback_kerι (𝟙 E ^ n)).map (Over.forget _))
      (show IsFinite (𝟙 E ^ n).left from inferInstance)
  have hδ : (x⁻¹ * y) ≫ (𝟙 E ^ n) = toUnit _ ≫ η[E] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, inv_mul_cancel]
    rfl
  let d := GrpObj.kerLift (𝟙 E ^ n) (x⁻¹ * y) hδ
  obtain ⟨d₀, hd₀⟩ := finiteSchemeFieldPointsConstant (GrpObj.ker (𝟙 E ^ n)) T.hom d
  change toUnit T ≫ d₀ = d at hd₀
  let a : Scheme.specAlgebraicClosure k ⟶ E :=
    toUnit _ ≫ d₀ ≫ GrpObj.kerι (𝟙 E ^ n)
  have ha : c ≫ a = x⁻¹ * y := by
    change (toUnit T ≫ inv (toUnit (Scheme.specAlgebraicClosure k))) ≫
      (toUnit _ ≫ d₀ ≫ GrpObj.kerι (𝟙 E ^ n)) = _
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hd₀]
    exact GrpObj.kerLift_kerι _ _ _
  have hn : (x⁻¹ * y) ^ n = 1 := by
    simpa only [comp_pow, Category.comp_id, ← Hom.one_def] using hδ
  have han : a ^ n = 1 := by
    apply hc
    change c ≫ a ^ n = c ≫ 1
    rw [comp_pow, MonObj.comp_one, ha, hn]
  have hay : y = x * (c ≫ a) := by rw [ha]; group
  refine ⟨a, ⟨han, hay⟩, ?_⟩
  intro b hb
  apply hc
  apply mul_left_cancel (a := x)
  exact hb.2.symm.trans hay

end AlgebraicGeometry
