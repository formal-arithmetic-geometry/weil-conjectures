/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClass

/-! # Generation of affine conormal sections by the difference derivation

## References

* Stacks Project, Tags 08S2, 01KJ, 01R3 and 00RW
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The values of a normalized difference derivation generate affine conormal sections
(Stacks, Tags 08S2, 01R3 and 00RW). -/
theorem diagonalConormal_affine_derivation_span (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D) :
    Submodule.span Γ(X, U.1) (Set.range (fun a : Γ(X, U.1) ↦
      D.d (X := op U.1) a)) = ⊤ :=
  open CategoryTheory.Limits in
  open scoped TensorProduct in
  by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
  have hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W := by
    simp only [W, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]
    exact le_rfl
  obtain ⟨r, q, hq, hr₂, hr₁, hclass⟩ := diagonalConormal_affine_ideal_class f U V hUV
  let t (a : Γ(X, U.1)) : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) :=
    ⟨(1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a - a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1)),
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal Γ(S, V.1) a⟩
  have hqt (a : Γ(X, U.1)) : q (t a) = D.d (X := op U.1) a := by
    obtain ⟨s, hs, hqs⟩ := hclass hδ (t a)
    have hs' : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s =
          (pullback.snd f f).appLE U.1 W inf_le_right a -
            (pullback.fst f f).appLE U.1 W inf_le_left a := by
      rw [hs]
      change r (_ - _) = _
      rw [map_sub, hr₂, hr₁]
    exact hqs.trans (hD U.1 W inf_le_left inf_le_right hδ a s hs').symm
  have ht : Submodule.span Γ(X, U.1) (Set.range t) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff
      ((KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1)).restrictScalars Γ(X, U.1))
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal Γ(S, V.1))).mpr
        (KaehlerDifferential.submodule_span_range_eq_ideal Γ(S, V.1) Γ(X, U.1))
  have hrange : q '' Set.range t =
      Set.range (fun a : Γ(X, U.1) ↦ D.d (X := op U.1) a) := by
    rw [← Set.range_comp]
    congr 1
    funext a
    exact hqt a
  rw [← hrange]
  calc
    Submodule.span Γ(X, U.1) (q '' Set.range t) =
        (Submodule.span Γ(X, U.1) (Set.range t)).map q :=
      (Submodule.map_span q (Set.range t)).symm
    _ = ⊤ := by
      rw [ht]
      exact (Submodule.map_top q).trans (LinearMap.range_eq_top.mpr hq)

end AlgebraicGeometry
