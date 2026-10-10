/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Convolution products of algebra homomorphisms killing a Hopf ideal

If two algebra homomorphisms out of a Hopf algebra `A` vanish on a Hopf ideal `I`, then so does
their convolution product: both factor through the quotient Hopf algebra `A ⧸ I`, and the
quotient map is a bialgebra homomorphism.

## Blueprint

- `sk-d-geometry`: the points of a closed subgroup scheme `V(I)` of an affine group scheme form a
  subgroup.
-/

@[expose] public section

open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Algebra R B]

namespace Ideal.IsHopfIdeal

/-- The zero ideal is a Hopf ideal. -/
instance bot : (⊥ : Ideal A).IsHopfIdeal R where
  counit_eq_zero x hx := by simp_all
  map_mkQ_comul_eq_zero x hx := by
    rw [Submodule.restrictScalars_mem, Ideal.mem_bot] at hx
    rw [hx, map_zero, map_zero]
  antipode_mem x hx := by simp_all

/-- The convolution product of two algebra homomorphisms vanishing on a Hopf ideal vanishes on
it. (blueprint: `sk-d-geometry`) -/
theorem convMul_apply_eq_zero {I : Ideal A} [I.IsHopfIdeal R] {f g : A →ₐ[R] B}
    (hf : ∀ a ∈ I, f a = 0) (hg : ∀ a ∈ I, g a = 0) {a : A} (ha : a ∈ I) :
    (toConv f * toConv g) a = 0 := by
  let q : A →ₐc[R] A ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hf' : f = (Ideal.Quotient.liftₐ I f hf).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  have hg' : g = (Ideal.Quotient.liftₐ I g hg).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  rw [hf', hg', ← AlgHom.convMul_comp_bialgHom_distrib]
  have : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
  simp [this]

omit [CommRing B] [Algebra R B] in
/-- The supremum of a set of Hopf ideals is a Hopf ideal: the counit, comultiplication and antipode
conditions are additive, and they hold on each ideal of the set. -/
theorem sSup {S : Set (Ideal A)} (hS : ∀ J ∈ S, J.IsHopfIdeal R) :
    (SupSet.sSup S).IsHopfIdeal R := by
  have hind {P : A → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
      (hmem : ∀ J ∈ S, ∀ x ∈ J, P x) {x : A} (hx : x ∈ SupSet.sSup S) : P x := by
    rw [sSup_eq_iSup'] at hx
    exact Submodule.iSup_induction _ (motive := P) hx (fun J x hx ↦ hmem J.1 J.2 x hx) h0 hadd
  have hle (J : Ideal A) (hJ : J ∈ S) :
      J.restrictScalars R ≤ (SupSet.sSup S).restrictScalars R := fun x hx ↦ le_sSup hJ hx
  have : ((SupSet.sSup S).restrictScalars R).IsCoideal := by
    refine (Submodule.isCoideal_iff_comul_mem _).2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · exact hind (P := fun x ↦ Coalgebra.counit (R := R) x = 0) (map_zero _)
        (fun x y hx hy ↦ by simp only [map_add, hx, hy, add_zero])
        (fun J hJ x hx ↦ (hS J hJ).counit_eq_zero hx) hx
    · refine hind (P := fun x ↦ Coalgebra.comul (R := R) x ∈
        LinearMap.range (LinearMap.lTensor A ((SupSet.sSup S).restrictScalars R).subtype) ⊔
          LinearMap.range (LinearMap.rTensor A ((SupSet.sSup S).restrictScalars R).subtype))
        (by simp only [map_zero]; exact zero_mem _)
        (fun x y hx hy ↦ by simp only [map_add]; exact add_mem hx hy) (fun J hJ x hx ↦ ?_) hx
      have := ((Submodule.isCoideal_iff_comul_mem _).1 (hS J hJ).toIsCoideal).2 x hx
      refine SetLike.le_def.1 (sup_le_sup ?_ ?_) this
      · rw [← Submodule.subtype_comp_inclusion _ _ (hle J hJ), LinearMap.lTensor_comp]
        exact LinearMap.range_comp_le_range _ _
      · rw [← Submodule.subtype_comp_inclusion _ _ (hle J hJ), LinearMap.rTensor_comp]
        exact LinearMap.range_comp_le_range _ _
  exact ⟨fun x hx ↦ hind (P := fun x ↦ HopfAlgebra.antipode R x ∈ SupSet.sSup S) (by simp)
    (fun x y hx hy ↦ by simp only [map_add]; exact add_mem hx hy)
    (fun J hJ x hx ↦ le_sSup hJ ((hS J hJ).antipode_mem hx)) hx⟩
end Ideal.IsHopfIdeal
