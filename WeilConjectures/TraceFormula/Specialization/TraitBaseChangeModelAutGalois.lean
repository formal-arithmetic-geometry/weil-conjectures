/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup

/-!

# Generic automorphisms as field automorphisms

A generic automorphism `τ` of `Spec Ω_K` (`NearbyCyclesModel.GenericAut`) is `Spec` of a ring
automorphism of `Ω_K`. This gives an injective group homomorphism from the group of generic
automorphisms to the ring automorphisms of `Ω_K`
(`NearbyCyclesModel.GenericAut.toRingAut`), through which the group inherits the Krull topology
of the Galois group `Gal(Ω_K / Frac K⟦t⟧ · Ω)`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The ring automorphism of `Ω_K` underlying a generic automorphism. -/
noncomputable def toRingEquiv (σ : GenericAut k' K) :
    traitGenericField K ≃+* traitGenericField K where
  toFun := (Spec.preimage σ.τ).hom
  invFun := (Spec.preimage (inv σ.τ)).hom
  left_inv x := by
    rw [← CommRingCat.comp_apply, ← Spec.preimage_comp, IsIso.inv_hom_id, Spec.preimage_id]
    rfl
  right_inv x := by
    rw [← CommRingCat.comp_apply, ← Spec.preimage_comp, IsIso.hom_inv_id, Spec.preimage_id]
    rfl
  map_mul' := map_mul _
  map_add' := map_add _

/-- Generic automorphisms act on `Ω_K` by ring automorphisms: a group homomorphism. -/
noncomputable def toRingAut : GenericAut k' K →* RingAut (traitGenericField K) where
  toFun := toRingEquiv
  map_one' := by
    ext x
    change (Spec.preimage (𝟙 (Spec (.of (traitGenericField K))))).hom x = x
    rw [Spec.preimage_id]
    rfl
  map_mul' σ τ := by
    ext x
    change (Spec.preimage (σ.τ ≫ τ.τ)).hom x = (Spec.preimage σ.τ).hom ((Spec.preimage τ.τ).hom x)
    rw [Spec.preimage_comp]
    rfl

lemma toRingAut_injective : Function.Injective (toRingAut (k' := k') (K := K)) := by
  intro σ τ h
  refine ext ?_
  rw [← Spec.map_preimage σ.τ, ← Spec.map_preimage τ.τ]
  congr 1
  ext x
  exact RingEquiv.congr_fun h x

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
