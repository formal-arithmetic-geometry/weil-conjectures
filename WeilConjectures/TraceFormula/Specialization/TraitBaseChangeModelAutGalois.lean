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

/-- Generic automorphisms are determined by their action on `Ω_K`. -/
lemma toRingAut_injective : Function.Injective (toRingAut (k' := k') (K := K)) := by
  intro σ τ h
  refine ext ?_
  rw [← Spec.map_preimage σ.τ, ← Spec.map_preimage τ.τ]
  congr 1
  ext x
  exact RingEquiv.congr_fun h x

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- A generic automorphism fixes the image of `K⟦t⟧` in `Ω_K`. -/
lemma toRingAut_algebraMap (σ : GenericAut k' K) (a : PowerSeries K) :
    toRingAut σ (algebraMap (PowerSeries K) (traitGenericField K) a) =
      algebraMap (PowerSeries K) (traitGenericField K) a := by
  have h := congrArg Spec.preimage σ.over_trait
  rw [traitGenericPoint, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg (fun f ↦ f.hom a) h

/-- A generic automorphism fixes the image of `Ω` in `Ω_K`. -/
lemma toRingAut_traitGenericFieldMap (σ : GenericAut k' K) (y : traitGenericField k') :
    toRingAut σ (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
  have h := congrArg Spec.preimage σ.over_base
  rw [traitGenericPointMap, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg (fun f ↦ f.hom y) h

/-- A generic automorphism fixes the field of fractions `Frac K⟦t⟧` inside `Ω_K`. -/
lemma toRingAut_algebraMap_fractionRing (σ : GenericAut k' K)
    (a : FractionRing (PowerSeries K)) :
    toRingAut σ (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K) a) =
      algebraMap (FractionRing (PowerSeries K)) (traitGenericField K) a := by
  have := congrArg (fun f : FractionRing (PowerSeries K) →+* traitGenericField K ↦ f a)
    (IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries K))
      (j := ((toRingAut σ : traitGenericField K ≃+* _) : traitGenericField K →+* _).comp
        (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)))
      (k := algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)) (by
        ext b
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply, toRingAut_algebraMap]))
  exact this

/-- A generic automorphism as an automorphism of `Ω_K` over `Frac K⟦t⟧`, an element of the
absolute Galois group of `Frac K⟦t⟧` (with its Krull topology). -/
noncomputable def toAlgEquiv : GenericAut k' K →*
    (traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := toRingAut σ) (toRingAut_algebraMap_fractionRing σ)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Generic automorphisms are determined by their action on `Ω_K`. -/
lemma toAlgEquiv_injective : Function.Injective (toAlgEquiv (k' := k') (K := K)) :=
  fun _ _ h ↦ toRingAut_injective (RingEquiv.ext fun x ↦ AlgEquiv.congr_fun h x)

/-- An automorphism of `Ω_K` over `Frac K⟦t⟧` fixing the image of `Ω` is a generic
automorphism. -/
noncomputable def ofAlgEquiv
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)
    (he : ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y) :
    GenericAut k' K where
  τ := Spec.map (CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K))
  isIso := by
    have : IsIso (CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K)) :=
      ⟨CommRingCat.ofHom (e.symm : traitGenericField K →+* traitGenericField K),
        by ext; simp, by ext; simp⟩
    infer_instance
  over_trait := by
    rw [traitGenericPoint, ← Spec.map_comp]
    congr 1
    ext a
    change e (algebraMap (PowerSeries K) (traitGenericField K) a) = _
    rw [IsScalarTower.algebraMap_apply (PowerSeries K) (FractionRing (PowerSeries K)),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rfl
  over_base := by
    rw [traitGenericPointMap, ← Spec.map_comp]
    congr 1
    ext y
    exact he y

lemma toAlgEquiv_ofAlgEquiv
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K)
    (he : ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y) :
    toAlgEquiv (ofAlgEquiv e he) = e := by
  refine AlgEquiv.ext fun x ↦ ?_
  have h : Spec.preimage (ofAlgEquiv e he).τ =
      CommRingCat.ofHom (e : traitGenericField K →+* traitGenericField K) :=
    Spec.preimage_map _
  exact congrArg (fun f ↦ f.hom x) h

/-- **The generic automorphisms are the Galois group `P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)`**: the
range of `toAlgEquiv` is the subgroup of the absolute Galois group of `Frac K⟦t⟧` fixing the
image of `Ω`. -/
lemma mem_range_toAlgEquiv_iff
    (e : traitGenericField K ≃ₐ[FractionRing (PowerSeries K)] traitGenericField K) :
    e ∈ (toAlgEquiv (k' := k') (K := K)).range ↔
      ∀ y, e (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
  refine ⟨?_, fun he ↦ ⟨ofAlgEquiv e he, toAlgEquiv_ofAlgEquiv e he⟩⟩
  rintro ⟨σ, rfl⟩ y
  exact toRingAut_traitGenericFieldMap σ y

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
