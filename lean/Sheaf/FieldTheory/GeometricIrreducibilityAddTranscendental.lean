/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Sheaf.FieldTheory.GeometricIrreducibilityTranscendental
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Field.ULift
import Sheaf.FieldTheory.GeometricIrreducibilitySeparable

/-!
# Adding a transcendental variable preserves geometric irreducibility

Source: Stacks Project, Algebra, Tag 0G32 (lemma-geometrically-irreducible-add-transcendental)
(blueprint: lem-zl-geometric-irreducibility-add-transcendental).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem geometricallyIrreducible_of_equiv
    {k F : Type u} {k' F' : Type v}
    [Field k] [Field F] [Field k'] [Field F']
    (i : k →+* F) (i' : k' →+* F') (e : k ≃+* k') (f : F ≃+* F')
    (he : ∀ a, f (i a) = i' (e a))
    (h : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom i'))) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom i)) := by
  let := i.toAlgebra
  let := i'.toAlgebra
  apply (geometricallyIrreducible_iff_separableElements_mem k F).mpr
  intro a ha
  have ha' : IsSeparable k' (f a) :=
    ha.of_equiv_equiv e f (RingHom.ext fun b ↦ (he b).symm)
  obtain ⟨b, hb⟩ := (geometricallyIrreducible_iff_separableElements_mem k' F').mp h _ ha'
  refine ⟨e.symm b, f.injective ?_⟩
  change i' b = f a at hb
  change f (i (e.symm b)) = f a
  rw [he, e.apply_symm_apply, hb]

/-- If `L/M` is geometrically irreducible and `x` is transcendental over `L`, then adjoining
`x` to both fields preserves geometric irreducibility.

Source: Stacks Project, Algebra, Tag 0G32 (lemma-geometrically-irreducible-add-transcendental)
(blueprint: lem-zl-geometric-irreducibility-add-transcendental).

Proof:
1. Apply the one-variable specialization of
   `lem-zl-geometric-irreducibility-transcendental` to the geometrically irreducible extension
   `L/M` and the one-element algebraically independent family consisting of `x`.
2. Transcendence of `x` over `L` is exactly algebraic independence of this singleton, and the
   resulting generated fields are `L(x)` and `M(x)`, represented below by their canonical
   intermediate fields in `K` over `M`.
-/
theorem geometricallyIrreducible_adjoin_transcendental
    {M : Type u} {L : Type u} {K : Type v}
    [Field M] [Field L] [Field K]
    [Algebra M L] [Algebra L K] [Algebra M K]
    [IsScalarTower M L K]
    (hLM : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap M L))))
    (x : K) (hx : Transcendental L x) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom
        (IntermediateField.inclusion
          (E := IntermediateField.adjoin M ({x} : Set K))
          (F := (IntermediateField.adjoin L ({x} : Set K)).restrictScalars M)
          (IntermediateField.adjoin_le_iff.mpr (fun y hy => by
            simp only [Set.mem_singleton_iff] at hy
            subst y
            change x ∈ IntermediateField.adjoin L ({x} : Set K)
            apply IntermediateField.subset_adjoin
            simp))).toRingHom)) := by
  -- The finite-family theorem requires an ambient universe containing the base universe.
  let e : K ≃ₐ[L] ULift.{u} K := ULift.algEquiv.symm
  have hx' : Transcendental L (e x) :=
    fun ha ↦ hx ((isAlgebraic_algHom_iff e.toAlgHom e.injective).mp ha)
  have ht : AlgebraicIndependent L (fun _ : Fin 1 ↦ e x) :=
    algebraicIndependent_unique_type_iff.mpr hx'
  have h := (geometricallyIrreducible_transcendental_extension (k := M) (K := L)).1
    hLM (ULift.{u} K) 1 (fun _ ↦ e x) ht
  let i := IntermediateField.inclusion (E := IntermediateField.adjoin M {x})
    (F := (IntermediateField.adjoin L {x}).restrictScalars M)
    (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L {x}))
  let i' := IntermediateField.inclusion (E := IntermediateField.adjoin M {e x})
    (F := (IntermediateField.adjoin L {e x}).restrictScalars M)
    (IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L {e x}))
  have h' : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom i'.toRingHom)) := by
    have hr : Set.range (fun _ : Fin 1 ↦ e x) = {e x} := Set.range_const
    rw [hr] at h
    exact h
  let eM : IntermediateField.adjoin M ({x} : Set K) ≃ₐ[M]
      IntermediateField.adjoin M ({e x} : Set (ULift.{u} K)) :=
    ((IntermediateField.adjoin M {x}).equivMap (e.restrictScalars M).toAlgHom).trans
      (IntermediateField.equivOfEq (by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
        rfl))
  let eL : IntermediateField.adjoin L ({x} : Set K) ≃ₐ[L]
      IntermediateField.adjoin L ({e x} : Set (ULift.{u} K)) :=
    ((IntermediateField.adjoin L {x}).equivMap e.toAlgHom).trans
      (IntermediateField.equivOfEq (by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
        rfl))
  exact geometricallyIrreducible_of_equiv i.toRingHom i'.toRingHom
    eM.toRingEquiv eL.toRingEquiv (fun a ↦ by
      apply Subtype.ext
      rfl) h'

end AlgebraicGeometry
