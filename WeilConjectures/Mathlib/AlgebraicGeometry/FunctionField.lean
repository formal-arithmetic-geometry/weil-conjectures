/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The generic point as a morphism from the spectrum of the function field

For an integral scheme `X`, `Scheme.functionField` is the stalk of the structure sheaf at the
generic point, and `Scheme.fromSpecStalk` turns a stalk into a morphism from its spectrum.
This file names the composite, the canonical morphism `Spec k(X) ⟶ X`, and shows that for an
integral scheme `X` it is dominant and stays scheme-theoretically dominant after flat base
change: for a flat `U ⟶ X`, functions on `U` are determined by their restriction to the
generic fibre `U ×_X Spec k(X)`. It also shows that the sections of an integral scheme with
integrally closed local rings over a nonempty open form an integrally closed domain
(`AlgebraicGeometry.Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism `Spec k(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme `X`, namely `Scheme.fromSpecStalk` at the generic point. -/
noncomputable abbrev fromSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The sections of an integral scheme with integrally closed local rings over a nonempty open
`U` form an integrally closed domain: an element of the function field which is integral over
`Γ(X, U)` is integral over every local ring at a point of `U`, hence lies in each of them, and
the sections over `U` are exactly the elements of the function field lying in all these local
rings. -/
theorem isIntegrallyClosed_of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  have hinj := X.germToFunctionField_injective U
  have : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
    refine isIntegrallyClosedIn_iff.mpr ⟨hinj, fun {g} hg ↦ ?_⟩
    have H (y : U) : ∃ (V : X.Opens) (hyV : (y : X) ∈ V) (hVU : V ≤ U) (t : Γ(X, V)),
        @Scheme.germToFunctionField X _ V ⟨⟨y, hyV⟩⟩ t = g := by
      obtain ⟨s, hs⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk y)).mp
        (hg.tower_top (A := X.presheaf.stalk y))
      obtain ⟨W, hyW, t, rfl⟩ := X.presheaf.exists_germ_eq s
      have : Nonempty W := ⟨⟨y, hyW⟩⟩
      refine ⟨W ⊓ U, ⟨hyW, y.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
      rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
      exact X.presheaf.germ_res_apply _ _ _ t
    choose V hyV hVU t ht using H
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
      (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV _⟩) t fun i j ↦ by
        obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
          ⟨i, hyV i⟩ ⟨j, hyV j⟩
        have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨z, hz⟩⟩
        apply X.germToFunctionField_injective (V i ⊓ V j)
        exact (X.presheaf.germ_res_apply _ _ _ _).trans
          ((ht i).trans ((ht j).symm.trans (X.presheaf.germ_res_apply _ _ _ _).symm))
    obtain ⟨y⟩ := ‹Nonempty U›
    refine ⟨s, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← ht y, ← hs y]
    exact (X.presheaf.germ_res_apply _ _ _ s).symm
  exact .of_isIntegrallyClosedIn Γ(X, U) X.functionField
variable (X : Scheme.{u}) [IsIntegral X]

/-- The generic point `Spec k(X) ⟶ X` of an integral scheme is dominant: its image contains
the generic point. -/
instance isDominant_fromSpecFunctionField : IsDominant X.fromSpecFunctionField := by
  rw [isDominant_iff, DenseRange]
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← genericPoint_spec X]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨_, X.fromSpecStalk_closedPoint⟩)

/-- For a flat morphism `f : U ⟶ X` to an integral scheme, pulling back functions along the
projection `U ×_X Spec k(X) ⟶ U` from the generic fibre is injective on global sections:
`Spec k(X) ⟶ X` is scheme-theoretically dominant, as a dominant morphism to a reduced
scheme, and this is preserved by the flat base change along `f`. -/
lemma injective_Γ_map_pullback_fst_fromSpecFunctionField {U : Scheme.{u}} (f : U ⟶ X)
    [Flat f] :
    Function.Injective (Scheme.Γ.map (pullback.fst f X.fromSpecFunctionField).op) := by
  have := IsSchemeTheoreticallyDominant.of_isDominant X.fromSpecFunctionField
  have : IsSchemeTheoreticallyDominant (pullback.fst f X.fromSpecFunctionField) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  exact (pullback.fst f X.fromSpecFunctionField).app_injective ⊤

end AlgebraicGeometry.Scheme
