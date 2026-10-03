/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The generic point as a morphism from the spectrum of the function field

For an integral scheme `X`, `Scheme.functionField` is the stalk of the structure sheaf at the
generic point, and `Scheme.fromSpecStalk` turns a stalk into a morphism from its spectrum.
This file names the composite, the canonical morphism `Spec k(X) ⟶ X`, and shows that the
sections of an integral scheme with integrally closed local rings over a nonempty open form an
integrally closed domain
(`AlgebraicGeometry.Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

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

end AlgebraicGeometry.Scheme
