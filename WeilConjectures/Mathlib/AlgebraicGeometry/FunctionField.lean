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

/-!
# The generic point as a morphism from the spectrum of the function field

For an integral scheme `X`, `Scheme.functionField` is the stalk of the structure sheaf at the
generic point, and `Scheme.fromSpecStalk` turns a stalk into a morphism from its spectrum.
This file names the composite, the canonical morphism `Spec k(X) ⟶ X`, and shows that for an
integral scheme `X` it is dominant and stays scheme-theoretically dominant after flat base
change: for a flat `U ⟶ X`, functions on `U` are determined by their restriction to the
generic fibre `U ×_X Spec k(X)`.
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
