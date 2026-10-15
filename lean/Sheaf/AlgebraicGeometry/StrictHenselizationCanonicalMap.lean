/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.Paper.StrictHenselizationPointEvaluation

/-! # The canonical pointed strict-local morphism

Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
The existing residue-field formulation is retained; this interface packages its uniquely
characterized map without requiring the caller to supply residue identifications.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The unique pointed map over the original morphism.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof: apply strictHenselizationResidue to obtain the local structures and the uniquely
pointed residue identifications. Use strictHenselizationFunctoriality with these
identifications and the residue embeddings furnished by the geometric points.
Its local homomorphism gives the required spectrum map. Evaluation is the compatible
geometric-point cocone, so its residue equation is exactly the second displayed equation.
Conversely a pointed map maps the closed point to the closed point and is local.
The residue equation and the uniqueness clause of functoriality give uniqueness. -/
theorem strictHenselizationMap_existsUnique
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : strictHenselizationScheme x ⟶ strictHenselizationScheme (x ≫ f),
      h ≫ strictHenselizationStructuralMap (x ≫ f) =
        strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation (x ≫ f))) := by
  sorry

/-- The map determined uniquely by functoriality, not a choice from mere existence.
Source: Stacks Project, Tags 04HX and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality). -/
noncomputable def strictHenselizationMap
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    strictHenselizationScheme x ⟶ strictHenselizationScheme (x ≫ f) :=
  Classical.choose (strictHenselizationMap_existsUnique f x)

/-- The defining structural square of the canonical map.
Source: Stacks Project, Tags 04HX and 04GU
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof: take the structural-square component of the property of the unique witness in
strictHenselizationMap_existsUnique. -/
theorem strictHenselizationMap_over
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    strictHenselizationMap f x ≫ strictHenselizationStructuralMap (x ≫ f) =
      strictHenselizationStructuralMap x ≫ f := by
  sorry

end AlgebraicGeometry.Scheme
