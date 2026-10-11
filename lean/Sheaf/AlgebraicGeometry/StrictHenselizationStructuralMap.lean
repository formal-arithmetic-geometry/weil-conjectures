/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Sheaf.AlgebraicGeometry.StrictHenselization

/-!
# The structural morphism of the strict henselization

The strict henselization `S_(s)` of a scheme `S` at a geometric point `s` maps to `S` through
every affine pointed étale neighbourhood; this module names that canonical morphism.

Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- There is a morphism `S_(s) ⟶ S` equal, for every representative affine pointed
neighbourhood `(V, v)`, to the limit leg `S_(s) ⟶ Spec Γ(V, ⊤)`, followed by the
identification `Spec Γ(V, ⊤) ≅ V` and the structure morphism `V ⟶ S`.
Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).

Proof: the representative category is cofiltered (`strictHenselization_properties`), hence
nonempty and connected. The legs of `strictHenselizationCone s` commute with the transition
maps, which are pointed morphisms over `S`, so the composites with the structure morphisms
agree along every arrow, hence for every pair of objects; take their common value. -/
theorem exists_strictHenselizationStructuralMap
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ ρ : strictHenselizationScheme s ⟶ S,
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
            Spec.map (ΓSpecIso
              (((equivSmallModel.{u}
                (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
            ((AffineEtale.Spec S).obj
              (((equivSmallModel.{u}
                (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
          ρ := by
  sorry

/-- The structural morphism `S_(s) ⟶ S` of the strict henselization at a geometric point:
the common composite of the limit legs with the neighbourhood structure morphisms,
characterized by `exists_strictHenselizationStructuralMap`.
Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map). -/
noncomputable def strictHenselizationStructuralMap
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : strictHenselizationScheme s ⟶ S :=
  Classical.choose (exists_strictHenselizationStructuralMap s)

end AlgebraicGeometry.Scheme
