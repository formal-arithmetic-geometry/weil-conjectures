/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleComplexPullbackTransport

/-! # Coherence of termwise pullbacks over a cone

Source: Stacks Project, Tag 0GIT, proof, and inverse-image composition coherence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true

/-- Termwise comparisons satisfy the unit, associativity, and cone transition laws.
Source: Stacks Project, Tag 0GIT, proof, termwise pullbacks, expanded using the
inverse-image composition and identity comparisons.
(blueprint: lem-weil-pbc-etale-complex-pullback-coherence)

Proof: evaluate inverse-image unit and associativity at each degree of C. The
inverse of the composition comparison defines phi. The left unit law, together
with D.map_id and the naturality of t at the identity, gives the first equality.
For composable f and g, apply the associativity law to D.map g, D.map f, and
 t.app i. Substitute D.map_comp and naturality of t; cancel the outer composition
comparison to get the second equality. For the final equality apply associativity
to c.π.app j, D.map f, and t.app i. Substitute the cone equation c.w f, the
naturality of t, and hp. Cancel the composition comparison for c.π.app j and
 t.app j. The composite displayed then equals the identity on p inverse image C.
Equality of complex maps follows from equality in every degree. These arguments
also apply to identity arrows and to a constant diagram; no cofilteredness or
universal property of the cone is needed. -/
theorem presentation_pullback_coherence
    {I : Type u} [SmallCategory I] (T : Scheme.{u})
    (D : I ⥤ Scheme.{u}) (c : Cone D) (t : D ⟶ (Functor.const I).obj T)
    (p : c.pt ⟶ T) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    let F := fun i : I =>
      ((upperStar AddCommGrpCat.{u + 1} (t.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C
    let φ := fun {i j : I} (f : j ⟶ i) =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm))
        (ComplexShape.up ℤ)).inv.app C
    let eG := fun i : I =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p (hp i).symm)
        (ComplexShape.up ℤ)).app C
    (∀ i : I, φ (𝟙 i) = presentationIdentityMap D i (F i)) ∧
    (∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : j ⟶ i), ((Functor.const Iᵒᵖ).obj
      (((upperStar AddCommGrpCat.{u + 1} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)).map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv) := by sorry


end AlgebraicGeometry.Etale
