/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-! Open and closed immersion of the distinguished component.
(blueprint: lem-dl-a1-normal-constant-field-component-marked-immersion).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/--
For the factor selected by the finite tensor decomposition, each affine chart of the
base change is a finite product of fields.  The inclusion of the selected factor is
therefore both a localization at an idempotent and a quotient by the complementary
idempotent.  Its spectrum map is consequently an open immersion and a closed
immersion.  These local morphisms agree on overlaps because the projection equations
`hp` and `hs` identify the chart restrictions with the canonical pullback projections;
covering `U₀` and gluing the chartwise morphism properties yields the asserted
`IsOpenImmersion j ∧ IsClosedImmersion j`.

Source: Stacks Project, fields.tex, Tag 0CKN, and varieties.tex, Tags 054Q and 0C3M.
The affine finite-product and gluing argument is left as this named obligation for the
marked component assembly.
(blueprint: lem-dl-a1-normal-constant-field-component-marked-immersion).
-/
theorem normal_constant_field_component_marked_immersion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left)
    (hη : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z)
    (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u}) (p : C ⟶ U₀.left)
    (s : C ⟶ Spec (CommRingCat.of D.k)) (j : C ⟶ (D.geometricFiber U₀).left)
    (hpb : IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)))
    (hp : j ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p)
    (hs : j ≫ pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s) :
    IsOpenImmersion j ∧ IsClosedImmersion j := by
  sorry
end AlgebraicGeometry
