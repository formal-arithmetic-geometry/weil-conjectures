/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Finite-term presentations on arbitrary affine schemes

Source: Stacks Project, Tag 08EB, transported by the canonical affine isomorphism
(blueprint: lem-pc-perfect-affine-finite-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Termwise associated sheaf followed by pushforward along the canonical affine isomorphism.
This is an explicit construction on complexes, before passage to the derived category.
Source: Stacks Project, Tag 08EB (blueprint: lem-pc-perfect-affine-finite-presentation). -/
noncomputable def affineModuleComplexFunctor (Y : Scheme.{u}) [IsAffine Y] :
    CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ :=
  @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} Γ(Y, ⊤))
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
    (tilde.functor Γ(Y, ⊤) ⋙ SheafOfModules.pushforward Y.isoSpec.inv.toRingCatSheafHom)
    ⟨fun _ _ ↦ by
      change (SheafOfModules.pushforward _).map (tilde.map 0) = 0
      rw [tilde.map_zero]
      rfl⟩ (ComplexShape.up ℤ)

/-- Every perfect quasi-coherent derived object on an affine scheme has a finite-term module
complex presentation under the explicit associated-sheaf functor.
Source: Stacks Project, Tag 08EB; Step 1 of lem-pc-perfect-affine-classes-small
(blueprint: lem-pc-perfect-affine-finite-presentation).

Proof: Put A = Γ(Y, O_Y) and use Y.isoSpec : Y ≅ Spec A. Pushforward along the
isomorphism and its inverse are exact mutually inverse functors on module sheaves;
their termwise extensions therefore invert quasi-isomorphisms and give mutually inverse
functors on derived categories. Quasi-coherence is preserved by these functors, as can
be checked on the corresponding affine opens. Perfectness is preserved too: transport
the covering in IsPerfect along the isomorphism, and transport each strictly perfect
complex. The finite free objects and their retraction maps are preserved, as are the
zero terms and the degree bounds. Apply perfect_iff_affine_bounded_projective to the
transported object on Spec A. This produces a bounded finite projective complex P and
an isomorphism with its termwise associated sheaf. Apply the inverse exact functor to
this isomorphism and use the derived counit. Its image is precisely the localization
of affineModuleComplexFunctor Y applied to P. Retain finiteness of its terms and forget
boundedness and projectivity, which are unnecessary for the smallness argument.
The zero ring and zero complex require no separate hypothesis. -/
theorem exists_affine_finite_module_presentation (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory Y) (hE : IsPerfect Y E.obj) :
    ∃ P : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ,
      (∀ n : ℤ, Module.Finite Γ(Y, ⊤) (P.X n)) ∧
      Nonempty (E.obj ≅ DerivedCategory.Q.obj ((affineModuleComplexFunctor Y).obj P)) := by
  sorry

end AlgebraicGeometry.Scheme
