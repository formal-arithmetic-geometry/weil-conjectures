/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Projective

/-! # Sheafifying a finite-projective comparison with affine sections

Source: Stacks Project, Tags 01IB and 08EB.
(blueprint: lem-pc-affine-projective-sections-sheafification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sheafification of a ring quasi-isomorphism to the sections of a quasi-coherent
complex supplies a quasi-isomorphism to that complex; finite projective terms give
flat, quasi-coherent and finitely presented sheaves.
Source: Stacks Project, Tag 01IB (schemes-lemma-spec-sheaves), and Tag 08EB.
(blueprint: lem-pc-affine-projective-sections-sheafification).

Proof: Use the explicit functor tilde followed by restriction along Y.isoSpec.hom.
The affine tilde functor is exact and thus preserves quasi-isomorphisms. Its counit
on every term of D is invertible because that term is quasi-coherent; naturality
makes these counits a chain isomorphism from the sheafified section complex to D.
Compose this chain isomorphism with the sheafification of q. Each finite projective
module P.X n is a retract of a finite free module. Tilde and restriction preserve
the retraction and finite sums, giving a retract of a finite free structure-module
on Y. Such a retract is quasi-coherent and finitely presented. On an affine open U
its sections are finite projective over Gamma(U,O), hence flat. For affine U inside
affine V, Gamma(U,O) is flat over Gamma(V,O) by flatness of open immersions.
Transitivity of flatness gives exactly the sectionwise IsFlatOver identity predicate,
with its restriction-of-scalars action. These arguments include rank zero and the zero ring.
No boundedness or perfectness is assumed in this sheafification step. -/
theorem affine_projective_sections_sheafification
    (Y : Scheme.{u}) [IsAffine Y]
    (D : CochainComplex Y.Modules ℤ)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (P : CochainComplex (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) ℤ)
    (hfinite : ∀ n : ℤ, Module.Finite (Γ(Y, ⊤) : Type u) (P.X n))
    (hprojective : ∀ n : ℤ, Module.Projective (Γ(Y, ⊤) : Type u) (P.X n))
    (q : P ⟶ ((@Functor.mapHomologicalComplex ℤ Y.Modules
      (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) _ _ _ _
      (SheafOfModules.evaluation.{u} Y.ringCatSheaf (op ⊤))
      ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)).obj D))
    (hq : QuasiIso q) :
    let C := ((tilde.functor Γ(Y, ⊤) ⋙ restrictFunctor Y.isoSpec.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
    (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 Y)) ∧
    (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
    (∀ n : ℤ, (C.X n).IsFinitePresentation) ∧
    ∃ e : C ⟶ D, QuasiIso e := by sorry

end AlgebraicGeometry.Scheme.Modules
