/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Degree-zero base change to the fraction field

Source: Stacks Project, Cohomology of Schemes, Tag 02KH, degree zero.
(blueprint: lem-sc-fraction-field-sections-base-change)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat base change on global sections, including its normalization on pure tensors.

Source: Stacks Project, Cohomology of Schemes, Tag 02KH, degree zero; More on
Morphisms, Tag 0EX8, general-case proof, displayed base-change equality.
(blueprint: lem-sc-fraction-field-sections-base-change)

Proof: The fraction field is a flat A-algebra. For a finite affine open cover of X,
separatedness over the affine base makes finite intersections affine. Quasi-coherence
identifies sections on each base-changed affine with K tensor_A the original sections.
These identifications send 1 tensor s to the adjunction-unit image of s and commute
with restriction. Global sections are the kernel of the first Cech differential.
Flatness preserves that kernel, and tensoring commutes with the finite products
in the first two Cech terms. This gives the asserted K-linear isomorphism and its
formula. Equivalently, apply the separated flat-cohomology comparison in degree zero
and identify H^0 with sections, tracking the augmentation. On the empty scheme both
sides are zero. No properness, valuation hypothesis, or triviality is used. -/
theorem exists_fractionField_sections_baseChange
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    (L : X.Modules) [L.IsQuasicoherent] :
    let g := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    let M := (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj L)
    let MK := (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ fK.appTop).hom).obj
      ((SheafOfModules.evaluation _ (op ⊤)).obj ((Modules.pullback g).obj L))
    ∃ e : K ⊗[A] M ≃ₗ[K] MK,
      ∀ s : Γ(L, ⊤), e (1 ⊗ₜ[A] s) =
        ((pullbackPushforwardAdjunction g).unit.app L).app ⊤ s := by sorry

end AlgebraicGeometry.Scheme.Modules
