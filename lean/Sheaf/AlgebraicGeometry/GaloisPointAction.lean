/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.GaloisPointActionCore
import Sheaf.AlgebraicGeometry.GaloisPointActionOpen

/-! Galois action on the functor of geometric lifts. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3.
(blueprint: lem-exc-galois-point-action).
-/
theorem exists_galoisPointAction
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    ∃ ρ : Gal(Ks/K) →* End p.fiber,
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (_ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x : p.fiber.obj X),
        ((ρ g).app X x).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) ∧
      (∀ (X : S.Etale) (x : p.fiber.obj X),
        IsOpen {g : Gal(Ks/K) | (ρ g).app X x = x}) := by
  dsimp
  obtain ⟨ρ, hρ⟩ := exists_galoisPointAction_core K Ks Ω
  refine ⟨ρ, hρ, ?_⟩
  exact galoisPointAction_open_stabilizers K Ks Ω ρ hρ

end AlgebraicGeometry.Scheme
