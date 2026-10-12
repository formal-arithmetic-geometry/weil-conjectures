/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-! Core action construction for geometric étale lifts. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-exc-galois-point-action-core).

Core action-and-formula part of the geometric Galois point action theorem.

(source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3;
 blueprint: lem-exc-galois-point-action-core).

The proof extends automorphisms from a separable closure through an algebraic closure and
then a transcendence basis, and acts on geometric étale lifts by precomposition.  Factorization
through finite separable residue fields makes the result independent of the chosen extension;
functoriality of precomposition gives the monoid-homomorphism laws and the displayed formula.
-/
theorem exists_galoisPointAction_core
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    ∃ ρ : Gal(Ks/K) →* End p.fiber,
      ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (_ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x : p.fiber.obj X),
        ((ρ g).app X x).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left := by
  sorry

end AlgebraicGeometry.Scheme
