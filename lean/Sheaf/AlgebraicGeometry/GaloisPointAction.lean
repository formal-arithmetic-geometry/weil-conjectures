/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-!
# Galois action on the functor of geometric lifts

Source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3.
(blueprint: lem-exc-galois-point-action).

Proof: Extend a K-automorphism of Ks to Omega by first extending it to the algebraic
closure of K in Omega, fixing a transcendence basis and extending to the algebraic
closure of the resulting rational function field. Precompose each geometric lift
with Spec of this extension. A lift to an etale scheme factors through the spectrum
of its finite separable residue field (Stacks 02GL(2)); the image of this field in
Omega lies in the image of Ks. Consequently any two extensions give the same lift.
This proves well-definedness. Postcomposition with an etale-site morphism commutes
with precomposition, giving naturality. Contravariance of Spec gives identity and
multiplication, hence a monoid homomorphism to endomorphisms of the point's fibre.
The subgroup fixing the finite separable residue-field image fixes the lift and is
open for the Krull topology. The full stabilizer is a subgroup containing that open
subgroup and is therefore open. The formula follows from the definition and its
independence of the extension. Empty fibres impose no condition; for a separably
closed base the action is trivial. No algebraicity of Omega over K is required. -/
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
        IsOpen {g : Gal(Ks/K) | (ρ g).app X x = x}) := by sorry

end AlgebraicGeometry.Scheme
