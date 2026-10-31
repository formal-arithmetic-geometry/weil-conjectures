/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinDeformationTestCategory

/-! # Morphisms of formal objects with varying complete local bases

Source: Stacks Project, Formal Deformation Theory, Tags 06H3, 06T2 and 06T3
(blueprint: def-sfb-artin-formal-base-morphism).

The local residue-preserving map pins every positive-level map to the actual
quotient composite; compatibility uses the canonical evaluation restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
  [Module.Finite R k]

/-- A morphism of formal objects over possibly different complete marked local rings.
The level maps are precisely the composites to the target's positive truncations.
The compatibility square uses the recorded canonical evaluation restriction.
Source: Stacks, Formal Deformation Theory, Tags 06H3, 06T2 and 06T3
(blueprint: def-sfb-artin-formal-base-morphism). -/
structure FormalBaseMorphism {F : CofibredGroupoids.{u, v, w} R k}
    {B C : CompleteLocalAlgebra R k} (η : FormalObject F B) (ξ : FormalObject F C) where
  hom : B.ring →ₐ[R] C.ring
  localHom : IsLocalHom hom
  marked : ∀ b : B.ring,
    C.residueEquiv (IsLocalRing.residue C.ring (hom b)) =
      B.residueEquiv (IsLocalRing.residue B.ring b)
  atLevel : ∀ n : ℕ, LocalMap B (levelTest C n)
  atLevel_eq : ∀ n : ℕ,
    (atLevel n).hom = (Ideal.Quotient.mkₐ R
      (IsLocalRing.maximalIdeal C.ring ^ (n + 1))).comp hom
  compatible : ∀ {m n : ℕ} (h : n ≤ m),
    (map (levelMap C h)).comp (atLevel m).hom = (atLevel n).hom
  app : ∀ n : ℕ, evaluate η (atLevel n) ≅ ξ.obj n
  comm : ∀ {m n : ℕ} (h : n ≤ m),
    (push F (levelMap C h)).map (app m).hom ≫ (ξ.transition h).hom =
      (evaluationRestriction η (levelMap C h) (atLevel n) (atLevel m)
        (compatible h)).hom ≫ (app n).hom

end AlgebraicGeometry.ArtinDeformation
