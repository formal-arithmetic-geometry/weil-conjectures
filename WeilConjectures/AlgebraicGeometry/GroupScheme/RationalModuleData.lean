/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HopfCoactionLinearization
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Rational coactions over an arbitrary commutative base ring

Source: Alper, Adequate moduli spaces, Proposition 9.5.1, affine comodule translation.
(blueprint: def-sfb-ring-rational-module-data)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.RingRationalModule

variable (A : CommRingCat.{u})

/-- Expose the given group law to the canonical affine Hopf construction.
Source: Mathlib Group/Affine. (blueprint: def-sfb-ring-rational-module-data) -/
instance coordinateOverGroup (G : Grp (Over (Spec A))) :
    GrpObj (G.X.left.asOver (Spec A)) := G.grp

/-- Pullback of functions over the base preserves the base scalars.
Source: Mathlib Group/Affine; Alper, Proposition 9.5.1.
(blueprint: def-sfb-ring-rational-module-data)

Proof: the canonical coordinate algebra structure pulls back scalars along the
structure morphism, using the canonical Gamma/Spec isomorphism. The over-category
square for f commutes. Applying the contravariant global-sections functor and
its composition law to that square gives this equality at each scalar a. -/
theorem coordinateMap_commutes {G H : Grp (Over (Spec A))}
    [IsAffine G.X.left] [IsAffine H.X.left] (f : G ⟶ H) (a : A) :
    f.hom.hom.left.appTop.hom (algebraMap A Γ(H.X.left, ⊤) a) =
      algebraMap A Γ(G.X.left, ⊤) a := by
  sorry

/-- Pullback on the canonical coordinate algebras, with its actual appTop ring map.
Source: Mathlib Group/Affine; Alper, Proposition 9.5.1.
(blueprint: def-sfb-ring-rational-module-data) -/
def coordinateMap {G H : Grp (Over (Spec A))}
    [IsAffine G.X.left] [IsAffine H.X.left] (f : G ⟶ H) :
    Γ(H.X.left, ⊤) →ₐ[A] Γ(G.X.left, ⊤) :=
  { f.hom.hom.left.appTop.hom with commutes' := coordinateMap_commutes A f }

variable (G : Grp (Over (Spec A))) [IsAffine G.X.left]
variable (V : Type v) [AddCommGroup V] [Module A V]

/-- A rational coaction is exactly a counital, coassociative linear map. The Hopf
structure is the canonical coordinate structure, with no flatness condition on V.
This is the project's existing commutative-base right-coaction predicate
`BorelDistributions.IsCoordinateCoaction` (def-sfb-affine-group-distribution-calculus),
re-exported here for the group object `G`; its conjuncts are coassociativity, then counit.
Source: Alper, Proposition 9.5.1, rational-module translation of quasi-coherent sheaves.
(blueprint: def-sfb-ring-rational-module-data) -/
abbrev IsRational (ρ : V →ₗ[A] V ⊗[A] Γ(G.X.left, ⊤)) : Prop :=
  BorelDistributions.IsCoordinateCoaction A G.X.left ρ

/-- The invariant submodule is the kernel of the coaction minus v mapped to v tensor 1.
This definition applies also to the restricted or inflated coaction map.
Source: Alper, Proposition 9.5.1, kernel-invariant direct image.
(blueprint: def-sfb-ring-rational-module-data) -/
def invariants (ρ : V →ₗ[A] V ⊗[A] Γ(G.X.left, ⊤)) : Submodule A V :=
  LinearMap.ker (ρ - (TensorProduct.mk A V Γ(G.X.left, ⊤)).flip 1)

/-- Equivariance is the coaction square for the specified linear map.
Source: Alper, Proposition 9.5.1, morphisms of rational modules.
(blueprint: def-sfb-ring-rational-module-data) -/
def IsEquivariant {W : Type w} [AddCommGroup W] [Module A W]
    (ρ : V →ₗ[A] V ⊗[A] Γ(G.X.left, ⊤))
    (σ : W →ₗ[A] W ⊗[A] Γ(G.X.left, ⊤)) (f : V →ₗ[A] W) : Prop :=
  f.rTensor Γ(G.X.left, ⊤) ∘ₗ ρ = σ ∘ₗ f

/-- Restriction, or inflation for a quotient map, composes with pullback of coordinates.
Source: Alper, Proposition 9.5.1, pullback along BH to BQ.
(blueprint: def-sfb-ring-rational-module-data) -/
def restrict {H : Grp (Over (Spec A))} [IsAffine H.X.left] (f : H ⟶ G)
    (ρ : V →ₗ[A] V ⊗[A] Γ(G.X.left, ⊤)) :
    V →ₗ[A] V ⊗[A] Γ(H.X.left, ⊤) :=
  (coordinateMap A f).toLinearMap.lTensor V ∘ₗ ρ

end AlgebraicGeometry.RingRationalModule
