/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange

/-! # A finite-level estimate for internal Hom of integral reductions -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

set_option hygiene false in
local notation "D(" X ", " R ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} R))

/-- The finite-level part of integral constructible internal Hom, for a single reduction,
before derived completeness and uniform tower bounds. The Tor bounds are measured after
restriction to `R`.

Source: blueprint `cor-coef-integral-internal-hom.proof.md`, sentences 2--4, specialized to
constant coefficients on the small etale site, with the regular coefficient sequence of
`lem-coef-integral-hom-reduction.proof.md`.
(blueprint: lem-coef-small-etale-integral-finite-hom-estimate)

Proof: every R/I^(m+1) is finite, by its finite filtration with subquotients of R/I.
For a residue field F of this finite ring, the regular two-term resolution of R/I^(m+1)
tensored over R with F has zero differential and is F[1] direct-sum F. By associativity,
testing the underlying R-reduction of K against the constant F-sheaf therefore tests the
direct sum of K tensor_R F and its shift by 1. The interval [a,b] forces K tensor_R F
to have support in [a+1,b]. Construct universal derived reductions Kn,Ln by a K-flat quotient model.
Universality and derived scalar associativity identify this with Kn tensor_(R/I^(n+1)) F.
Similarly the residue tests for Ln have support [c+1,e].
The finite-length filtration of any module over each local Artinian factor, or equivalently
the nilpotent-ideal residue criterion, gives quotient Tor intervals [a+1,b] and [c+1,e].
Constructibility of Kn and Ln follows from that of their restrictions to R. The case where
v is a unit has zero quotient categories. Constructibility transports through exact scalar
restriction. On affine opens over an algebraic closure of the base field, the finite-Tor
constructible Hom estimate, by dual-tensor-dual, gives quotient Tor interval
[c+1-b-2d,e-a-1+2d]. It applies to arbitrary finite coefficient rings on finite-Tor inputs;
no self-injectivity of R or its quotients is asserted. Descent under the field extension and
gluing over affine opens preserve constructibility and the bounds. Restricting scalars to R
adds the degree -1 term of the regular coefficient resolution, giving
[c-b-2d,e-a-1+2d], contained in the claimed interval. Exact restriction commutes with homology.
The scalar adjunction and the regular coefficient triangle identify the restricted finite Hom
with the displayed reduction of the ambient Hom. Completeness and uniform tower bounds are
separate steps. This estimate assumes only one finite-level reduction of K and L.
If an input interval is reversed, its tensor-unit test makes that reduction zero, so its finite
Hom is zero. The empty scheme is handled by the same vanishing argument. At a point with
K=L=R, the restricted reductions have amplitude [-1,0] and the asserted interval is [-1,1],
which contains the actual output. For K=R/v and L=R over a DVR, retaining the degree -1
coefficient term gives input intervals [-2,0] and [-1,0] and output contained in [-1,2]. -/
theorem integralFiniteHomEstimate
    {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    [Finite (R ⧸ I)]
    {v : R} (hv : v ∈ nonZeroDivisors R) (hI : I = Ideal.span {v})
    {k : Type u} [Field k] [HasInvertibleExponent (R ⧸ I) (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (n : ℕ)
    {K L : D(X, R)}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b c e : ℤ)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b
      ((reductionModIdeal R X (I ^ (n + 1))).obj K))
    (hLt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X c e
      ((reductionModIdeal R X (I ^ (n + 1))).obj L))
    : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
        ((reductionModIdeal R X (I ^ (n + 1))).obj
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L)) := by
  sorry

end AlgebraicGeometry.Etale
