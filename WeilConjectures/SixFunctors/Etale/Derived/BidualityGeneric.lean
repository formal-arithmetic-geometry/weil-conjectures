/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericDuality

/-!
# Verdier biduality at the nonclosed points

The inductive step of the proof of Verdier biduality
(`thm-weil-etale-geometric-biduality`) at a nonclosed point: through a coordinate sending the
point to the generic point of `𝔸¹_k`, biduality in lower dimension on the geometric generic
fibre gives biduality at the point.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The statement proved by induction on the dimension: Verdier biduality on `Dctf(X, Λ)` for
every separated scheme `X` of finite type and of dimension at most `d` over an algebraically
closed field in which the exponent of `Λ` is invertible. -/
def BidualityUpTo (d : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a], topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)

/-- **Biduality at nonclosed points.** Assume Verdier biduality in dimensions `< d`. Let `X` be
separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and let
`K ∈ Dctf(X, Λ)`. Then at every nonclosed point `x` of `X` the geometric stalks of the
cohomology of `δ_K` are isomorphisms. A coordinate `t` on an affine neighbourhood `V` of `x`
sends `x` to the generic point of `𝔸¹_k`; the geometric generic fibre `V_η̄` has dimension
`< d` (`lem-fin-coordinate-generic-dimension`), so `δ` is an isomorphism on it, and it is the
restriction of `δ_K` (`lem-weil-geometric-generic-duality`, `lem-weil-delta-restriction`); and a
geometric point over `x` factors through `V_η̄`. -/
theorem isIso_sheafFiber_map_verdierDualDoubleDual_app_of_not_isClosed (d : ℕ)
    (IH : ∀ d' < d, BidualityUpTo Λ d') {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) (q : ℤ) :
    IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
      ((_root_.DerivedCategory.homologyFunctor _ q).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K))) :=
  sorry

end Etale

end AlgebraicGeometry
