/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Torsion orders invertible in a field

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
node order 1680 (blueprint: def-kun-torsion-invertible).

Torsion itself is the existing `CategoryTheory.Sheaf.IsTorsion`. The predicate below
adds the field-dependent condition on each element of each geometric stalk; it does
not require a common annihilator. Geometric points with separably closed residue
fields suffice and include the algebraically closed geometric points.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Positive integer orders invertible in the ground field. Their ordering is divisibility,
encoded by `invertibleTorsionOrderDvd`, rather than the usual ordering of natural numbers.
Source: Weil blueprint, node order 1680 (blueprint: def-kun-torsion-invertible). -/
def invertibleTorsionOrders (K : Type u) [Field K] : Set ℕ :=
  {n | 0 < n ∧ (n : K) ≠ 0}

/-- Divisibility on the positive orders invertible in `K`.
Source: Weil blueprint, node order 1680 (blueprint: def-kun-torsion-invertible). -/
def invertibleTorsionOrderDvd (K : Type u) [Field K]
    (n m : invertibleTorsionOrders K) : Prop :=
  n.val ∣ m.val

/-- The `n`-torsion subsheaf, constructed as the kernel of multiplication by `n`.
Source: Weil blueprint, node order 1680 (blueprint: def-kun-torsion-invertible). -/
noncomputable def etaleNTorsion {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (n • 𝟙 F)

/-- Each geometric stalk element has a positive annihilator invertible in `K`.
Source: Weil blueprint, node order 1680 (blueprint: def-kun-torsion-invertible).
In characteristic zero this is ordinary torsion; in positive characteristic it is
prime-to-characteristic torsion. The integer is allowed to depend on the stalk element. -/
def IsTorsionOfInvertibleOrder (K : Type u) [Field K] (T : Over (Spec (.of K)))
    (F : Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T.left)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
    ∃ n : ℕ, n ∈ invertibleTorsionOrders K ∧ n • x = 0

/-- Torsion cohomology with orders invertible in `K`, in every integer degree.
Source: Weil blueprint, node order 1680 (blueprint: def-kun-torsion-invertible). -/
def HasTorsionCohomologyOfInvertibleOrder (K : Type u) [Field K] (T : Over (Spec (.of K)))
    (E : DerivedCategory (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})) : Prop :=
  ∀ q : ℤ, IsTorsionOfInvertibleOrder K
    T ((DerivedCategory.homologyFunctor
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj E)

end AlgebraicGeometry.Etale
