/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Relative affine vanishing

Placeholder, proved on branch dl-a1-b1-wip/artingabber.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- Placeholder, proved on branch dl-a1-b1-wip/artingabber. -/
theorem Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (N : ℕ)
    (hX : topologicalKrullDim X ≤ N) (y : Y) (r : ℕ)
    (hr : topologicalKrullDim (closure ({y} : Set Y)) = r) (q : ℤ) (hq : (N : ℤ) < q + r) :
    IsZero ((Y.uliftPointSmallEtale y).sheafFiber.obj (Etale.higherDirectImage Λ f q G)) := by
  sorry

end AlgebraicGeometry
