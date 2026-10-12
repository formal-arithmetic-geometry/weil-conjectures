/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop
import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# Intersection with an effective Cartier divisor

Source: Stacks Project, Varieties, Tags 0BEU and 0BEV
(blueprint: lem-sc-intersection-effective-cartier).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Intersection with a nonempty effective Cartier divisor gives the intersection number
of the remaining bundles on that divisor, and preserves properness and ampleness.
Source: Stacks Project, Varieties, Tags 0BEU and 0BEV
(blueprint: lem-sc-intersection-effective-cartier).

Proof:
1. Restrict the bundles to `Z`. The closed immersions `D → Z → X` make `D` proper over `k`
   by `lem-weil-pbc-closed-immersion-proper`. The Cartier ideal is invertible by
   `lemma-nagata-effective-cartier-is-invertible`. Its dual is `O_Z(D)` by
   `lem-pc-divisor-line-bundle-invertible`. The exact sequence `0 → J → O_Z → O_D → 0`,
   tensored with invertible bundles, gives the Euler-characteristic difference formula.
   In the zero-scheme case, `lem-pc-zero-scheme-divisor-iso` supplies `hIso` from a section
   of the restricted bundle whose zero scheme is Cartier.
2. If the divisor dimension is assumed, retain it. Otherwise `Z` is integral and proper,
   hence of finite type over `k`; `lem-sc-effective-cartier-dimension-drop` applied to the
   nonempty Cartier divisor gives dimension `d - 1`.
3. By `lem-pc-euler-additive`, the difference of the twist polynomials is the polynomial
   on `D`. By `lem-sc-snapper-numerical-polynomial` its total degree is at most `d - 1`.
   Comparing the coefficient of `n₂ ⋯ n_d` in this difference with that of `n₁ ⋯ n_d`
   in the original polynomial gives the equality by `def-sc-intersection-number`.
4. By `def-sc-ample`, a positive power of an ample bundle is very ample. Compose its
   closed immersion into projective space with `D → Z → X`. Its pullback of `O(1)` is
   the restriction of that power. By `lem-pc-very-ample-ample` it is ample, and the
   positive-power characterization on the proper scheme `D` makes the restriction ample.
-/
theorem intersection_effectiveCartier
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (Z : Scheme.{u}) [Nonempty Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : 1 ≤ d)
    (hdimZ : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞))
    (L : Fin d → X.Modules)
    [∀ j : Fin d, (L j).IsInvertible]
    (J : Z.IdealSheafData) (hJ : J.IsInvertible) [Nonempty J.subscheme]
    (hDim : topologicalKrullDim J.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ∨
      IsIntegral Z)
    (hIso : (Scheme.Modules.tensorPullback i).obj (L ⟨0, hd⟩) ≅
      Scheme.Modules.dual J.toModules) :
    IsProper (J.subschemeι ≫ i ≫ X ↘ Spec (.of k)) ∧
      (∃ hdimD : topologicalKrullDim J.subscheme =
          (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞),
        (∀ (M : X.Modules), M.IsInvertible →
        IsAmple (X ↘ Spec (.of k)) M →
        IsAmple (J.subschemeι ≫ i ≫ X ↘ Spec (.of k))
            ((Scheme.Modules.tensorPullback (J.subschemeι ≫ i)).obj M)) ∧
      Scheme.Modules.intersectionNumber k X Z i d hdimZ L =
        Scheme.Modules.intersectionNumber k X J.subscheme (J.subschemeι ≫ i) (d - 1)
          hdimD
          (fun j : Fin (d - 1) ↦ L ⟨j.1 + 1, by omega⟩)) := by
  sorry

end AlgebraicGeometry
