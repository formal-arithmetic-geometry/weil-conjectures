/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Height

/-!
# Strict normal crossings divisors over a field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, Remark 4.2.2(i),
with smooth strata over the field (blueprint: def-trf-smooth-strict-normal-crossings-divisor).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A reduced effective Cartier divisor with finitely many smooth irreducible components
and smooth intersections of the expected pure codimension. The integral closed subschemes
`C i` are pairwise noncontained and their scheme-theoretic union is `D`; consequently these
are exactly its irreducible components with reduced structure. The intersection indexed by
`s` is cut out by the sum `s.sup C`. Pure codimension is expressed by the height of every
minimal prime on every ambient affine chart. Empty intersections are smooth and have no
minimal primes, so they impose no height condition. For `s` empty the intersection is `X`.
Source: ILO VIII Remark 4.2.2(i), and Stacks 0B8X for smoothness over a perfect field
(blueprint: def-trf-smooth-strict-normal-crossings-divisor). -/
def IsSmoothStrictNormalCrossingsDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData) : Prop :=
  D.IsInvertible ∧ IsReduced D.subscheme ∧
    ∃ (n : ℕ) (C : Fin n → X.IdealSheafData),
      D = (⨅ i, C i) ∧
      (∀ i, IsIntegral (C i).subscheme) ∧
      (∀ i j, (C i).support ≤ (C j).support → i = j) ∧
      ∀ s : Finset (Fin n),
        Smooth ((s.sup C).subschemeι ≫ f) ∧
          ∀ (U : X.affineOpens) (p : Ideal Γ(X, U.1)),
            p ∈ ((s.sup C).ideal U).minimalPrimes → p.height = (s.card : ℕ∞)

end AlgebraicGeometry.Scheme.IdealSheafData
