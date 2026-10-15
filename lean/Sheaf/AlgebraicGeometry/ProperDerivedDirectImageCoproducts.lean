/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import Sheaf.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Coproducts and proper derived direct image

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-proper-coproducts.md;
Stacks Project, Tags 0A3V, 095U and 0F11 (blueprint: lem-amb-proper-coproducts).
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper direct image with finite commutative coefficients preserves every set-indexed
coproduct on the ordinary unbounded derived categories. Its restriction to the bounded-below
category agrees with the bounded-below derived direct image.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-proper-coproducts.md;
Stacks Project, Tags 0A3V, 095U and 0F11 (blueprint: lem-amb-proper-coproducts).

Proof:
1. By pqf-lem-proper-basic, r is quasi-compact and quasi-separated. Since T is
   quasi-compact, lem-fin-finite-type-fibre-dimension-bound gives a uniform nonnegative
   bound e on fibre dimensions, including empty fibres, without an absolute dimension bound.
2. Finiteness of A gives N > 0 with N * 1 = 0. Every A-module sheaf is killed by N,
   hence its underlying abelian sheaf is torsion: in the filtered colimit of the n-torsion
   subsheaves the N-torsion term is already the whole sheaf, and passage to lcm(n,N)
   shows that its inclusion is inverse to the canonical colimit map.
   Apply lem-kun-proper-torsion-cd-bound to get vanishing above 2e. By
   lem-sbc-higher-direct-image-forget-comparison this also gives module-sheaf vanishing;
   a module sheaf with zero underlying abelian sheaf is zero.
3. Apply lem-exc-direct-image-coproducts with c = 2e. Its finite acyclic-resolution
   argument proves coproduct preservation for arbitrary unbounded inputs, including
   the empty family. Finally src-right-derived-functor-plus-compatibility, applied to
   the additive module direct image, supplies the bounded-below comparison isomorphism.
-/
theorem proper_rightDerivedLowerStar_preservesCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (r : V ⟶ T) [IsProper r]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T] :
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r)) ∧
    Nonempty
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) r ⋙
          _root_.DerivedCategory.Plus.ι ≅
        _root_.DerivedCategory.Plus.ι ⋙ rightDerivedLowerStar (ModuleCat.{u + 1} A) r) := by
  sorry

end AlgebraicGeometry.Etale
