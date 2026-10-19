/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale descent of reduced Cartier divisors

Source: literature/stacks-project/spaces-divisors.tex, Tag 083C, with reduced pullback
from literature/stacks-project/descent.tex, Tag 034E, and literature/stacks-project/schemes.tex,
Tag 01J3 (blueprint: lem-trf-etale-reduced-cartier-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Étale pullback preserves the reduced induced closed subscheme, and the effective Cartier
condition descends along a jointly surjective étale family.

Source: Stacks Project, spaces-divisors.tex Tag 083C, conditions (1)--(3), together with
Descent Tag 034E and Schemes Tag 01J3 for the reduced pullback identification. The covering
family is indexed by a type in an arbitrary universe.
(blueprint: lem-trf-etale-reduced-cartier-descent)

Proof:
1. The pullback of the reduced induced closed immersion is a closed immersion with the
   pulled-back ideal. The projection to the reduced induced subscheme is étale by base
   change, hence the pullback is reduced; its image is the inverse image of the closed
   subset, so uniqueness of the reduced induced structure gives the displayed isomorphism.
2. An effective Cartier ideal pulls back along an étale (hence flat) morphism, so the
   forward implication holds for every member of the family.
3. A jointly surjective étale family is an fpqc cover. The ideals of the pulled-back
   reduced subschemes are the pullbacks of the original ideal. Effective Cartier ideals
   are invertible, and fpqc descent of finite locally free rank one reflects invertibility;
   the invertible-ideal/effective-Cartier equivalence gives the converse. The empty
   divisor is covered by the unit ideal.
-/
theorem etale_reduced_cartier_descent
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) :
    (∀ (W : Scheme.{u}) (v : W ⟶ X) [Etale v],
      ∃ e : pullback v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≅
          (Scheme.IdealSheafData.vanishingIdeal
            (Z.preimage v.continuous)).subscheme,
        e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
            (Z.preimage v.continuous)).subschemeι =
          pullback.fst v (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) ∧
    (∀ {ι : Type*} (W : ι → Scheme.{u}) (v : ∀ i, W i ⟶ X)
        [∀ i, Etale (v i)],
      (⋃ i, Set.range (v i).base = Set.univ) →
      ((Scheme.IdealSheafData.vanishingIdeal Z).IsInvertible ↔
        ∀ i, (Scheme.IdealSheafData.vanishingIdeal
          (Z.preimage (v i).continuous)).IsInvertible)) := by
  sorry

end AlgebraicGeometry
