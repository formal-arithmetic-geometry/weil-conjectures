/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
/-! # Localized ring comparison
Source: Stacks Project, Algebra, Tag 037D, proof first paragraph.
(blueprint: lem-pc-localized-ring-colimit-comparison) -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra
/-- Canonical localized ring colimit comparison.
Source: Stacks Project, Algebra, Tag 037D, proof first paragraph.
(blueprint: lem-pc-localized-ring-colimit-comparison)
Proof: The stage local maps form a cocone, since their restrictions to the original
rings agree. Lift each numerator and denominator through the supplied ring colimit and
pass to a common stage; the lifted denominator avoids the contracted prime. This proves
surjectivity of the induced map. For injectivity, lift a multiplier outside the prime
witnessing equality of fractions. The zero cross difference holds at a later stage by
the filtered colimit equality criterion. The multiplier remains outside the prime,
so the fractions agree there. Hence the induced map is a bijective ring map. Its inverse
is a ring map and the coprojection formula is its defining factorization equation.
The numerator transition equation determines each entire localized transition map. -/
theorem localizedRingColimitComparison
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] (F L : Λ ⥤ CommRingCat.{u})
    (κ : F ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (hF : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (p : Ideal T) [p.IsPrime] (pᵢ : ∀ i, Ideal (F.obj i)) [∀ i, (pᵢ i).IsPrime]
    (hp : ∀ i, pᵢ i = p.comap (κ.app i).hom)
    (eᵢ : ∀ i, L.obj i ≃+* Localization.AtPrime (pᵢ i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : F.obj i),
      eᵢ j ((L.map f).hom ((eᵢ i).symm (algebraMap _ _ x))) =
        algebraMap _ _ ((F.map f).hom x)) :
    ∃ e : (colimit L : CommRingCat.{u}) ≃+* Localization.AtPrime p,
      ∀ i (z : L.obj i), e ((colimit.ι L i).hom z) =
        Localization.localRingHom (pᵢ i) p (κ.app i).hom (hp i) (eᵢ i z) := by sorry
end Algebra
