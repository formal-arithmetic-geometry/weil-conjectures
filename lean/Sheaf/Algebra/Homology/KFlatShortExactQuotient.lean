/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Homology.HomologySequence

/-! # Total tensor exactness and K-flatness for a flat quotient

Source: Stacks Project, Cohomology on Sites, Tag 0G7B,
`lemma-K-flat-two-out-of-three-ses`, used in Tag 0F1M
(blueprint: lem-kun-kflat-short-exact-quotient).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

set_option autoImplicit false in
/-- A degreewise short exact sequence with flat quotient stays degreewise short exact
under direct-sum total tensor with any complex; K-flatness satisfies all three
implications of two out of three. No boundedness or splitting is assumed.
Source: Stacks Project, Cohomology on Sites, Tag 0G7B
(blueprint: lem-kun-kflat-short-exact-quotient).

Proof:
1. Apply `lem-weil-pbc-site-flat-quotient-tensor-ses` in each bidegree `(p,q)`
   with quotient `S.X₃.X p` flat and arbitrary tensor factor `A.X q`.
2. The sheafified tensor symmetry of `def-pur-sheaf-tensor-product`, natural
   in the two sequence maps, gives the same exact sequence in the other orientation.
3. In total degree `n`, take finite biproducts over finite subsets of the pairs
   `(p,q)` with `p + q = n`. Their filtered colimit is the full sheaf coproduct.
   Exact filtered colimits from `lem-pur-ringed-site-grothendieck-abelian` give
   short exactness of that coproduct, in both tensor orientations.
4. The canonical tensor maps commute with the differential
   `d ⊗ 1 + (-1)^p (1 ⊗ d)` by the chain-map identities and tensor functoriality.
   Thus the degreewise sequences are precisely the asserted total tensor sequence.
   Every summand has just two outgoing differential components, even when unbounded.
5. For any acyclic test complex, K-flatness of two original complexes makes two
   left total tensors acyclic by `def-pc-kflat-complex`. The long exact cohomology
   sequence of `lem-weil-pbc-complex-ses-homology-long-exact` forces the third
   tensor to be acyclic: use the neighbors of Hⁿ of the third, first, or middle
   tensor, respectively. By `def-pc-acyclic-complex-modules` this is acyclicity
   in every integer degree. Quantifying over all acyclic tests proves each of
   the three K-flatness implications. -/
theorem kflat_shortExact_flat_quotient
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (S : ShortComplex (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (hS : S.ShortExact)
    (hP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (S.X₃.X i)) :
    (∀ A : CochainComplex (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
      (∃ h : (S.f ▷ A) ≫ (S.g ▷ A) = 0,
        (ShortComplex.mk (S.f ▷ A) (S.g ▷ A) h).ShortExact)) ∧
    (S.X₁.IsKFlatIndependentCoefficients → S.X₂.IsKFlatIndependentCoefficients →
      S.X₃.IsKFlatIndependentCoefficients) ∧
    (S.X₁.IsKFlatIndependentCoefficients → S.X₃.IsKFlatIndependentCoefficients →
      S.X₂.IsKFlatIndependentCoefficients) ∧
    (S.X₂.IsKFlatIndependentCoefficients → S.X₃.IsKFlatIndependentCoefficients →
      S.X₁.IsKFlatIndependentCoefficients) := by
  sorry

end CochainComplex
