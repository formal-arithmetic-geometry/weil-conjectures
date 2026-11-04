/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationBase
import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationComparison

/-! # Finite filtered twisting totalization

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (blueprint: lem-trf-filtered-mapping-cylinder-step).
The realization record spells out the summand differential, tail inclusions,
degreewise splitting and canonical quotient projections, using the existing notions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- Finite upper triangular twisting families have the specified total complex,
degreewise split finite tail filtration, canonical graded identifications and compatible maps.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (blueprint: lem-trf-filtered-mapping-cylinder-step).

Proof:
1. On the finite biproduct put the original differentials on the diagonal and the
   degree-one twisting maps above it. The diagonal entries of the square vanish
   because each G is a complex; each remaining potentially nonzero entry is the
   assumed Maurer--Cartan expression. Hence the differential squares to zero.
2. The differential increases the weight. Its tails are therefore subcomplexes,
   with F^a = top and F^(b+1) = bottom. Summand coordinates split every tail
   inclusion degreewise. Projection to weight p kills the next tail and identifies
   its cokernel complex with G_p: the off-diagonal differential terms vanish in
   this quotient. Outside the interval consecutive tails agree and the grade is zero.
3. Finitely many upper bounds give a common upper bound for the total complex and
   its tails. Their terms are finite sums of flat sheaves (lem-pc-kflat-closure),
   including the empty sum. Apply lem-pc-bounded-above-flat-kflat-site (Stacks 06YQ)
   to obtain K-flatness. The separately assumed K-flatness of G_p is redundant here.
4. For a strictly compatible family f, its direct sum commutes with the diagonal
   differential entries by the chain-map identities and with the twisting entries
   by the stated compatibility. It preserves every tail. The quotient projection
   squares identify its graded map with f_p under the same graded identifications,
   proving naturality and graded quasi-isomorphism; the outside grades are zero. -/
theorem exists_finiteFilteredTwistingTotalization
    (a b : ℤ) (hab : a ≤ b) (D : FiniteTwistingFamily R a b) :
    ∃ M : FiniteTwistingTotalization D,
      (((∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
          SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
        (∀ p : ↥(Finset.Icc a b), (D.G p).IsKFlatIndependentCoefficients)) →
        M.P.IsKFlatIndependentCoefficients ∧
          ∀ r : ℤ, IsKFlatIndependentCoefficients (J := J) (R := R)
            (M.F.step r : CochainComplex (ringedSiteModules.{w}
              ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)) ∧
      ∀ D' : FiniteTwistingFamily R a b,
        ∃ M' : FiniteTwistingTotalization D',
          ∀ (f : ∀ p : ↥(Finset.Icc a b), D.G p ⟶ D'.G p),
            (∀ p : ↥(Finset.Icc a b), QuasiIso (f p)) →
            (∀ (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) (n : ℤ),
              D.τ p q hpq n ≫ (f q).f (n + 1) = (f p).f n ≫ D'.τ p q hpq n) →
            ∃ φ : FilteredObject.Hom ⟨M.P, M.F⟩ ⟨M'.P, M'.F⟩,
              (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
                biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
                    (M.coordinates n).inv ≫ φ.hom.f n =
                  (f p).f n ≫
                    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
                      (M'.coordinates n).inv) ∧
              (∀ p : ↥(Finset.Icc a b),
                (M.gradedIso p).hom ≫ f p =
                  FilteredObject.gradedMapSteps φ p.val ≫ (M'.gradedIso p).hom) ∧
              (∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps φ p)) := by
  obtain ⟨M, hflat⟩ := exists_finiteTwistingTotalization_base a b hab D
  refine ⟨M, hflat, ?_⟩
  intro D'
  obtain ⟨M', _⟩ := exists_finiteTwistingTotalization_base a b hab D'
  refine ⟨M', ?_⟩
  intro f hf hτ
  exact exists_finiteTwistingTotalization_comparison D D' M M' f hf hτ

end CochainComplex
