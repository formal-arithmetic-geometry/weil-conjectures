module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Zero entries persist on later spectral-sequence pages

Source: Stacks Project, Homology, Tag 0BDV (proof of lemma-relate-boundedness),
using the page-homology definition in Tag 011N (definition-spectral-sequence).
(blueprint: lem-weil-pbc-spectral-page-zero-propagation)
-/

@[expose] public section

universe v u

namespace CategoryTheory.SpectralSequence

open Limits

/-- Zero entries of an integer-bigraded cohomological spectral sequence persist on later
pages. If page two is supported in the first quadrant and has zero positive rows, every
page is supported in row zero with nonnegative first coordinate. Any stationary value
in a positive row is therefore zero; a stationary value is expressed by isomorphisms
from every sufficiently late page entry to that object.

Source: Stacks Project, Homology, Tags 0BDV and 011N.
(blueprint: lem-weil-pbc-spectral-page-zero-propagation)

Proof: Fix a page t and bidegree (p,q). Its incoming and outgoing differentials form
the short complex with objects E_t^(p-t,q+t-1), E_t^(p,q), E_t^(p+t,q-t+1).
Their composite is zero by the page complex axiom (def-sp-spectral-sequence).
If its middle object is zero, lem-weil-pbc-short-complex-zero-homology, namely
ShortComplex.isZero_homology_of_isZero_X₂, makes its homology zero. The specified
page-homology isomorphism then makes E_(t+1)^(p,q) zero. Induction on k gives
vanishing on page s+k from vanishing on page s, proving the first assertion for
r >= s. Under the two page-two vanishing hypotheses, p < 0 or q < 0 uses the
first hypothesis; the remaining off-row case has q > 0 and uses the second.
Propagating from s = 2 proves the support assertion on every page. For a positive-row
stationary value, choose its starting page R and transport the vanishing at page R
along the supplied isomorphism to the stationary object. -/
theorem spectral_page_zero_propagation
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequence C) :
    (∀ (s : ℤ) (hs : 2 ≤ s) (p q r : ℤ) (hsr : s ≤ r),
      IsZero ((E.page s hs).X (p, q)) →
        IsZero ((E.page r (le_trans hs hsr)).X (p, q))) ∧
    ((∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q))) →
      (∀ p q : ℤ, 0 < q → IsZero ((E.page 2).X (p, q))) →
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
        p < 0 ∨ q ≠ 0 → IsZero ((E.page r hr).X (p, q))) ∧
      ∀ p q : ℤ, 0 < q → ∀ Z : C,
        (∃ (R : ℤ) (hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          Nonempty ((E.page r (le_trans hR hr)).X (p, q) ≅ Z)) → IsZero Z) := by
  have hprop : ∀ (s : ℤ) (hs : 2 ≤ s) (p q r : ℤ) (hsr : s ≤ r),
      IsZero ((E.page s hs).X (p, q)) →
        IsZero ((E.page r (le_trans hs hsr)).X (p, q)) := by
    intro s hs p q r hsr hz
    induction r, hsr using Int.leInduction with
    | base => exact hz
    | succ r hsr ih =>
      exact (ShortComplex.isZero_homology_of_isZero_X₂
        ((E.page r (le_trans hs hsr)).sc (p, q)) ih).of_iso
          (E.iso r (r + 1) (p, q) rfl (le_trans hs hsr)).symm
  refine ⟨hprop, ?_⟩
  intro hquad hpos
  have hsupport : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      p < 0 ∨ q ≠ 0 → IsZero ((E.page r hr).X (p, q)) := by
    intro r hr p q hpq
    apply hprop 2 (by omega) p q r hr
    rcases hpq with hp | hq
    · exact hquad p q (Or.inl hp)
    · by_cases hneg : q < 0
      · exact hquad p q (Or.inr hneg)
      · exact hpos p q (by omega)
  refine ⟨hsupport, ?_⟩
  intro p q hq Z hstationary
  obtain ⟨R, hR, hstationary⟩ := hstationary
  obtain ⟨e⟩ := hstationary R le_rfl
  exact (hsupport R hR p q (Or.inr (by omega))).of_iso e.symm

end CategoryTheory.SpectralSequence
