/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions

import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedComparisons
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # Finite Tate descent

Source: Stacks Project, Tags 03PK and 099R.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

private theorem comparison_iso_lift_unique
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} {Z : D}
    (a : F.obj Y ≅ Z) (b : F.obj X ≅ Z) :
    ∃! h : X ≅ Y, F.mapIso h ≪≫ a = b := by
  let e := (Functor.FullyFaithful.ofFullyFaithful F).isoEquiv (X := X) (Y := Y)
  refine ⟨e.symm (b ≪≫ a.symm), ?_, ?_⟩
  · change e (e.symm (b ≪≫ a.symm)) ≪≫ a = b
    simp
  · intro h hh
    apply e.injective
    change F.mapIso h = _
    rw [Equiv.apply_symm_apply]
    calc
      F.mapIso h = (F.mapIso h ≪≫ a) ≪≫ a.symm := by simp
      _ = b ≪≫ a.symm := by rw [hh]

/-- The finite pro-etale Tate twists descend canonically, with the specified root
normalization, all nonnegative tensor powers, pullback squares, exponent transitions,
and uniqueness of the descent with its comparison. Both positive exponents are indexed
by their predecessor: the finite quotient is at `n+1`, and the annihilator is `l^(r+1)`.
There is no condition relating `n+1` to the ramification index.
Source: Stacks Project, Tags 03PK, 099R, 0GLZ, 099T and 03EL. -/
theorem finite_tate_site_descent :
    ∃ b : ∀ (T : Scheme.{u}), IsUnit (l : Γ(T, ⊤)) →
      ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k,
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      IsFiniteTateSiteComparison l E n T r hA k (b T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k),
      IsFiniteTateEtalePullback l E n T v r hA k c ∧
      IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).mapIso
          (b T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso c ≪≫ b T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapIso t ≪≫ b T hT r hA k =
            b T hT r' hA' k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
      (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
      (alpha : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj G ≅
          finiteTateProSheaf l E n T k),
      ∃! h : finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k ≅ G,
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapIso h ≪≫ alpha =
            b T hT r hA k) := by
  classical
  obtain ⟨b, hb⟩ := finite_tate_normalized_comparisons l E n
  obtain ⟨hp, ht⟩ := finite_tate_normalized_coherence l E n b hb
  refine ⟨b, hb, hp, ?_, ?_⟩
  · intro T hT r r' hrr hA hA' k
    obtain ⟨t, htn, hts⟩ := ht T hT r r' hrr hA hA' k
    obtain ⟨q, hq, hqu⟩ := comparison_iso_lift_unique
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
      (b T hT r hA k) (b T hT r' hA' k)
    refine ⟨t, ⟨htn, hts⟩, ?_⟩
    intro t' ht'
    exact (hqu t' ht'.2).trans (hqu t hts).symm
  · intro T hT r hA k G alpha
    exact comparison_iso_lift_unique
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
      alpha (b T hT r hA k)

end AlgebraicGeometry.Scheme
