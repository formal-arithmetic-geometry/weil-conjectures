/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import WeilConjectures.CategoryTheory.SiteCechVanishingStep

/-!
# The Čech vanishing criterion for a general site

## References

* Stacks Project, Cohomology on Sites, Lemma 03F9.
-/

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- Higher Čech vanishing on a cofinal collection of coverings implies higher cohomology
vanishing over the specified objects. `S` supplies the chosen products of each covering
in `Cov`; no finite products of the whole category or of its slices are required.

Stacks Project, Cohomology on Sites, Lemma 03F9. -/
theorem isZero_H'_of_siteCech_vanishing
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
    [HasExt.{r} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    (B : Set C)
    (Cov : ∀ (U : C) (T : Type u) (V : T → C), (∀ t, V t ⟶ U) → Prop)
    (S : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Cov U T V f → SiteCechComplex V f)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hcover : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Cov U T V f → Presieve.ofArrows V f ∈ J U)
    (hB : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (h : Cov U T V f), U ∈ B ∧ (∀ t, V t ∈ B) ∧
        ∀ (p : ℕ) (a : Fin (p + 1) → T), (S U T V f h).W p a ∈ B)
    (hcofinal : ∀ (U : C), U ∈ B →
      ∀ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
        Presieve.ofArrows V f ∈ J U →
        ∃ (K : Type u) (W : K → C) (g : ∀ k, W k ⟶ U),
          Cov U K W g ∧ ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k)
    (hcech : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (h : Cov U T V f) (p : ℕ), 0 < p →
        IsZero (((S U T V f h).cohomologyFunctor p).obj F.obj)) :
    ∀ (U : C), U ∈ B → ∀ (p : ℕ), 0 < p → IsZero (H' F p U) := by
  intro U hU p hp
  have hshift := siteCech_vanishing_dimension_shift J B Cov S F hcover hB hcofinal hcech
  have hUshift := hshift U hU
  induction p using Nat.strong_induction_on with
  | h p ih =>
      by_cases h₁ : p = 1
      · simpa [h₁] using hUshift.1
      · have hlt : 1 < p := by omega
        apply hUshift.2 p hlt
        apply ih (p - 1)
        · omega
        · omega

end CategoryTheory.Sheaf
