module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.CategoryTheory.SiteCechComplex

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The injective-resolution and Čech-complex argument of Stacks 03F9 produces the
base case and the dimension-shifting step. The remaining proof is the standard
strong induction on the degree.

Proof in words: embed a Čech-acyclic sheaf into an injective, use the short exact
section sequences and the long exact sequences of derived functors and Čech
complexes. The injective is Čech-acyclic and has vanishing higher derived
functors; section surjectivity gives degree one, and dimension shifting gives
higher degrees.
(blueprint: lem-weil-pbc-site-cech-vanishing-dimension-shift) -/
theorem siteCech_vanishing_dimension_shift
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
    ∀ U, U ∈ B →
      IsZero (H' F 1 U) ∧
        ∀ p, 1 < p → IsZero (H' F (p - 1) U) → IsZero (H' F p U) := by
  sorry

end CategoryTheory.Sheaf
