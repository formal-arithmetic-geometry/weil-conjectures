module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section
universe w uA vA vH
open CategoryTheory.Limits
namespace CategoryTheory

/-- Exact derived Gabriel--Popescu localization over a chosen compact source.
(blueprint: lem-g2-grothendieck-derived-exact-localization)
Proof in words: extend Gabriel--Popescu by free presentations, prove exactness using injectives
and Baer's criterion, and derive termwise as in the parent node. -/
theorem grothendieckDerived_exact_localization
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B)
    (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B)
    (aB : ∀ n : ℤ, (shiftFunctor B n).Additive) (tB : Pretriangulated B)
    (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B) :
    letI := cB
    letI := zB
    letI := sB
    letI := pB
    letI := aB
    letI := tB
    letI := iB
    letI := sumsB
    ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
      (adj : L ⊣ R) (sL : L.CommShift ℤ),
    letI := sL
    L.IsTriangulated ∧ IsIso adj.counit := by
  sorry

end CategoryTheory
