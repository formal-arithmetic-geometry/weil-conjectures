module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section
universe w uA vA vH
open CategoryTheory.Limits
namespace CategoryTheory

/-- Compact triangulated source supplied by the module-category construction.
(blueprint: lem-g2-grothendieck-derived-compact-source)
Proof in words: the free-module construction and compact-generator argument described in
the parent node; the universe-lifted package is exactly the source part of that argument. -/
theorem grothendieckDerived_compact_source
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B := by
  sorry

end CategoryTheory
