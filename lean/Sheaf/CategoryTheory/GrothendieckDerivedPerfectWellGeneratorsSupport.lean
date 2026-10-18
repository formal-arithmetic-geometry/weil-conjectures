module

public import Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
public import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
public import Sheaf.CategoryTheory.CompactlyGenerated
public import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.CategoryTheory.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory

set_option linter.style.haveILetI false

@[expose] public section

universe v u u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Supporting small-class construction for the exact compact localization.
Source: Neeman, Theorem 0.2 and Krause, Sections 6.2--6.3.
(blueprint: new-sfb-derived-perfect-well-generators-support-b4)

The canonical alpha-compact class above a common regular bound for the image of
the source compact generators is essentially small, shift closed, alpha-small,
and a coproduct factorization class. It contains every image generator. The
construction is the ambient small-class argument; the present statement omits
the separate localizing-generation conclusion, which is proved by the
compact-generator telescope in the importing theorem. -/
theorem exists_small_factorization_class_of_compact_localization
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] :
    ∃ (B : Type (max u (v + 1))) (cB : Category.{v} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{v} B),
      letI := iB
      letI := sumsB
      ∃ (J : Type v) (E : J → B),
        (∀ j, IsCompactObject (E j)) ∧ IsTriangulatedGeneratingFamily E ∧
        ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
          (adj : L ⊣ R) (sL : L.CommShift ℤ),
          letI := sL
          L.IsTriangulated ∧ IsIso adj.counit ∧
          ∃ (G : ObjectProperty (DerivedCategory A)) (κ : Cardinal.{v})
            (_ : Fact κ.IsRegular),
            ObjectProperty.EssentiallySmall.{v} G ∧ G.IsStableUnderShift ℤ ∧
            (∀ U, G U → IsAlphaSmall U κ) ∧
            G.IsCoproductFactorizationClass ∧
            ∀ j, G (L.obj (E j)) := by
  sorry

end CategoryTheory
