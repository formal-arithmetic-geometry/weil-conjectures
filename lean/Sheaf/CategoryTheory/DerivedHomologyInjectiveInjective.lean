module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

/-- Injectivity half of the injective-target derived homology comparison.

Source: proof step 1 of `new-stage3-derived-homology-injective-bijective`.
Proof: if a chain map into the injective complex concentrated in degree zero
induces zero on degree-zero homology, its degree-zero component factors through
the image of the preceding differential; injectivity extends this factor to a
null homotopy. Transporting across the derived localization gives equality of
the original morphisms. The statement is isolated as the injectivity half.

(blueprint: new-stage3-derived-homology-injective-injective) -/
theorem derived_homology_injective_injective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Injective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
        ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by sorry

end CategoryTheory
