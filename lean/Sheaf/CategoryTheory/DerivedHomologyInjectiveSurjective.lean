module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

/-- Surjectivity half of the injective-target derived homology comparison.

Source: proof step 1 of `new-stage3-derived-homology-injective-bijective`.
Proof: represent a derived morphism by a map of complexes into the injective
complex concentrated in degree zero, lift a degree-zero homology map through
cycles using injectivity, and descend the resulting chain map. The statement
is isolated as the surjectivity half so that the remaining chain-level argument
can be developed independently.

(blueprint: new-stage3-derived-homology-injective-surjective) -/
theorem derived_homology_injective_surjective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Surjective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
        ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by sorry

end CategoryTheory
