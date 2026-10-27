module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Sheaf.CategoryTheory.WeakSerrePresentableCardinalPackage
import Sheaf.CategoryTheory.PresentableSubcomplexLeftExtension
import Sheaf.SixFunctorsBasics.SetGeneratedDerivedOrthogonalTriangle

/-! # Small localizing generators for a Grothendieck weak-Serre derived subcategory

Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, Appendix A, Theorem A.3 and its proof,
with Lemma A.1 and Remark A.2 identifying the localizing hull of the detecting family.
(blueprint: lem-sfb-weak-serre-derived-small-generators)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

/-- The derived objects with cohomology in a coproduct-closed Grothendieck weak-Serre
subcategory have a small family of localizing generators. The final clauses give the
universal property of the smallest full replete triangulated subcategory closed under
ambient small coproducts; `homologyProperty A` means membership in `A` in every degree.

Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, Appendix A, Theorem A.3, its proof,
Lemma A.1 and Remark A.2. (blueprint: lem-sfb-weak-serre-derived-small-generators)

Proof:
1. `lem-sbc-cohomology-in-weak-serre-subcategory` gives triangulatedness and
repleteness. Coproducts of complexes compute derived coproducts by
`lem-kun-grothendieck-derived-coproducts`. Exactness of coproducts in the Grothendieck
category, `lem-weil-pbc-kinjective-functorial-existence` and
`src-weil-derived-homology-preserves-coproducts` identify their cohomology with the
coproduct of the cohomologies. Thus the indicated property is closed under all small
ambient coproducts, including the empty family.
2. Choose the common uncountable regular presentability cardinal from
`lem-sfb-weak-serre-presentable-cardinal-package`. Its Serre closure, common
presentables, filtered-subobject density and small epimorphism lifts give the
hypotheses of the one-degree extension lemma.
3. Choose a small skeleton of the ambient presentables. Bounded-above complexes
on this skeleton with cohomology in the subcategory form a small set: their data
are countable sequences of objects and differentials in small Hom sets, subject
to the complex equations. Their derived images form a small family in the property.
4. For a nonzero derived object in the property, choose a degree with nonzero
cohomology. Density supplies a nonzero presentable subobject of that cohomology.
The small epimorphism lift supplies a presentable subobject of cycles mapping
onto it, initializing a bounded-above partial subcomplex in that degree.
5. Apply `lem-sfb-presentable-subcomplex-left-extension` successively to the left,
retaining earlier terms and differentials. Countable dependent choice gives a
bounded-above presentable subcomplex whose cohomology lies in the subcategory.
Its map to the original complex is nonzero on the chosen cohomology, so the small
family in step 3 detects every nonzero object of the property.
6. Its localizing hull lies in the property by step 1. For any object of the property,
`lem-sfb-set-generated-derived-orthogonal-triangle` gives a triangle with first
vertex in the hull and third vertex right orthogonal to it. The third vertex is
still in the property. Detection forces it to be zero, so the first arrow is an
isomorphism. Repleteness puts the original object in the hull, proving minimality. -/
theorem weakSerre_derived_small_generators
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{v} B]
    (A : ObjectProperty B) [A.IsClosedUnderIsomorphisms] [A.ContainsZero]
    [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels] [A.IsClosedUnderExtensions]
    [Abelian A.FullSubcategory] [IsGrothendieckAbelian.{v} A.FullSubcategory]
    (hcoprod : ∀ I : Type v, A.IsClosedUnderColimitsOfShape (Discrete I)) :
    ∃ (I : Type v) (P : I → DerivedCategory B),
      (∀ i : I, DerivedCategory.homologyProperty A (P i)) ∧
      (DerivedCategory.homologyProperty A).IsClosedUnderIsomorphisms ∧
      (DerivedCategory.homologyProperty A).IsTriangulated ∧
      (∀ J : Type v,
        (DerivedCategory.homologyProperty A).IsClosedUnderColimitsOfShape (Discrete J)) ∧
      ∀ R : ObjectProperty (DerivedCategory B),
        (∀ i : I, R (P i)) → R.IsClosedUnderIsomorphisms → R.IsTriangulated →
        (∀ J : Type v, R.IsClosedUnderColimitsOfShape (Discrete J)) →
        DerivedCategory.homologyProperty A ≤ R := by
  sorry

end CategoryTheory
