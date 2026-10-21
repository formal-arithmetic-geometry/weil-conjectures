module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The degree-zero category of a cohomology-stable derived subcategory

Source: blueprint main-20261015, `sec-six-functors-basics`,
`sk-lem-int-integral-heart-triangulated.proof.md`, paragraph (2)
(blueprint: lem-sfb-derived-degree-zero-abelian-criterion).

The full subcategory in the abelian category is the existing Mathlib object property
`T.inverseImage (singleFunctor A 0)`. The restricted single functor is its canonical
`ObjectProperty.lift`. No auxiliary notion or choice of a cone is introduced.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The degree-zero objects of a strictly full, cohomology-stable triangulated subcategory
form an abelian subcategory with ambient kernels, cokernels, finite biproducts and extensions.
The cone identifications commute with the connecting and cohomology maps, and hence are the
canonical identifications relative to the given distinguished triangle.

Source: blueprint main-20261015, `sk-lem-int-integral-heart-triangulated.proof.md`,
paragraph (2) (blueprint: lem-sfb-derived-degree-zero-abelian-criterion).

Proof plan:
1. Functoriality and strict fullness give isomorphism closure of the inverse-image property.
   The single complex of zero is zero, giving its zero object.
2. The single functor is fully faithful by lem-weil-pbc-derived-single-fully-faithful.
   Fullness of both subcategories gives full faithfulness of its restriction. Single-complex
   cohomology and lem-sf-derived-concentrated-single identify the essential image: a complex
   with cohomology only in degree zero is isomorphic to the single of its zeroth cohomology,
   which belongs to the subcategory by the cohomology-closure hypothesis.
3. Rotate the specified cone triangle. Shift and extension closure of T imply that its cone
   belongs to T (def-weil-triangulated-category, def-weil-triangulated-subcategory).
4. By lem-sf-derived-homology-long-exact the triangle gives the exact sequence
   0 -> H^{-1}(D) -> M -> N -> H^0(D) -> 0. The first and last maps are a kernel and a
   cokernel, respectively, so their universal properties give the displayed isomorphisms
   and equations. Cohomology closure and strict fullness place all ambient kernels and
   cokernels in the inverse-image property (def-weil-pbc-exact-sequence).
5. A short exact sequence in A yields a short exact sequence of single complexes, hence a
   distinguished triangle by lem-weil-pbc-complex-ses-triangle. Extension closure of T gives
   extension closure of the inverse-image property.
6. Apply extension closure to the split short exact sequence of a binary biproduct. Together
   with zero and isomorphism closure this gives every finite ambient biproduct, equivalently
   finite product (def-sp-abelian, def-weil-pbc-exact-sequence).
7. Apply lem-weil-pbc-abelian-full-subcategory-exact to the zero, kernel, cokernel and finite
   product closures. It gives abelianness with inherited addition and ambient kernels and
   cokernels. No boundedness or pre-existing t-structure on T is used. -/
theorem degreeZero_abelian_criterion
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : ObjectProperty (DerivedCategory A))
    [T.IsTriangulated] [T.IsClosedUnderIsomorphisms]
    (hcohomology : ∀ (K : DerivedCategory A), T K → ∀ q : ℤ,
      T ((singleFunctor A 0).obj ((homologyFunctor A q).obj K))) :
    (T.lift ((T.inverseImage (singleFunctor A 0)).ι ⋙ singleFunctor A 0)
      (fun M => M.property)).Full ∧
    (T.lift ((T.inverseImage (singleFunctor A 0)).ι ⋙ singleFunctor A 0)
      (fun M => M.property)).Faithful ∧
    (∀ K : T.FullSubcategory,
      (∃ M : (T.inverseImage (singleFunctor A 0)).FullSubcategory,
        Nonempty ((singleFunctor A 0).obj M.obj ≅ K.obj)) ↔
      ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor A q).obj K.obj)) ∧
    (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory)
      (f : M ⟶ N) (D : DerivedCategory A)
      (g : (singleFunctor A 0).obj N.obj ⟶ D)
      (h : D ⟶ ((singleFunctor A 0).obj M.obj)⟦(1 : ℤ)⟧),
      Triangle.mk ((singleFunctor A 0).map f.hom) g h ∈ distTriang (DerivedCategory A) →
      ∃ (eK : kernel f.hom ≅ (homologyFunctor A (-1)).obj D)
        (eC : cokernel f.hom ≅ (homologyFunctor A 0).obj D),
        eK.hom ≫
            HomologySequence.δ (Triangle.mk ((singleFunctor A 0).map f.hom) g h) (-1) 0 ≫
            (singleFunctorCompHomologyFunctorIso A 0).hom.app M.obj = kernel.ι f.hom ∧
        (singleFunctorCompHomologyFunctorIso A 0).inv.app N.obj ≫
            (homologyFunctor A 0).map g = cokernel.π f.hom ≫ eC.hom ∧
        (T.inverseImage (singleFunctor A 0)) (kernel f.hom) ∧
        (T.inverseImage (singleFunctor A 0)) (cokernel f.hom)) ∧
    (T.inverseImage (singleFunctor A 0)).ContainsZero ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderFiniteProducts ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderKernels ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderCokernels ∧
    (∃ hB : Abelian (T.inverseImage (singleFunctor A 0)).FullSubcategory,
      hB.toPreadditive =
        Preadditive.fullSubcategory (T.inverseImage (singleFunctor A 0)) ∧
      (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory) (f : M ⟶ N),
        PreservesLimit (parallelPair f 0) (T.inverseImage (singleFunctor A 0)).ι) ∧
      (∀ (M N : (T.inverseImage (singleFunctor A 0)).FullSubcategory) (f : M ⟶ N),
        PreservesColimit (parallelPair f 0) (T.inverseImage (singleFunctor A 0)).ι)) ∧
    (T.inverseImage (singleFunctor A 0)).IsClosedUnderExtensions := by
  sorry

end DerivedCategory
