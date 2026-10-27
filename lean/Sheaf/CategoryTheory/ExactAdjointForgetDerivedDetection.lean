module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Exact adjoint forgetting and detection on unbounded derived categories

Source: Stacks Project, Tags 015Z, 08BJ, 015F and 05RT; the detection argument in
`WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebraComp.lean`,
`isIso_of_isIso_forget_mapDerivedCategory_map`
(blueprint: lem-sf-exact-adjoint-forget-derived-detection).
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- An exact conservative right adjoint with exact left adjoint preserves injectives
and K-injectives, and its termwise unbounded derived functor is conservative and
triangulated. The cohomology comparison is the inverse of the existing normalized
comparison, with its kernel/image/quotient formula on representatives. Naturality of
this isomorphism covers all chain maps and all localized morphisms; termwise application
also preserves homotopies. The final isomorphism is the existing single-degree comparison
(`singleFunctor` puts the object in the specified cohomological degree).

Source: Stacks Tags 015Z, 08BJ, 015F and 05RT; generalized detection argument in
`IsoAlgebraComp.isIso_of_isIso_forget_mapDerivedCategory_map`
(blueprint: lem-sf-exact-adjoint-forget-derived-detection).

Proof plan:
1. Apply `lem-sp-right-adjoint-preserves-injectives` to the exact left adjoint F.
   Apply `lem-weil-pbc-right-adjoint-preserves-kinjective` with u = U and v = F:
   adjunction transports a map from an acyclic complex to a map from its exact F-image,
   whose null-homotopy exists by K-injectivity, and transports that homotopy back.
2. `lem-sf-exact-functor-derived-triangulated` supplies U.mapDerivedCategory, its
   triangulated structure and shift compatibility, and mapDerivedCategorySingleFunctor.
   No injective resolution or boundedness hypothesis is used.
3. Apply `lem-pur-exact-derived-cohomology-coherence` with F = U and G the identity.
   Invert its normalized theta to obtain chi. The representative formula below is
   mapDerivedCategoryHomologyFunctorIso_hom_app_Q. Naturality descends through Q and Qh,
   so it applies to chain maps and localized morphisms independently of representatives.
   Applying additive U to f - g = dh + hd gives the homotopy equation for their images.
4. If D(U)(f) is invertible, its cohomology maps are invertible. Naturality of chi
   conjugates them to U(H^r(f)). Conservativity of U gives invertibility of H^r(f)
   in every integer degree. Apply `lem-weil-pbc-unbounded-derived-iso-cohomology`
   (`DerivedCategory.isIso_iff`) to conclude that f is invertible.
-/
theorem exactAdjointForgetDerivedDetection
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) (U : B ⥤ A) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (_adj : F ⊣ U) [U.ReflectsIsomorphisms] :
    U.PreservesInjectiveObjects ∧ U.PreservesKInjectiveComplexes ∧
    U.mapDerivedCategory.IsTriangulated ∧ U.mapDerivedCategory.ReflectsIsomorphisms ∧
    (∀ r : ℤ, ∃ chi : U.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor A r ≅
        DerivedCategory.homologyFunctor B r ⋙ U,
      chi = (U.mapDerivedCategoryHomologyFunctorIso r).symm ∧
      ∀ K : CochainComplex B ℤ,
        chi.inv.app (DerivedCategory.Q.obj K) =
          U.map ((DerivedCategory.homologyFunctorFactors B r).hom.app K) ≫
            (U.mapHomologicalComplexHomologyIso (.up ℤ) r).inv.app K ≫
            (DerivedCategory.homologyFunctorFactors A r).inv.app
              ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
            (DerivedCategory.homologyFunctor A r).map
              (U.mapDerivedCategoryFactors.inv.app K)) ∧
    (∀ (K L : CochainComplex B ℤ) (f g : K ⟶ L), Homotopy f g →
      Nonempty (Homotopy ((U.mapHomologicalComplex (.up ℤ)).map f)
        ((U.mapHomologicalComplex (.up ℤ)).map g))) ∧
    (∀ (K L : DerivedCategory B) (f : K ⟶ L), IsIso (U.mapDerivedCategory.map f) →
      (∀ r : ℤ, IsIso (U.map ((DerivedCategory.homologyFunctor B r).map f))) ∧
      (∀ r : ℤ, IsIso ((DerivedCategory.homologyFunctor B r).map f)) ∧ IsIso f) ∧
    (∀ r : ℤ, ∃ sigma : DerivedCategory.singleFunctor B r ⋙ U.mapDerivedCategory ≅
        U ⋙ DerivedCategory.singleFunctor A r,
      sigma = U.mapDerivedCategorySingleFunctor r) := by
  have detect (K L : DerivedCategory B) (f : K ⟶ L)
      (hf : IsIso (U.mapDerivedCategory.map f)) :
      (∀ r : ℤ, IsIso (U.map ((DerivedCategory.homologyFunctor B r).map f))) ∧
      (∀ r : ℤ, IsIso ((DerivedCategory.homologyFunctor B r).map f)) ∧ IsIso f := by
    have hU (r : ℤ) : IsIso (U.map ((DerivedCategory.homologyFunctor B r).map f)) :=
      (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso r) f).2
        (by change IsIso ((DerivedCategory.homologyFunctor A r).map
              (U.mapDerivedCategory.map f)); infer_instance)
    have hB (r : ℤ) : IsIso ((DerivedCategory.homologyFunctor B r).map f) :=
      isIso_of_reflects_iso _ U
    exact ⟨hU, hB, (DerivedCategory.isIso_iff B f).2 hB⟩
  refine ⟨_adj.preservesInjectiveObjects_of_preservesFiniteLimits,
    _adj.preservesKInjectiveComplexes, inferInstance, ?_, ?_, ?_, detect, ?_⟩
  · exact ⟨fun {K L} f hf ↦ (detect K L f hf).2.2⟩
  · intro r
    refine ⟨(U.mapDerivedCategoryHomologyFunctorIso r).symm, rfl, ?_⟩
    intro K
    exact U.mapDerivedCategoryHomologyFunctorIso_hom_app_Q r K
  · intro K L f g h
    exact ⟨U.mapHomotopy h⟩
  · intro r
    exact ⟨U.mapDerivedCategorySingleFunctor r, rfl⟩

end CategoryTheory.Functor
