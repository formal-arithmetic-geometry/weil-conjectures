module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

@[expose] public section
set_option autoImplicit false
universe u v w w'
open CategoryTheory
namespace DerivedCategory

/-- The remaining comparison step upgrades unmarked lifting data to the prescribed marking.
Source: Stacks Project, More on Algebra, Tag 0BCA, the cone-coordinate homotopy.
(blueprint: lem-weil-pbc-nilpotent-marked-free-complex-lift-marking)
Assuming the bounded finite-free lift has already been constructed, the cone comparison
and its explicit contracting homotopy identify its derived reduction with the specified
isomorphism. The proof is deferred as a separate comparison item so the construction
and the marking calculation can be developed independently.
-/
theorem exists_marking_compatible_finiteFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F)
    (hdata : ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i))) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      L.map β.hom ≫ α.hom =
        L.map ((quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        Qh.map ((@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk I))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
          (.up ℤ)).hom.app P) ≫
        (quotientCompQhIso (ModuleCat.{max u v} (R ⧸ I))).hom.app _ ≫
        Q.map θ.hom := by
  sorry

end DerivedCategory
