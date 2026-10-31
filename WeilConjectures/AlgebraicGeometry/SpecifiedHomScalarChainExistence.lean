/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final

/-! Existence of the normalized scalar Hom chain map.
Source: Stacks 0A8X, 08J9 (blueprint: lem-zl-specified-hom-scalar-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

theorem specifiedHomScalarChain_exists (X : Scheme.{u})
    (uE : 𝟭 (CochainComplex (integralTowerModules l E X) ℤ) ⟶
      coefficientHomResolution.{u, u + 1, u} (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X))
    (uL : 𝟭 (CochainComplex (integralTowerModules l L X) ℤ) ⟶
      coefficientHomResolution.{u, u + 1, u} (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l L X))
    (P I Q : CochainComplex (integralTowerModules l E X) ℤ)
    (_hP : integralOperationsGoodComplex l E X P)
    (_hQ : integralOperationsGoodComplex l E X Q) [I.IsKInjective]
    (_hM : sfIntegralConstructible l E X (DerivedCategory.Q.obj P))
    (_hN : sfIntegralConstructible l E X (DerivedCategory.Q.obj I))
    (q : Q ⟶ homComplex (R := completedIntegralCommRingSheafUnrestricted l E X) P I)
    [QuasiIso q] :
    ∃ δ : ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      homComplex (R := completedIntegralCommRingSheafUnrestricted l L X)
        (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P)
        ((coefficientHomResolution.{u, u + 1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X)).obj
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)),
      (∀ (r m : ℤ) (U : X.ProEtᵒᵖ) (x : (Q.X r).val.obj U) (y : (P.X m).val.obj U)
        (s b : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U),
        coefficientHomSectionEvaluation.{u, u + 1, u} (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l L X) _ _ _ δ r m (m+r) rfl U
          (integralOrdinaryTensorSection l E L ι X (Q.X r) U s x)
          (integralOrdinaryTensorSection l E L ι X (P.X m) U b y) =
        ((((uL).app
          (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj I)).f
          (m+r)).val.app U)
          (integralOrdinaryTensorSection l E L ι X (I.X (m+r)) U (s*b)
            (((((coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I r m (m+r) rfl).val.app U
                ((q.f r).val.app U x)).app
                  (op (CategoryTheory.Over.mk (𝟙 U.unop)))).hom) y))) ∧
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map δ =
        (integralOrdinaryDerivedScalar l E L ι X).map
          (DerivedCategory.Q.map q ≫
            DerivedCategory.Q.map
              ((homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E X)).obj
                (op P) |>.map ((uE).app I)) ≫
            (coefficientHomResolutionIso.{u, u + 1, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P I).inv) ≫
          scalarHomOrdinary l E L ι X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) ≫
          (integralDerivedInternalHom l L X).map (Prod.mkHom
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.inv.app P).op
            ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app I)) ≫
          (coefficientHomResolutionIso.{u, u + 1, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l L X) _ _).hom := by
  sorry

end WeilConjectures
