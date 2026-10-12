/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FiniteCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution

/-!
# Unbounded right derived functors of bounded amplitude preserve coproducts

Let `F : C ⥤ D` be a left exact additive functor out of a Grothendieck abelian category. The
classical right derived functors are the homology of the unbounded `R(F)` on objects placed in
degree `0`: `RᵖF(X) ≅ Hᵖ(R(F)(X[0]))`
(`CategoryTheory.Functor.rightDerivedObjIsoHomologyRightDerivedFunctorObj`).

Consequently, if `Hᵖ(R(F)(X[0])) = 0` for all `p > N` and all objects `X`, then `F` has right
cohomological dimension at most `N`, and if moreover `F` preserves coproducts and coproducts of
injective objects are `F`-acyclic, then `R(F)` preserves coproducts on the unbounded derived
category (`CategoryTheory.Functor.preservesColimitsOfShape_discrete_rightDerivedFunctor_of_isZero`).
-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- The classical right derived functors are the homology of the unbounded right derived
functor on objects placed in degree `0`: `RᵖF(X) ≅ Hᵖ(R(F)(X[0]))`. -/
noncomputable def rightDerivedObjIsoHomologyRightDerivedFunctorObj (X : C) (p : ℕ) :
    (F.rightDerived p).obj X ≅ (DerivedCategory.homologyFunctor D p).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)) :=
  ((injectiveResolution X).kInjectiveResolution.rightDerivedHomologyIsoRightDerived F p).symm ≪≫
    ((injectiveResolution X).kInjectiveResolution.homologyRightDerivedFunctorObjIso F p).symm ≪≫
    (DerivedCategory.homologyFunctor D p).mapIso
      (F.rightDerivedFunctor.mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).symm)

/-- If the homology of `R(F)(X[0])` vanishes above `N` for every `X`, then `F` has right
cohomological dimension at most `N`. -/
lemma hasRightCohomologicalDimensionLE_of_isZero (N : ℕ)
    (h : ∀ (X : C) (p : ℤ), (N : ℤ) < p → IsZero ((DerivedCategory.homologyFunctor D p).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)))) :
    F.HasRightCohomologicalDimensionLE N := fun q X hq ↦
  (h X q (by exact_mod_cast hq)).of_iso (F.rightDerivedObjIsoHomologyRightDerivedFunctorObj X q)

/-- **Coproducts and right derived functors of bounded amplitude.** Let `F` be left exact,
preserve coproducts of shape `J`, let coproducts of injective objects be `F`-acyclic, and let
`Hᵖ(R(F)(X[0])) = 0` for all `p > N` and all objects `X`. Then the unbounded right derived
functor `R(F)` preserves coproducts of shape `J`. -/
theorem preservesColimitsOfShape_discrete_rightDerivedFunctor_of_isZero
    [IsGrothendieckAbelian.{w} C] [PreservesFiniteLimits F] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [Abelian.HasKInjectiveResolutions D] [PreservesColimitsOfShape (Discrete J) F] (N : ℕ)
    (h : ∀ (X : C) (p : ℤ), (N : ℤ) < p → IsZero ((DerivedCategory.homologyFunctor D p).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X))))
    (hsum : ∀ (G : Discrete J ⥤ C), (∀ j, Injective (G.obj j)) → ∀ (c : Cocone G),
      IsColimit c → F.rightAcyclic c.pt) :
    PreservesColimitsOfShape (Discrete J) F.rightDerivedFunctor :=
  PreservesAcyclicityOfRightAcyclic.preservesColimitsOfShape_discrete_rightDerivedFunctor.{w} J
    ((F.hasRightCohomologicalDimensionLE_of_isZero N h).preservesAcyclicityOfRightAcyclic) hsum

end Functor

end CategoryTheory
