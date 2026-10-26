/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LocallyFiniteConstant

/-!
# Constructible finite-coefficient module objects are of étale origin

TODO
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- A constructible module object over `Λ_X = p_X^* T̲`, for a finite discrete ring `T`, is a
constructible sheaf of `T`-modules on `X_proét` (blueprint `def-weil-finite-torsion-constructibility`):
on the strata, the pro-étale local finite presentations `Λ^m ⟶ Λ^n` become constant matrices over
a refinement of the covers, whose cokernels are constant sheaves of finite `T`-modules. -/
theorem isConstructible_finiteCoefficientModEquivalence_functor_obj
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (hN : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj T) X) N) :
    IsConstructible (ULift.{u + 1} T) ((finiteCoefficientModEquivalence X T).functor.obj N) := by
  obtain ⟨S, hS⟩ := hN
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  exact isFiniteLocallyConstant_of_iso
    (finiteCoefficientModEquivalenceUpperStarIso (S.immersion a) N).symm
    (isFiniteLocallyConstant_finiteCoefficientModEquivalence_functor_obj 𝒰 fun i ↦
      CondensedRing.isFinitelyPresented_upperStar_of_comap_iso _ (𝒰.f i)
        (condensedPullbackHom _ (S.immersion a))
        (CondensedRing.comapUpperStarObjIso _ (S.immersion a) N) (h𝒰 i))

/-- The image of a bounded constructible complex of module objects over `Λ_X` under the derived
comparison `finiteCoefficientDerivedEquivalence` is bounded below of étale origin. -/
theorem plusEtaleOrigin_finiteCoefficientDerivedEquivalence_functor_obj
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) A) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj A) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hA
  refine DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology _ _ (fun n ↦ ?_)
    ⟨⟨a, (finiteCoefficientModEquivalence X T).functor.isGE_mapDerivedCategory_obj A a⟩,
      ⟨b, (finiteCoefficientModEquivalence X T).functor.isLE_mapDerivedCategory_obj A b⟩⟩
  obtain ⟨G, -, ⟨e⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
    (isConstructible_finiteCoefficientModEquivalence_functor_obj (hc n))
  exact ⟨G, ⟨e ≪≫
    ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategoryHomologyFunctorIso n).app A⟩⟩

end AlgebraicGeometry.ProEtale
