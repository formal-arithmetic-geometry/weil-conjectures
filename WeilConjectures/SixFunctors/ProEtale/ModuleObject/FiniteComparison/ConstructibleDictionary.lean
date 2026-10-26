/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstantRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible étale complexes as condensed constructible complexes

Let `T` be a finite discrete commutative ring and `Φ = ProEtale.finiteCoefficientModEquivalence`
the equivalence between module objects over `Λ_X = p_X^* T̲` and sheaves of `T`-modules on
`X_proét`. This file shows that the condensed reading `Φ⁻¹ (ν^* -)` of constructible étale sheaves
and complexes is constructible:

* `ProEtale.isLocallyFinitelyPresented_inverse_obj_comparisonUpperStar_obj`: for a finite
  locally constant étale sheaf `H`, the module object `Φ⁻¹ (ν^* H)` is pro-étale locally
  finitely presented. An étale cover trivialising `H` is a pro-étale cover; on a (nonempty)
  member `U`, `ν^* H` restricts to the constant sheaf of a finite `T`-module, and `Φ⁻¹` of such
  a constant sheaf is finitely presented
  (`ProEtale.isFinitelyPresented_finiteCoefficientModEquivalence_inverse_obj_constantSheaf`),
  `Φ⁻¹` commuting with pullback (`ProEtale.finiteCoefficientModUpperStarInverseIso`).
* `ProEtale.isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj`: for a
  constructible étale sheaf `G`, `Φ⁻¹ (ν^* G)` is constructible, on the strata of a
  stratification for `G`.
* `ProEtale.CondensedRing.boundedConstructibleOfEtale`: for a bounded constructible étale
  complex `N` of `𝒪_E ⧸ ℓⁿ`-modules, `Φ⁻¹ (ν^* N)` is bounded constructible
  (`ProEtale.CondensedRing.BoundedConstructibleOfEtale`); `ν^*` and `Φ⁻¹` are exact, so they
  commute with the cohomology sheaves.

The changes of ring objects between `(g)^*[Ab] Λ_Y` and `Λ_X` are handled by restriction of
scalars along the isomorphism `α_g`
(`ProEtale.CondensedRing.isLocallyFinitelyPresented_mapMod_iff`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-- A family of étale morphisms covering `X` is a pro-étale cover. -/
def etaleCoverToProetaleCover {X : Scheme.{u}} (𝒰 : Cover.{u} etalePrecoverage X) :
    Cover.{u} proetalePrecoverage X where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := etalePrecoverage_le_proetalePrecoverage _ 𝒰.mem₀

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **`Φ⁻¹` commutes with pullback**: `g^*⟦T̲⟧ (Φ_Y⁻¹ P) ≅ Φ_X⁻¹ (g^* P)`, for
`Φ = finiteCoefficientModEquivalence` (`upperStarFiniteCoefficientModEquivalenceIso`). -/
noncomputable def finiteCoefficientModUpperStarInverseIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :
    (g)^*⟦Profinite.continuousMapRingObj T⟧.obj
        ((finiteCoefficientModEquivalence Y T).inverse.obj P) ≅
      (finiteCoefficientModEquivalence X T).inverse.obj
        ((g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj P) :=
  (finiteCoefficientModEquivalence X T).unitIso.app _ ≪≫
    (finiteCoefficientModEquivalence X T).inverse.mapIso
      ((upperStarFiniteCoefficientModEquivalenceIso g T).app _ ≪≫
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].mapIso
          ((finiteCoefficientModEquivalence Y T).counitIso.app P))

omit [DiscreteTopology T] [Finite T] in
/-- If `g^*⟦T̲⟧ M` is finitely presented over `Λ_X`, then the sheaf pullback `g^* M` is finitely
presented over `g^* Λ_Y`, the two differing by restriction of scalars along `α_g`. -/
lemma isFinitelyPresented_mapMod_of_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)}
    (h : Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ((g)^*⟦Profinite.continuousMapRingObj T⟧.obj M)) :
    Mod.IsFinitelyPresented
      ((g)^*[Ab.{u + 1}].obj (condensedRingObj (Profinite.continuousMapRingObj T) Y))
      (((g)^*[Ab.{u + 1}].mapMod _).obj M) :=
  (h.comap (condensedPullbackHom _ g)).of_iso (comapUpperStarObjIso _ g M)

/-- On a nonempty `U` étale over `Y` over which a finite étale sheaf `H` becomes constant, the
pullback of the condensed reading `Φ⁻¹ (ν^* H)` is finitely presented: it is `Φ⁻¹` of the
constant sheaf of a finite `T`-module. -/
lemma isFinitelyPresented_upperStar_inverse_obj_comparisonUpperStar_obj {U Y : Scheme.{u}}
    (f : U ⟶ Y) [Nonempty U]
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)))
    [IsFiniteSheaf
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) H]
    (hc : ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).obj H).IsConstant
      U.smallEtaleTopology) :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) U)
      ((f)^*⟦Profinite.continuousMapRingObj T⟧.obj
        ((finiteCoefficientModEquivalence Y T).inverse.obj
          ((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj H))) := by
  obtain ⟨M, ⟨e⟩⟩ :=
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).obj H).mem_essImage_of_isConstant
  have : IsFiniteSheaf
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M)
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj M) :=
    have := IsFiniteSheaf.upperStar
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) f H
    IsFiniteSheaf.of_iso
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) e.symm
  have : Module.Finite (ULift.{u + 1} T) M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := U) M
  exact (isFinitelyPresented_finiteCoefficientModEquivalence_inverse_obj_constantSheaf
    U T M).of_iso (finiteCoefficientModUpperStarInverseIso T f _ ≪≫
      (finiteCoefficientModEquivalence U T).inverse.mapIso
        ((comparisonUpperStarCompUpperStarIso _ f).app H ≪≫
          (ν^*(U)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).mapIso e.symm ≪≫
          (comparisonUpperStarConstantSheafIso (ULift.{u + 1} T) U).app M)).symm

/-- **The condensed reading of a finite locally constant étale sheaf is locally finitely
presented**: an étale cover trivialising `H` is a pro-étale cover, and on its nonempty members
`ν^* H` is the constant sheaf of a finite `T`-module. -/
lemma isLocallyFinitelyPresented_inverse_obj_comparisonUpperStar_obj {Y : Scheme.{u}}
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)))
    [IsFiniteLocallyConstantSheaf
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) H] :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) Y)
      ((finiteCoefficientModEquivalence Y T).inverse.obj
        ((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj H)) := by
  obtain ⟨⟨𝒰₀, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := H)
  let 𝒰 := etaleCoverToProetaleCover 𝒰₀.nonemptyMembers
  refine ⟨𝒰, fun i ↦ isFinitelyPresented_mapMod_of_upperStar T (𝒰.f i) ?_⟩
  have : Nonempty (𝒰.X i) := i.2
  exact isFinitelyPresented_upperStar_inverse_obj_comparisonUpperStar_obj T (𝒰.f i) H
    ((isConstant_over_iff_upperStar _ (𝒰₀.etalePrecoverageToEtale i.1) H).mp (h𝒰 i.1))


/-- **The condensed reading of a constructible étale sheaf is constructible**: on the strata of a
stratification for `G`, it is the condensed reading of a finite locally constant sheaf. -/
lemma isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)))
    [IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
      (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) G] :
    IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj T) X)
      ((finiteCoefficientModEquivalence X T).inverse.obj
        ((ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj G)) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M →ₗ[ULift.{u + 1} T] N)
    (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} T) ↦ M) (F := G)
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff _ _ _).2 ?_⟩
  have := hS a
  exact (isLocallyFinitelyPresented_inverse_obj_comparisonUpperStar_obj T _).of_iso
    (finiteCoefficientModUpperStarInverseIso T (S.immersion a) _ ≪≫
      (finiteCoefficientModEquivalence (S.domain a) T).inverse.mapIso
        ((comparisonUpperStarCompUpperStarIso _ (S.immersion a)).app G)).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **Constructible étale complexes are read from bounded constructible condensed ones**: for a
bounded constructible étale complex `N` of `𝒪_E ⧸ ℓⁿ`-modules on `X`, the condensed complex
`Φ⁻¹ (ν^* N)` is bounded constructible. The exact functors `ν^*` and `Φ⁻¹` preserve boundedness
and commute with the cohomology sheaves, and the condensed reading of a constructible étale sheaf
is constructible (`ProEtale.isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj`). -/
theorem boundedConstructibleOfEtale (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : BoundedConstructibleOfEtale ℓ E n X := by
  intro N hN
  refine ⟨Functor.bounded_mapDerivedCategory_obj _
    ((ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).bounded_mapDerivedCategory_obj
      hN.1), fun i ↦ ?_⟩
  have : IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ i).obj N) := hN.2 i
  exact (isConstructibleModuleObject_inverse_obj_comparisonUpperStar_obj
    (PadicAlgCl.integersModPow ℓ E n) _).of_iso
    ((finiteCoefficientModEquivalence X.left _).inverse.mapIso
      ((Functor.mapDerivedCategoryHomologyFunctorIso
        (ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])
        i).app N) ≪≫
      (((finiteCoefficientModEquivalence X.left
        (PadicAlgCl.integersModPow ℓ E n)).inverse.mapDerivedCategoryHomologyFunctorIso i).app _))

end AlgebraicGeometry.ProEtale.CondensedRing
