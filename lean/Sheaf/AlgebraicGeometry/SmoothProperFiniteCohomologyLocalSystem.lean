/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q129, W9
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import Sheaf.AlgebraicGeometry.ConstructibleCospecializationLocalSystem
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperLocallyConstant
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-! # Smooth proper finite cohomology local systems

Source: Stacks Project, More on Etale Cohomology, Tag 0GLI,
`proposition-loc-cst-torsion`, specialized to the prime field
(blueprint: lem-sfb-smooth-proper-finite-cohomology-local-system).

The base is arbitrary. Local constant models and their isomorphisms are taken in the
module-valued sheaf category, so their linear structure is retained throughout.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Limits in
private theorem finiteLocalSystem_affine
    {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [Smooth f] [IsProper f]
    (ell : ℕ) [Fact ell.Prime]
    (hunit : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    [Scheme.IsFiniteLocallyConstantSheaf F] (q : ℤ) :
    Scheme.IsFiniteLocallyConstantSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let R := ULift.{u + 1} (ZMod ell)
  let A := ModuleCat.{u + 1} R
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let G := (DerivedCategory.Plus.homologyFunctor _ q).obj
    ((rightDerivedLowerStarPlus A f).obj K)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : Scheme.IsConstructibleSheaf F :=
    ⟨Scheme.Stratification.trivial X, fun _ ↦
      Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩
  have hK : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj K.obj) := by
    intro n
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    exact (DerivedCategory.boundedConstructible_singleFunctor_obj F 0).2 n
  have hR (a : R) (s : S) : IsUnit (addOrderOf a : S.presheaf.stalk s) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero
      (ULift.ext _ _ (by simp)))) (hunit s)
  have hC := isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
    R hR f (HasCompactification.compactification f) K hK q
  have : Scheme.IsConstructibleSheaf G := by
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((rightDerivedLowerShriekOfCompactification A
            (HasCompactification.compactification f)).obj K.obj)) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hC
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerShriekOfCompactification A
          (HasCompactification.compactification f)).obj K.obj))
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar A f).app K.obj) ≪≫
        homologyRightDerivedLowerStarSingleIsoPlus f F q)
  have hglobal : IsUnit (ell : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ ⊤
    intro s hs
    simpa only [map_natCast] using hunit s
  apply Scheme.isFiniteLocallyConstantSheaf_of_constructible_bijective_cospecialization G
  intro Ω _ _ s Ω' _ _ t
  apply Scheme.bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap s t G
  exact isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper
    R f ell (Fact.out : ell.Prime).ne_zero (CharP.cast_eq_zero R ell) hglobal F s t q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Higher direct images of finite prime-field local systems along a smooth proper
morphism are finite prime-field local systems, without a Noetherian base hypothesis.

Source: Stacks Project, More on Etale Cohomology, Tag 0GLI,
`proposition-loc-cst-torsion`
(blueprint: lem-sfb-smooth-proper-finite-cohomology-local-system).

`ULift (ZMod ell)` is the prime field in the coefficient universe. `Module.Finite`
expresses finite dimension over that field. The degree-zero single functor and the
bounded-below derived direct image implement the node's convention for `R^q f_* F`.

Proof:
1. Convert the given constant finite-module charts to the intrinsic finite locally
   constant predicate. Work first over an arbitrary affine base, so the proper source
   is quasi-compact and quasi-separated. The one-stratum partition makes `F` constructible.
2. Compact-support constructibility applied to `F[0]`, followed by the proper comparison
   between derived lower shriek and derived direct image, makes `H^q(Rf_* F[0])`
   constructible. The comparison between the two constructibility conventions preserves
   the module structure.
3. Smooth proper specialization makes every cospecialization map bijective. Apply the
   constructible cospecialization criterion over the arbitrary affine base. Its proof
   shrinks using constructible kernel and cokernel vanishing loci; no Noetherian
   approximation is necessary.
4. For the affine cover of an arbitrary base, proper base change and exact inverse image
   identify each restricted higher direct image with the higher direct image of the
   pulled-back local system. Finite local constancy glues along this cover. Convert back
   to the required constant finite-module charts.
-/
theorem finite_localSystem_higherDirectImage_smooth_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f]
    (ell : ℕ) [Fact ell.Prime]
    (hunit : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    (hF : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)),
        Module.Finite (ULift.{u + 1} (ZMod ell)) M ∧
          Nonempty (F.over (𝒰.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj M))
    (q : ℤ) (hq : 0 ≤ q) :
    ∃ 𝒱 : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ j : 𝒱.I₀,
      ∃ N : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)),
        Module.Finite (ULift.{u + 1} (ZMod ell)) N ∧
          Nonempty
            (((DerivedCategory.Plus.homologyFunctor _ q).obj
              ((rightDerivedLowerStarPlus
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).over
                  (𝒱.etalePrecoverageToEtale j) ≅
              (constantSheaf (S.smallEtaleTopology.over (𝒱.etalePrecoverageToEtale j))
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj N) := by
  have _hq : 0 ≤ q := hq
  let R := ULift.{u + 1} (ZMod ell)
  let A := ModuleCat.{u + 1} R
  obtain ⟨𝒰, h𝒰⟩ := hF
  let d : Scheme.LocallyConstantDatum F := ⟨𝒰, fun i ↦ by
    obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
    exact Sheaf.isConstant_of_iso _ e⟩
  have : Scheme.IsFiniteLocallyConstantSheaf F :=
    (Scheme.finite_locally_constant_module_values_iff F).1.mp ⟨d, fun i ↦ by
      obtain ⟨M, hM, e⟩ := h𝒰 i
      have := hM
      exact ⟨M, Module.finite_of_finite R, e⟩⟩
  let G := (DerivedCategory.Plus.homologyFunctor _ q).obj
    ((rightDerivedLowerStarPlus A f).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hlocal (i : S.affineCover.I₀) :
      Scheme.IsFiniteLocallyConstantSheaf ((upperStar A (S.affineCover.f i)).obj G) := by
    let a := S.affineCover.f i
    have : Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar A (Limits.pullback.fst f a)).obj F) :=
      Scheme.IsFiniteLocallyConstantSheaf.upperStar _ F
    have : Smooth (Limits.pullback.snd f a) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have := finiteLocalSystem_affine (Limits.pullback.snd f a) ell (fun x ↦ by
      simpa only [map_natCast] using (hunit (a x)).map (a.stalkMap x).hom)
      ((upperStar A (Limits.pullback.fst f a)).obj F) q
    have := isIso_baseChange_of_isProper_of_isAddTorsion_ring R
      isAddTorsion_of_finite (IsPullback.of_hasPullback f a)
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      (F := (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus A (Limits.pullback.snd f a)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar A (Limits.pullback.fst f a)).obj F))))
      ((((upperStar A a).mapDerivedCategoryPlusHomologyFunctorIso q).app
          ((rightDerivedLowerStarPlus A f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((baseChange A (IsPullback.of_hasPullback f a).toCommSq).app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
            (rightDerivedLowerStarPlus A (Limits.pullback.snd f a)).mapIso
              (((upperStar A (Limits.pullback.fst f a)).mapDerivedCategoryPlusSingleFunctor
                0).app F))).symm
  have : Scheme.IsFiniteLocallyConstantSheaf G :=
    Scheme.IsFiniteLocallyConstantSheaf.of_openCover S.affineCover G
  obtain ⟨e, he⟩ := (Scheme.finite_locally_constant_module_values_iff G).1.mpr
    (inferInstance : Scheme.IsFiniteLocallyConstantSheaf G)
  refine ⟨e.cover, fun i ↦ ?_⟩
  obtain ⟨M, hM, hE⟩ := he i
  have := hM
  exact ⟨M, Module.Finite.of_finite, hE⟩

end AlgebraicGeometry.Etale
