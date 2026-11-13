/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteAffineEtaleThickeningDecomposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtalePushforwardConstructible
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleSurjectiveDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Finite finitely presented pushforward preserves constructibility
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem constructible_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (IsConstructibleSheaf.upperStar f F)

private theorem constructible_of_iso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hF : IsConstructibleEtaleModuleSheaf F) : IsConstructibleEtaleModuleSheaf G := by
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    (IsConstructibleSheaf.of_iso e)

private theorem constructible_finite_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  have := (IsFinite.locallyQuasiFinite_and_quasiCompact f).1
  have hqf : Scheme.Hom.IsQuasiFinite f :=
    ⟨inferInstance, inferInstance, fun x ↦ isOpen_discrete _⟩
  obtain ⟨Y', hY', a, ha, Z, i, hi, hefin, heet⟩ :=
    exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite f hqf
      ⟨inferInstance, inferInstance, inferInstance⟩
  have := hY'
  have := ha
  have := hi.1
  have := hi.2
  have := hefin
  have := heet
  have : IsAffine (Limits.pullback f a) := isAffine_of_isAffineHom (Limits.pullback.snd f a)
  have : IsAffine Z := isAffine_of_isAffineHom i
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst f a)).obj F
  let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F'
  have hH : IsConstructibleEtaleModuleSheaf H :=
    constructible_pullback i F' (constructible_pullback (Limits.pullback.fst f a) F hF)
  have heH := isConstructibleEtaleModuleSheaf_lowerStar_of_finite_etale
    (i ≫ Limits.pullback.snd f a) H hH
  have : (Etale.upperStar (ModuleCat.{u + 1} Λ) i).IsEquivalence :=
    Etale.isEquivalence_upperStar_of_thickening (ModuleCat.{u + 1} Λ) i hi.2.surj
  -- Topological invariance makes the adjunction unit invertible for module sheaves.
  let unitIso : F' ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) i).obj H :=
    asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F')
  let compIso := (Etale.lowerStar (ModuleCat.{u + 1} Λ) (Limits.pullback.snd f a)).mapIso
    unitIso ≪≫ (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) i (Limits.pullback.snd f a)).app H
  have hf' := constructible_of_iso compIso.symm heH
  -- The finite exchange isomorphism has source a^*(f_*F).
  have hsq := IsPullback.of_hasPullback f a
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) hsq
  have hbc := constructible_of_iso
    (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq).app F)).symm hf'
  exact isConstructibleEtaleModuleSheaf_of_surjective_pullback a _ hbc

/-- Finite finitely presented pushforward preserves constructible module sheaves on qcqs
schemes over a finite commutative coefficient ring. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  obtain ⟨R, a, ha⟩ := (compactSpace_iff_exists (X := Y)).mp inferInstance
  have : Surjective a := ⟨ha⟩
  have : IsAffine (Limits.pullback f a) := isAffine_of_isAffineHom (Limits.pullback.snd f a)
  have hF' := constructible_pullback (Limits.pullback.fst f a) F hF
  have hpush := constructible_finite_affine (Limits.pullback.snd f a) _ hF'
  -- The finite exchange isomorphism has source a^*(f_*F).
  have hsq := IsPullback.of_hasPullback f a
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) hsq
  have hbc := constructible_of_iso
    (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq).app F)).symm hpush
  exact isConstructibleEtaleModuleSheaf_of_surjective_pullback a _ hbc

end AlgebraicGeometry.Scheme
