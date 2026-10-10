/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Stability of `Dctf`: finite coefficients and open immersions

For a finite coefficient ring `Λ`, this file shows that the derived tensor product and the
extension by zero `Rf_!` preserve `Dctf`, computes `Rj_!` and `Rj^!` along an open immersion,
and constructs the descended functors `Lf^*`, `Rf_!` and `𝔻_X` between the categories `Dctf`.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### The derived tensor product at a finite coefficient ring -/

section Tensor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-sf-tor-sheaf-constructible`: Tor sheaves of constructible sheaves.

For a finite ring `Λ` and constructible sheaves `F` and `G` of `Λ`-modules on `X_ét`, every
homology sheaf of `F ⊗ᴸ G` is constructible: on a common stratification both are locally
constant, and on a cover where both are constant `Hʳ(F ⊗ᴸ G)` is the constant sheaf
`Tor_{-r}(M, N)` of finite modules. -/
theorem isConstructibleSheaf_homology_tensor_singleFunctor {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] [IsConstructibleSheaf G] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
  sorry

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), constructibility: for a finite ring `Λ`, the derived tensor product of two
bounded constructible complexes, one of them of finite Tor amplitude, is bounded constructible.
Finite Tor amplitude of one factor is needed for boundedness: over `ℤ/ℓ²` on a point,
`ℤ/ℓ ⊗ᴸ ℤ/ℓ` has a nonzero `Tor_i` for every `i ≥ 0`. The coefficients cannot be an arbitrary
coefficient category: over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has the
non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ` in degree `-1`, although `R/(x)` has Tor
amplitude in `[-1, 0]`. -/
theorem boundedConstructible_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : finiteTorAmplitude (ModuleCat.{u + 1} Λ) X M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) :=
  have : IsNoetherianRing Λ := inferInstance
  ⟨bounded_derivedTensor_of_finiteTorAmplitude _ X hK.1 hMt,
    constructibleHomology_derivedTensor _ (fun F G hF hG n ↦ by
      have := (Etale.constructibleSheaf_iff _ _ _).mp hF
      have := (Etale.constructibleSheaf_iff _ _ _).mp hG
      exact (Etale.constructibleSheaf_iff _ _ _).mpr
        (isConstructibleSheaf_homology_tensor_singleFunctor Λ F G n)) hK hM⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (ii): `- ⊗ᴸ - : Dctf(X, Λ) × Dctf(X, Λ) ⥤ Dctf(X, Λ)` is defined, for a finite ring
`Λ`. The internal-Hom half of the clause is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`
below. -/
theorem constructibleFiniteTor_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) := by
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hMbc, c, d, hMt⟩ := hM
  exact ⟨boundedConstructible_tensor Λ X hKbc hMbc ⟨c, d, hMt⟩,
    a + c, b + d, torAmplitudeIn_tensor _ X a b c d hKt hMt⟩

end Tensor

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iv): `Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` is defined for every separated finite-type `f`
admitting a compactification. One assembles the open-immersion case
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`) with the proper
case, where `Rf_! = Rf_*`, along a compactification of `f`. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
    [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : constructibleFiniteTor A X K) :
    constructibleFiniteTor A Y ((R(f)_![A]).obj K) :=
  sorry

/-! ### Open immersions -/

section OpenImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U Y : Scheme.{u}} (j : U ⟶ Y)
  [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j]

/-- The derived lower shriek along a quasi-compact open immersion `j` is extension by zero,
`Rj_! ≅ D(j_!)`: it is computed by the compactification `U ⟶[j] Y ⟶[𝟙] Y`, and `Rj_!` does not
depend on the compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). -/
noncomputable def rightDerivedLowerShriekIsoOfIsOpenImmersion :
    R(j)_![ModuleCat.{u + 1} Λ] ≅ D((j)_!open[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerShriekIso Λ (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft D((j)_!open[ModuleCat.{u + 1} Λ])
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _

/-- Blueprint `sk-lem-sf-open-ctf`: Extension by zero preserves the finite-Tor constructible
category.

For a quasi-compact open immersion `j : U ⟶ Y` admitting a compactification and a finite ring
`Λ`, extension by zero sends `Dctf(U, Λ)` into `Dctf(Y, Λ)` *without moving the interval*: if
`K` is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`, then so is `Rj_! K`. Indeed `Rj_! = j_!` is exact, the extension by zero of a
constructible sheaf is constructible, and `j_!K ⊗ᴸ F ≅ j_!(K ⊗ᴸ j^*F)` by the projection
formula. -/
theorem constructibleTorAmplitudeIn_rightDerivedLowerShriek (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  let F := (j)_!open[ModuleCat.{u + 1} Λ]
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app K).symm ⟨⟨⟨?_, fun n ↦ ?_⟩,
      F.homologyConcentratedIn_mapDerivedCategory_obj hab⟩, fun G ↦ ?_⟩
  · exact F.bounded_mapDerivedCategory_obj hbc.1
  · have := hbc.2 n
    have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n ⋙ F).obj K) :=
      IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
        j.range_closedComplement ((_root_.DerivedCategory.homologyFunctor _ n).obj K)
    exact IsConstructibleSheaf.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
  · -- `j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)`
    have e := (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).app
      K).app ((_root_.DerivedCategory.singleFunctor _ 0).obj G)).symm ≪≫
      F.mapDerivedCategory.mapIso (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) j).app G))
    obtain ⟨h₁, h₂⟩ := F.homologyConcentratedIn_mapDerivedCategory_obj (hta ((j)^*[_].obj G))
    have : _root_.DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) a := h₁
    have : _root_.DerivedCategory.TStructure.t.IsLE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) b := h₂
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- For a quasi-compact open immersion `j`, the exceptional inverse image is the restriction,
`Rj^! ≅ D(j^*)`: both are right adjoint to `Rj_! ≅ D(j_!)`. -/
noncomputable def rightDerivedUpperShriekIsoOfIsOpenImmersion :
    R(j)^![ModuleCat.{u + 1} Λ] ≅ D((j)^*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) j).rightAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoLeft
      (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).symm)

/-- Blueprint `sk-prop-sf-rf-shriek-preservation`: Preservation for the exceptional inverse
image.

Clause (i), open-immersion case: for a quasi-compact open immersion `f` and a finite ring `Λ`,
`Rf^!` preserves the constructible interval and the Tor amplitude *unchanged*, the right adjoint
of `Rf_! ≅ f_!` being the exact functor `f^*`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b
      ((R(j)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm ⟨⟨?_,
      ((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab⟩, ?_⟩
  · exact hbc.mapDerivedCategory_upperStar j
  · exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ j a b hta)

end OpenImmersion

/-! ### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (i): the restriction
`Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` of the derived pullback to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.leftDerivedUpperStar [UpperStarPreservesFlat A]
    (f : X ⟶ Y) :
    DerivedCategoryFiniteTor A Y ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A Y ⋙ L((f)^*[A]))
    fun K ↦ constructibleFiniteTor_leftDerivedUpperStar A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (iv): the restriction
`Rf_! : Dctf(X, A) ⥤ Dctf(Y, A)` of the compactly supported direct image to the small
categories. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriek (f : X ⟶ Y)
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryFiniteTor A Y :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A X ⋙ R(f)_![A])
    fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek A f K.property

/-- Blueprint `sk-thm-sf-ctf-stability`, clause (vi): the restriction
`𝔻_X : Dctf(X, A)ᵒᵖ ⥤ Dctf(X, A)` of the Verdier dual to the small categories, given that `𝔻_X`
preserves `Dctf(X, A)`. For a finite `Λ` whose exponent is invertible on `k` and `X` separated of
finite type over `k`, this is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`; that
the restriction is an anti-equivalence is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`. -/
noncomputable def DerivedCategoryFiniteTor.verdierDual {S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]
    (h : ∀ ⦃K⦄, constructibleFiniteTor A X K →
      constructibleFiniteTor A X ((Etale.verdierDual A a).obj (op K))) :
    (DerivedCategoryFiniteTor A X)ᵒᵖ ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ ((DerivedCategoryFiniteTor.ι A X).op ⋙ Etale.verdierDual A a)
    fun K ↦ h K.unop.property

end Functors

end Etale

end AlgebraicGeometry
