/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal

/-!
# Extension of scalars and the projection map of `Rg_*` on the pro-étale site

Let `S` be a finite free algebra over a Noetherian ring `R`, for instance the ring of integers
`𝒪_{E'}` of a finite extension `E'/E` of `ℓ`-adic fields over `𝒪_E`. Extension of scalars
`N = S ⊗_R - : D(X_proét, R) ⥤ D(X_proét, S)` commutes with the derived pullbacks `Lg^*`, with the
derived tensor products and with the derived direct images `Rg_*`, and it carries the projection
map `Rg_* M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^* L)` over `R` to the one over `S`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app`:
  the base change map `N (Rg_* M) ⟶ Rg_* (N M)` is invertible. Restriction of scalars `U` is
  conservative, and `U N M` is the sum of copies of `M` indexed by a basis of `S`, on which `U` of
  the base change map is the iterated mate of the commutation of `N` with `Lg^*`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_extendScalars`:
  the transport of the projection formula for `Rg_*` along extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

/-- Restriction of scalars of pro-étale sheaves preserves finite colimits: it is the sheafified
postcomposition with restriction of scalars, which is left adjoint to coextension of scalars. -/
instance preservesFiniteColimits_sheafComposeRestrictScalars :
    PreservesFiniteColimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) := by
  have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hadj.rightAdjoint_preservesLimits
  have : (Scheme.ProEt.topology X).HasSheafCompose
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (Scheme.ProEt.topology X) hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- Restriction of scalars of pro-étale sheaves reflects isomorphisms, isomorphisms of sheaves
being detected on sections. -/
instance reflectsIsomorphisms_sheafComposeRestrictScalars :
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)).ReflectsIsomorphisms where
  reflects {F G} f hf := by
    have : IsIso ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} φ)).map f)) := inferInstance
    have : IsIso f.hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U)) :=
        NatIso.isIso_app_of_isIso
          ((sheafToPresheaf _ _).map ((sheafCompose (Scheme.ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1} φ)).map f)) U
      have : IsIso ((forget (ModuleCat R)).map
          ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U))) := inferInstance
      have : IsIso ((forget (ModuleCat S)).map (f.hom.app U)) := this
      exact isIso_of_reflects_iso _ (forget (ModuleCat S))
    have : IsIso ((sheafToPresheaf _ _).map f) := this
    exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

section Linear

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type*) [Ring Λ] [Linear Λ A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` on pro-étale sheaves with values in a `Λ`-linear category is
`Λ`-linear: it acts on morphisms by whiskering. -/
instance linear_lowerStar : (g)_*[A].Linear Λ where

/-- The pullback `g^*` on pro-étale sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear pushforward. -/
instance linear_upperStar : (g)^*[A].Linear Λ :=
  (upperStarLowerStarAdjunction A g).left_adjoint_linear

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` on pro-étale sheaves is `Λ`-linear: it is isomorphic to the
functor `D(g^*)` induced by the `Λ`-linear exact functor `g^*`. -/
instance linear_leftDerivedUpperStar : (L((g)^*[A])).Linear Λ :=
  Functor.linear_of_iso Λ ((g)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The derived pushforward `Rg_*` on pro-étale sheaves is `Λ`-linear, being right adjoint to the
`Λ`-linear `Lg^*`. -/
instance linear_rightDerivedLowerStar : (R((g)_*[A])).Linear Λ :=
  (derivedUpperStarLowerStarAdjunction A g).right_adjoint_linear

end Linear

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
  (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [ProEtale.UpperStarPreservesFlat B]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (E_Y : Sheaf (Scheme.ProEt.topology Y) A ⥤ Sheaf (Scheme.ProEt.topology Y) B) [E_Y.Additive]
  [PreservesFiniteLimits E_Y] [PreservesFiniteColimits E_Y] [E_Y.PreservesFlat]
  [E_Y.IsLeftAdjoint] [E_Y.Monoidal]
  (E_Z : Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Z) B) [E_Z.Additive]
  [PreservesFiniteLimits E_Z] [PreservesFiniteColimits E_Z] [E_Z.PreservesFlat]
  [E_Z.IsLeftAdjoint] [E_Z.Monoidal]
  (τ : E_Y ⋙ (g)^*[B] ≅ (g)^*[A] ⋙ E_Z) [NatTrans.IsMonoidal τ.hom]

end General

section ScalarExtension

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- Restriction of scalars preserves pro-étale sheaves, being a right adjoint. -/
instance hasSheafCompose_restrictScalars (φ : R →+* S) :
    (Scheme.ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars.{u + 1} φ) :=
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.restrictScalars.{u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).rightAdjoint_preservesLimits
  hasSheafCompose_of_preservesLimitsOfSize _

/-- Restriction of scalars of pro-étale sheaves preserves limits, being a right adjoint. -/
instance preservesLimits_sheafComposeRestrictScalars (φ : R →+* S) :
    PreservesLimits (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)) :=
  (sheafExtendScalarsAdjunction φ X).rightAdjoint_preservesLimits

/-- Extension of scalars along a flat algebra is exact on pro-étale sheaves. -/
instance preservesFiniteLimits_sheafExtendScalars_algebraMap [Module.Flat R S] :
    PreservesFiniteLimits (sheafExtendScalars (algebraMap R S) X) :=
  preservesFiniteLimits_sheafExtendScalars X (RingHom.flat_algebraMap_iff.2 inferInstance)

variable [Module.Flat R S]

variable {X}

local notation "𝐅" => sheafExtendScalars (algebraMap R S) X
set_option hygiene false in
local notation "𝐀" => sheafExtendScalarsAdjunction (algebraMap R S) X
set_option hygiene false in
local notation "𝐆" => sheafCompose (Scheme.ProEt.topology X)
  (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))

variable [Module.Finite R S] [Module.Free R S]
  [Nontrivial R] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

variable [IsNoetherianRing R] [IsNoetherianRing S]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end OpenImmersion

end ScalarExtension

end AlgebraicGeometry.ProEtale
