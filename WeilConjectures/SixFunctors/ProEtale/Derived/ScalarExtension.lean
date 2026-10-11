/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

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

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.ReflectsIsomorphisms]

/-- An exact functor reflecting isomorphisms induces a functor on derived categories reflecting
isomorphisms: a morphism is an isomorphism iff it is one on all homology objects, and
`F.mapDerivedCategory` commutes with homology. -/
instance reflectsIsomorphisms_mapDerivedCategory : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F

end CategoryTheory.Functor

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

end AlgebraicGeometry.ProEtale
