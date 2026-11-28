/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Restriction of scalars of pro-étale sheaves of modules is exact

For a ring morphism `φ : R →+* S` and a scheme `X`, restriction of scalars
`Sh(X_proét, S) ⥤ Sh(X_proét, R)` preserves limits, being right adjoint to extension of scalars,
and finite colimits, being left adjoint to coextension of scalars; it reflects isomorphisms.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_sheafComposeRestrictScalars`,
  `AlgebraicGeometry.ProEtale.preservesLimits_sheafComposeRestrictScalars`: exactness.
- `AlgebraicGeometry.ProEtale.reflectsIsomorphisms_sheafComposeRestrictScalars`: restriction of
  scalars is conservative.
-/

@[expose] public section

universe u

open CategoryTheory Limits

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


end AlgebraicGeometry.ProEtale
