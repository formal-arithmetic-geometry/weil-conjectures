/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.FittingIdealSheaf
public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Affine realization and pullback of Fitting ideal sheaves

Source: Stacks Project, Divisors, Tags 0C3C, 0C3D and 0C3I; Schemes, Tag 01JU;
Morphisms, Tag 01QQ (blueprint: lem-trf-fitting-ideal-sheaf-pullback).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The largest ideal satisfying the affine kernel-minor bounds attains those bounds,
its closed subscheme has the expected affine quotient charts, and both commute with
arbitrary scheme pullback. The pulled-back ideal is an image, with no injectivity claim.
Source: Stacks Project, Divisors, Tags 0C3C, 0C3D and 0C3I; Schemes, Tag 01JU;
Morphisms, Tag 01QQ (blueprint: lem-trf-fitting-ideal-sheaf-pullback).

Proof plan:
1. On each affine open, finite type gives finite generators by
   lem-weil-pbc-quasi-coherent-finite-type-affine. Apply
   lem-trf-fitting-ideal-sheaf-affine-sections to identify the largest ideal with every
   kernel-minor ideal. Presentation independence is
   lem-trf-fitting-ideal-independence-base-change; its definition includes the unit-ideal
   convention when the number of generators is at most the index.
2. The affine counit of lem-weil-pbc-affine-tilde-gamma-adjunction identifies the restricted
   module with its associated module. Use lem-weil-pbc-spec-module-tilde-sections and
   localization in lem-trf-fitting-ideal-independence-base-change to check principal-open
   compatibility. Principal opens are affine by lem-weil-pbc-affine-ideals-closed-subscheme.
3. That affine-ideals gluing lemma gives the closed immersion and quotient charts.
   Its ideal (def-sbc-closed-immersion-ideal-sheaf) agrees with the Fitting ideal on every
   affine open, hence as an ideal subsheaf, by the sheaf condition.
4. Apply lem-trf-fitting-sheaf-arbitrary-pullback: the tensor pullback is finite-type
   quasi-coherent and its affine Fitting ideals are the extensions of the original ones.
   The first three steps apply also to this pullback.
5. By lem-pc-closed-subscheme-base-change-ideal-image, the base-changed closed immersion
   has the image of the pulled-back ideal as its ideal. By
   lem-pc-ideal-sheaf-comap-affine-extension these are the same extended ideals on affine
   pairs. Such pairs cover every open of the source, proving the ideal equalities.
6. The two closed immersions over the source have equal ideals. Apply
   lem-weil-pbc-closed-immersion-factor-ideal-inclusion in both directions. Their composites
   are identities because closed immersions are monomorphisms (def-weil-closed-immersion).
   This also proves uniqueness of the isomorphism over the source.
-/
theorem fittingIdealSheaf_affine_pullback (S : Scheme.{u}) (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    (∀ (U : S.affineOpens) (n : ℕ)
      (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)),
      Function.Surjective π →
        (fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r ∧
        (fittingIdealSheaf F r).comap U.1.ι =
          IdealSheafData.ofIdealTop
            ((π.presentationFittingIdeal r).map U.1.topIso.inv.hom) ∧
        ∃ e : Limits.pullback (fittingIdealSheaf F r).subschemeι U.1.ι ≅
          Spec (.of (Γ(S, U.1) ⧸ π.presentationFittingIdeal r)),
          e.hom ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (π.presentationFittingIdeal r))) ≫ U.2.isoSpec.inv =
              pullback.snd (fittingIdealSheaf F r).subschemeι U.1.ι) ∧
    (∀ (T : Scheme.{u}) (h : T ⟶ S),
      ∃ (hft : ((tensorPullback h).obj F).IsFiniteType)
        (hqc : ((tensorPullback h).obj F).IsQuasicoherent),
        @fittingIdealSheaf T ((tensorPullback h).obj F) hft hqc r =
          (fittingIdealSheaf F r).comap h ∧
        Subobject.mk (@fittingIdealSheaf T ((tensorPullback h).obj F) hft hqc r).toModulesι =
          imageSubobject
            ((tensorPullback h).map (fittingIdealSheaf F r).toModulesι ≫
              ((tensorPullbackSectionAdjunction h).homEquiv
                (SheafOfModules.unit S.ringCatSheaf)
                (SheafOfModules.unit T.ringCatSheaf)).symm
                  (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom)) ∧
        ∃! e : (@fittingIdealSheaf T ((tensorPullback h).obj F) hft hqc r).subscheme ≅
          Limits.pullback h (fittingIdealSheaf F r).subschemeι,
          e.hom ≫ pullback.fst h (fittingIdealSheaf F r).subschemeι =
            (@fittingIdealSheaf T ((tensorPullback h).obj F) hft hqc r).subschemeι) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
