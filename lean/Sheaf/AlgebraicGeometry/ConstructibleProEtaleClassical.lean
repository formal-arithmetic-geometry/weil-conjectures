/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.ProEtaleConstantModulePullbackComposition
import Sheaf.AlgebraicGeometry.ProEtaleClassicalZariskiLocal
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import Sheaf.Paper.ProEtaleStratifiedEssentialImage
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation

/-! # Constructible pro-etale module sheaves are classical

Source: current Weil blueprint, sec-proetale-coefficients/sk-thm-pe-constructible-comparison,
`sk-thm-pe-constructible-comparison-classical.md`; Stacks Project, Tags 099Y and 09AK
(blueprint: det-pe-constructible-comparison-classical).

The global and Zariski-local assertions use intrinsic modules over the constant ring.
The stratum schemes are reduced, including when the ambient scheme is nonreduced.
Local models are finitely generated modules, with no finite-ring assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

private theorem intrinsicClassical_iff_fixed {X : Scheme.{u}}
    (Λ : Type u) [CommRing Λ]
    (F : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X Λ)) :
    IsClassicalModule Λ F ↔ IsClassical
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).obj
          ((Scheme.proEtaleModuleRestriction X Λ).obj F)) := by
  exact isClassicalModule_iff Λ F

private theorem finiteModels_classical {X : Scheme.{u}}
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X Λ))
    (hmodels : ∃ (I : Type (u + 1)) (V : I → X.ProEt)
      (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 X)),
      Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
      ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
        Module.Finite (ULift.{u + 1, u} Λ) M ∧
        Nonempty (F.over (V a) ≅ Scheme.proEtaleConstantModuleSheafOver X Λ (V a) M)) :
    IsClassicalModule Λ F := by
  classical
  let A := ULift.{u + 1, u} Λ
  have : IsNoetherianRing A := isNoetherianRing_of_ringEquiv Λ ULift.ringEquiv.symm
  let E := (Scheme.proEtaleModuleRestriction X Λ).obj F
  obtain ⟨I, V, f, hf, h⟩ := hmodels
  have hfp : ∀ i : I, ∃ M : ModuleCat.{u + 1} A,
      Module.FinitePresentation A M ∧
      Nonempty (E.over (V i) ≅
        (constantSheaf ((Scheme.ProEt.topology X).over (V i)) (ModuleCat.{u + 1} A)).obj M) := by
    intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := h i
    have := hM
    have hpres : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing X Λ)
    let a := Functor.whiskerLeft (Over.forget (V i)).op (Scheme.proEtaleModuleScalarUnit X Λ)
    have hi : Presheaf.IsLocallyInjective ((Scheme.ProEt.topology X).over (V i)) a :=
      (Scheme.proEtaleConstantRingUnit_over_locallyBijective X Λ (V i)).1
    have hs : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over (V i)) a :=
      (Scheme.proEtaleConstantRingUnit_over_locallyBijective X Λ (V i)).2
    let L := Scheme.ConstantScalarComparison.restriction
      ((Scheme.ProEt.topology X).over (V i)) A (R.over (V i)) a
    have hc := Scheme.ConstantScalarComparison.constantComparisonHom_isIso
      ((Scheme.ProEt.topology X).over (V i)) A (R.over (V i)) a M
    exact ⟨M, hpres, ⟨L.mapIso e ≪≫
      (asIso (Scheme.ConstantScalarComparison.constantComparisonHom
        ((Scheme.ProEt.topology X).over (V i)) A (R.over (V i)) a M)).symm⟩⟩
  have hloc : IsFinitePresentationProEtaleLocalSystem X Λ E := by
    refine ⟨⟨I, V, f, hf, ?_⟩, I, V, f, hf, hfp⟩
    intro i
    obtain ⟨M, _, e⟩ := hfp i
    exact ⟨M, e⟩
  apply (intrinsicClassical_iff_fixed Λ F).mpr
  exact (finiteLocalSystemsTwist X Λ E hloc).2.1

private theorem fixedClassical_iff_essImage {X : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (E : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    IsClassical ((sheafCompose (Scheme.ProEt.topology X)
      (forget (ModuleCat.{u + 1} A))).obj E) ↔
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).essImage E := by
  obtain ⟨adj, _, _, _, _, h⟩ := proEtaleClassicalSheavesModules X A
  exact h E

private theorem intrinsicClassical_zariskiLocal {X : Scheme.{u}}
    (Λ : Type u) [CommRing Λ]
    (F : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X Λ))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsClassicalModule Λ (Scheme.proEtaleConstantModulePullback U.ι Λ F)) :
    IsClassicalModule Λ F := by
  classical
  choose U hx hU using h
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  let E := (Scheme.proEtaleModuleRestriction X Λ).obj F
  apply (intrinsicClassical_iff_fixed Λ F).mpr
  apply (proEtaleClassical_zariskiLocal X (ULift.{u + 1, u} Λ) E).1 X U
  · apply le_antisymm le_top
    intro x _
    exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  · intro x
    obtain ⟨e⟩ := Scheme.proEtaleModuleRestriction_pullback_of_isIso (U x).ι Λ F
    let t := e ≪≫ (upperStarIsoOpenImmersionRestriction A (U x).ι).app E
    apply (isClassical_iso_iff
      ((sheafCompose (Scheme.ProEt.topology (U x).toScheme) (forget A)).mapIso t)).mp
    exact (intrinsicClassical_iff_fixed Λ _).mp (hU x)

private theorem stratified_classical {X : Scheme.{u}}
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X Λ))
    (S : Scheme.LocallyClosedStratification X)
    (hm : ∀ k : Fin S.n,
      ∃ (I : Type (u + 1)) (V : I → (S.domain k).ProEt)
        (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 (S.domain k))),
        Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage (S.domain k)).coverings _ ∧
        ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Module.Finite (ULift.{u + 1, u} Λ) M ∧
          Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion k) Λ F).over (V a) ≅
            Scheme.proEtaleConstantModuleSheafOver (S.domain k) Λ (V a) M)) :
    IsClassicalModule Λ F := by
  let A := ULift.{u + 1, u} Λ
  let E := (Scheme.proEtaleModuleRestriction X Λ).obj F
  apply (intrinsicClassical_iff_fixed Λ F).mpr
  apply (fixedClassical_iff_essImage A E).mpr
  apply comparison_essImage_of_stratification A S E
  intro k
  have h : IsClassicalModule Λ
      (Scheme.proEtaleConstantModulePullback (S.immersion k) Λ F) :=
    finiteModels_classical Λ _ (hm k)
  obtain ⟨e⟩ := Scheme.proEtaleModuleRestriction_pullback_of_isIso (S.immersion k) Λ F
  apply (fixedClassical_iff_essImage A _).mp
  apply (isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology (S.domain k))
      (forget (ModuleCat.{u + 1} A))).mapIso e)).mp
  exact (intrinsicClassical_iff_fixed Λ _).mp h


/-- A finite constructible locally closed partition with finite constant local module models
makes a pro-etale module sheaf classical. Reduced immersed representatives realize the
reduced induced structure on each stratum. Constructibility, local closedness, disjointness
and covering are fields of `S.toStratification`; empty strata and zero strata are allowed.

Source: current blueprint, constructible-comparison-classical; Stacks, Tags 099Y and 09AK
(blueprint: det-pe-constructible-comparison-classical).

Proof: restrict scalars along the constant-ring sheafification unit. On each slice,
the constant-model comparison identifies the same finitely generated model with the
usual constant module sheaf. Its finite presentation follows from Noetherianity.
The finite local-system comparison makes each stratum classical. The essential-image
criterion and stratified essential-image induction then make the entire sheaf classical.
The latter induction uses affine shrinking, the open-closed exact sequence, extension
by zero and closed direct-image comparison; it works for arbitrary coefficient rings.
Finally scalar restriction preserves the underlying set sheaf, hence classicality. -/
theorem constructible_isClassicalModule (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing X Λ)))
    (S : Scheme.LocallyClosedStratification X)
    (_hred : ∀ k : Fin S.n, IsReduced (S.domain k))
    (_hmodels : ∀ k : Fin S.n,
      ∃ (I : Type (u + 1)) (V : I → (S.domain k).ProEt)
        (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 (S.domain k))),
        Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage (S.domain k)).coverings _ ∧
        ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Module.Finite (ULift.{u + 1, u} Λ) M ∧
          Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion k) Λ F).over (V a) ≅
            Scheme.proEtaleConstantModuleSheafOver (S.domain k) Λ (V a) M)) :
    IsClassicalModule Λ F := by
  exact stratified_classical Λ F S _hmodels

/-- The finite constructible partition may exist only on Zariski neighborhoods of points.
Restriction to a stratum of an open is pullback along its composite immersion into X,
with the canonical constant-ring structure map.

Source: current blueprint, constructible-comparison-classical, last sentence;
Stacks, Tags 09AJ and 09AK (blueprint: det-pe-constructible-comparison-classical).

Proof: the preceding stratified argument works on any scheme, so it applies directly
on each given neighborhood. The canonical composition isomorphism of intrinsic module
pullbacks identifies the stratum restrictions with the displayed composite pullbacks.
The fixed-module encoding commutes with pullback and with open restriction. Zariski
locality of classicality therefore gives classicality of the original sheaf. -/
theorem locallyConstructible_isClassicalModule (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
    (F : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing X Λ)))
    (_hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ S : Scheme.LocallyClosedStratification U.toScheme,
        (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
        ∀ k : Fin S.n,
          ∃ (I : Type (u + 1)) (V : I → (S.domain k).ProEt)
            (f : ∀ a : I, V a ⟶ Scheme.ProEt.mk (𝟙 (S.domain k))),
            Presieve.ofArrows V f ∈ (Scheme.ProEt.precoverage (S.domain k)).coverings _ ∧
            ∀ a : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
              Module.Finite (ULift.{u + 1, u} Λ) M ∧
              Nonempty ((Scheme.proEtaleConstantModulePullback
                (S.immersion k ≫ U.ι) Λ F).over (V a) ≅
                  Scheme.proEtaleConstantModuleSheafOver (S.domain k) Λ (V a) M)) :
    IsClassicalModule Λ F := by
  apply intrinsicClassical_zariskiLocal Λ F
  intro x
  obtain ⟨U, hx, S, hred, hm⟩ := _hlocal x
  refine ⟨U, hx, ?_⟩
  apply stratified_classical Λ _ S
  intro k
  obtain ⟨I, V, f, hf, he⟩ := hm k
  refine ⟨I, V, f, hf, ?_⟩
  intro a
  obtain ⟨M, hM, ⟨e⟩⟩ := he a
  obtain ⟨c⟩ := Scheme.proEtaleConstantModulePullback_comp U.ι (S.immersion k) Λ
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ (V a)).mapIso (c.app F).symm ≪≫ e⟩⟩

end AlgebraicGeometry.ProEtale
