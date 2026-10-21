/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedExtensionZeroComparison
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization

import Sheaf.Paper.ExtensionZeroPerfectModelTransport
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# Extension by zero preserves stratified perfect local models

Source: Bhatt--Scholze, Lemma 6.1.12, Proposition 6.6.11 and Definition 6.7.6/Lemma 6.7.7
(blueprint: lem-cbc-extension-zero-stratified-perfect).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private theorem localDerived_isZero {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (V : S.ProEt)
    (K : DerivedCategory (pbcModules T R))
    (hK : IsZero ((adicTowerPullback g R).obj K)) :
    IsZero (integralLocalDerived g R V K) := by
  let B := (adicTowerInverseImage g).obj R
  let F := SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1} B V
  let L := (adicTowerPullback g R).obj K
  have h : IsZero (F.mapDerivedCategory.obj L) := F.mapDerivedCategory.map_isZero hK
  let e := F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)
  have h' : IsZero (F.mapDerivedCategory.obj
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage L))) :=
    h.of_iso (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L))
  exact h'.of_iso e.symm

private theorem perfect_zero (A : Type (u + 1)) [CommRing A] :
    let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    let := HasZeroObject.zero' (C := DerivedCategory (ModuleCat.{u + 1} A))
    DerivedCategory.IsPerfectRingComplex (0 : DerivedCategory (ModuleCat.{u + 1} A)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let := HasZeroObject.zero' (C := DerivedCategory (ModuleCat.{u + 1} A))
  let := HasZeroObject.zero' (C := CochainComplex (ModuleCat.{u + 1} A) ℤ)
  let P : CochainComplex (ModuleCat.{u + 1} A) ℤ := 0
  refine ⟨P, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · intro n
    have hz := (HomologicalComplex.eval _ _ n).map_isZero
      (isZero_zero (CochainComplex (ModuleCat.{u + 1} A) ℤ))
    have : Subsingleton (P.X n) := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨(isZero_zero _).iso (DerivedCategory.Q.map_isZero (isZero_zero _))⟩

private def extendStratification {T U Z : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (hcover : Set.range j ∪ Set.range i = Set.univ)
    (hdisjoint : Disjoint (Set.range j) (Set.range i))
    (s : Stratification U) : Stratification T where
  n := s.n + 1
  stratum := Fin.cases (Set.range i) (fun k ↦ j '' s.stratum k)
  isLocallyClosed_stratum := Fin.cases i.isLocallyClosed_range
    (fun k ↦ (s.isLocallyClosed_stratum k).image j.isOpenEmbedding.isInducing
      j.isOpenEmbedding.isOpen_range.isLocallyClosed)
  isConstructible_stratum := Fin.cases
    i.isLocallyClosed_range.isConstructible_of_noetherianSpace
    (fun k ↦ ((s.isLocallyClosed_stratum k).image j.isOpenEmbedding.isInducing
      j.isOpenEmbedding.isOpen_range.isLocallyClosed).isConstructible_of_noetherianSpace)
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ Set.range j ∪ Set.range i := hcover.symm ▸ Set.mem_univ x
    rcases hx with ⟨y, rfl⟩ | hx
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
      exact Set.mem_iUnion.mpr ⟨k.succ, y, hk, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨0, hx⟩
  pairwise_disjoint_stratum := by
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact (hab rfl).elim
      | succ b =>
        exact hdisjoint.symm.mono (Set.Subset.refl _) (Set.image_subset_range _ _)
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        exact hdisjoint.mono (Set.image_subset_range _ _) (Set.Subset.refl _)
      | succ b =>
        exact (Set.disjoint_image_iff j.isOpenEmbedding.injective).mpr
          (s.pairwise_disjoint_stratum (fun h ↦ hab (congrArg Fin.succ h)))
  domain := Fin.cases Z s.domain
  immersion := Fin.cases i (fun k ↦ s.immersion k ≫ j)
  isImmersion := Fin.cases (inferInstanceAs (IsImmersion i))
    (fun k ↦ inferInstanceAs (IsImmersion (s.immersion k ≫ j)))
  range_immersion := Fin.cases rfl (fun k ↦ by
    change Set.range (s.immersion k ≫ j).base = j.base '' s.stratum k
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, s.range_immersion])

private theorem closedDerived_isZero {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T U Z : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hji : Set.range j = (Set.range i)ᶜ)
    (K : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) :
    IsZero ((adicTowerPullback i (pbcAdicCompletion T d)).obj
      ((cbcDerivedOpenShriek d j inferInstance).obj K)) := by
  let R := pbcAdicCompletion T d
  let W := cbcOpenObject j inferInstance
  have : IsOpenImmersion W.hom := inferInstanceAs (IsOpenImmersion j)
  have : QuasiCompact W.hom := inferInstanceAs (QuasiCompact j)
  obtain ⟨q, hq, ai, aj, hci, huj, hzi, hzj, hlj, hcj, hli, hci', hs, hf⟩ :=
    proEtale_ringed_open_closed i W hji R
  let F := cbcOpenShriek d j inferInstance
  let G := proEtaleRingModulePullback i R ((adicTowerInverseImage i).obj R) (Iso.refl _)
  have hz (M : pbcModules U (pbcAdicCompletion U d)) : IsZero (G.obj (F.obj M)) := by
    have hm := hzj ((cbcModuleToSlice d T W).obj M)
    let H := proEtaleRingExtension i R ((adicTowerInverseImage i).obj R) (Iso.refl _)
    have : PreservesFiniteLimits H := proEtaleRingExtension_preservesFiniteLimits ..
    have : H.Additive := Functor.additive_of_preserves_binary_products H
    exact H.map_isZero hm
  let P := DerivedCategory.Q.objPreimage K
  have hp : IsZero (((G.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro n
    exact (hz (P.X n)).eq_of_src _ _
  have hqp := DerivedCategory.Q.map_isZero hp
  let e := G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have hpre : IsZero (G.mapDerivedCategory.obj
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) := hqp.of_iso e
  exact hpre.of_iso
    ((F.mapDerivedCategory ⋙ G.mapDerivedCategory).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm

/-- Extension by zero carries an integral stratified-perfect object on a quasi-compact open
into an integral stratified-perfect object on the ambient Noetherian scheme, and its pullback to
any complementary closed subscheme is zero.  The stratified-perfect predicate is the canonical
finite locally closed pro-etale model predicate; the coefficient datum is the canonical
uniformizer-adic datum attached to a finite extension of `ℚ_ℓ`.

Source: Bhatt--Scholze, Lemma 6.1.12, Proposition 6.6.11 and Definition 6.7.6/Lemma 6.7.7
(blueprint: lem-cbc-extension-zero-stratified-perfect).

Proof: use the exact completed-coefficient extension by zero `cbcDerivedOpenShriek`.  The
open restriction identity transports every original perfect model along the actual inverse
image and the canonical quotient-compatible coefficient identifications.  The complementary
closed inverse image is zero by the ringed pro-etale open-closed localization theorem.  Adding
that closed immersion to the original finite locally closed stratification gives the asserted
finite stratification of the ambient scheme, with the zero complex as its model on the new
closed stratum.
-/
theorem cbc_extension_zero_stratified_perfect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T U Z : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hcover : Set.range j ∪ Set.range i = Set.univ)
    (hdisjoint : Disjoint (Set.range j) (Set.range i))
    (K : DerivedCategory (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))))
    (hK : IsIntegralStratifiedPerfect U (pbcIntegralDatum l E) K) :
    IsIntegralStratifiedPerfect T (pbcIntegralDatum l E)
        ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K) ∧
      IsZero
        ((adicTowerPullback i (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
          ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)) := by
  let d := pbcIntegralDatum l E
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} (PbcIntegralRing l E))
  let := HasZeroObject.zero'
    (C := DerivedCategory (ModuleCat.{u + 1} (PbcIntegralRing l E)))
  have hji : Set.range j = (Set.range i)ᶜ := by
    ext x
    constructor
    · intro hxj hxi
      exact Set.disjoint_left.mp hdisjoint hxj hxi
    · intro hxi
      have hx : x ∈ Set.range j ∪ Set.range i := hcover.symm ▸ Set.mem_univ x
      exact hx.elim id (fun h ↦ (hxi h).elim)
  have hz := closedDerived_isZero d j i hji K
  refine ⟨?_, hz⟩
  obtain ⟨s, hs⟩ := hK
  refine ⟨extendStratification j i hcover hdisjoint s, ?_⟩
  intro k
  induction k using Fin.cases with
  | zero =>
    change ∃ V : Sieve (⊤_ Z.ProEt), V ∈ ProEt.topology Z (⊤_ Z.ProEt) ∧ _
    refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
    intro V f hf
    refine ⟨0, perfect_zero _, ?_⟩
    change Nonempty (integralLocalDerived i (pbcAdicCompletion T d) V
      ((cbcDerivedOpenShriek d j inferInstance).obj K) ≅
        integralLocalDerived i (pbcAdicCompletion T d) V
          ((integralConstantDerived T d).obj 0))
    have hleft := localDerived_isZero i (pbcAdicCompletion T d) V _ hz
    have hc : IsZero ((integralConstantDerived T d).obj 0) := by
      dsimp [integralConstantDerived]
      exact Functor.map_isZero _ (isZero_zero _)
    have hright := localDerived_isZero i (pbcAdicCompletion T d) V _
      ((adicTowerPullback i (pbcAdicCompletion T d)).map_isZero hc)
    exact ⟨hleft.iso hright⟩
  | succ k =>
    change ∃ V : Sieve (⊤_ (s.domain k).ProEt),
      V ∈ ProEt.topology (s.domain k) (⊤_ (s.domain k).ProEt) ∧ _
    obtain ⟨V, hV, hmodels⟩ := hs k
    refine ⟨V, hV, ?_⟩
    intro W f hf
    obtain ⟨P, hP, he⟩ := hmodels W f hf
    exact ⟨P, hP, cbc_extension_zero_perfect_model_transport d j
      (s.immersion k) W K P he⟩

end AlgebraicGeometry.Scheme
