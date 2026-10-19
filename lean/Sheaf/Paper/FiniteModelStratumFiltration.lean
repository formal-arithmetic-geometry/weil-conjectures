/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.NoetherianSpace

import Sheaf.Paper.OpenFiltrationSuccessor
import all Sheaf.Paper.ContinuousConstructibleIntegralGluing
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ReducedSourceFactors
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Finite open filtrations with finite constant models on reduced strata

Source: Stacks Project, Topology, Tag 09Y5
(`lemma-noetherian-partition-refined-by-stratification`), and Pro-etale Cohomology,
Tag 09AH (`lemma-ses-associated-to-open`)
(blueprint: lem-sfb-finite-model-stratum-filtration).
Re-recorded by group NS on 2026-10-18; the statement and constructions are unchanged.

The auxiliary functors name the actual extension-by-zero pieces and closed-stratum
pieces. Cokernels in the functor category express naturality with the opens fixed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

private instance (priority := 2000) essentiallySmallSelfInstance
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical piece `v_! v^*`, for the inclusion of an open subscheme.
Source: Stacks Tag 09AH, first term of the localization sequence
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationPiece {X : Scheme.{u}} (V : X.Opens) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  upperStar Λ V.ι ⋙ openImmersionLowerShriek Λ V.ι

/-- The counit of the specified extension-by-zero/restriction adjunction.
Source: Stacks Tag 09AH, injection of the open-supported piece
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationCounit {X : Scheme.{u}} (V : X.Opens) :
    openFiltrationPiece Λ V ⟶ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit

/-- The functor `v_! t_* t^* v^*` for a closed stratum in an open subscheme.
Source: Stacks Tag 09AH, closed term of the localization sequence, extended by zero
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationStratum {X : Scheme.{u}} (V : X.Opens)
    {S : Scheme.{u}} (t : S ⟶ V.toScheme) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  upperStar Λ V.ι ⋙ upperStar Λ t ⋙ lowerStar Λ t ⋙ openImmersionLowerShriek Λ V.ι

set_option backward.isDefEq.respectTransparency false in
private theorem pointModulePullbackIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((upperStar Λ f).obj (((upperStarFromPoint Z).mapMod Λ).obj P) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj P) := by
  let α := condensedPullbackHom Λ f
  let e := Mod.comapEquivalenceOfIsIso α
  have : (Mod.comap α).Full := e.fullyFaithfulFunctor.full
  have : (Mod.comap α).Faithful := e.fullyFaithfulFunctor.faithful
  let a := Mod.extendRestrictAdjunction α
  have : IsIso a.counit := a.counit_isIso_of_R_fully_faithful
  let eP := (Functor.mapModCompIso (upperStarFromPoint Z)
    (ProEtale.upperStar Ab.{u + 1} f) (upperStarFromPointComp f).hom Λ).app P
  exact ⟨(Mod.extendScalars α).mapIso eP ≪≫ asIso (a.counit.app _)⟩

private theorem finiteModel_of_iso {Y : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
    HasFiniteConstantLocalModel Λ Y N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem pullback_square_iso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (h : a ≫ c = b ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)) :
    Nonempty ((upperStar Λ a).obj ((upperStar Λ c).obj M) ≅
      (upperStar Λ b).obj ((upperStar Λ d).obj M)) := by
  exact ⟨(upperStarComp Λ a c).symm.app M ≪≫
    (upperStarCongr Λ h).app M ≪≫ (upperStarComp Λ b d).app M⟩

private theorem pullback_model {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (h : a ≫ c = b ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (e : Nonempty ((upperStar Λ d).obj M ≅ ((upperStarFromPoint C).mapMod Λ).obj P)) :
    Nonempty ((upperStar Λ a).obj ((upperStar Λ c).obj M) ≅
      ((upperStarFromPoint A).mapMod Λ).obj P) := by
  obtain ⟨e⟩ := e
  obtain ⟨es⟩ := pullback_square_iso Λ a b c d h M
  obtain ⟨ep⟩ := pointModulePullbackIso Λ b P
  exact ⟨es ≪≫ (upperStar Λ b).mapIso e ≪≫ ep⟩

private theorem finiteModel_pullback_cover {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z)
    (𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (a : 𝒱.I₀ → 𝒰.I₀) (g : ∀ i, 𝒱.X i ⟶ 𝒰.X (a i))
    (w : ∀ i, 𝒱.f i ≫ f = g i ≫ 𝒰.f (a i))
    (h𝒰 : ∀ i, ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((upperStar Λ (𝒰.f i)).obj M ≅
        ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj P)) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  refine ⟨𝒱, fun i ↦ ?_⟩
  obtain ⟨P, hP, eP⟩ := h𝒰 (a i)
  exact ⟨P, hP, pullback_model Λ (𝒱.f i) (g i) f (𝒰.f (a i)) (w i) M P eP⟩

private theorem finiteModel_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : HasFiniteConstantLocalModel Λ Z M) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  exact finiteModel_pullback_cover Λ f M 𝒰 (𝒰.pullback₂ f) id
    (fun i ↦ pullback.fst (𝒰.f i) f)
    (fun i ↦ (pullback.condition (f := 𝒰.f i) (g := f)).symm) h𝒰

private theorem reduced_factors_immersion {Y Z X : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (i : Z ⟶ X) [IsImmersion i]
    (h : Set.range f ⊆ Set.range i) : ∃ g : Y ⟶ Z, g ≫ i = f := by
  let f' : Y ⟶ i.coborderRange.toScheme :=
    IsOpenImmersion.lift i.coborderRange.ι f (h.trans (by simpa using! subset_coborder))
  have hf' : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have h' : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := h (Set.mem_range_self y)
    refine ⟨z, ?_⟩
    apply i.coborderRange.ι.isOpenEmbedding.injective
    change (i.liftCoborder ≫ i.coborderRange.ι) z = (f' ≫ i.coborderRange.ι) y
    rw [i.liftCoborder_ι, hf']
    exact hz
  obtain ⟨g, hg⟩ :=
    (reduced_source_factors_through_closed_subscheme i.liftCoborder f').1.mpr h'
  refine ⟨g, ?_⟩
  rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf']

private theorem finiteModel_on_reduced_substratum {X Y : Scheme.{u}} [IsReduced Y]
    (A : Scheme.Stratification X) (a : Fin A.n) (f : Y ⟶ X)
    (hf : Set.range f ⊆ A.stratum a)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ (A.domain a)
      ((upperStar Λ (A.immersion a)).obj M)) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  obtain ⟨g, hg⟩ := reduced_factors_immersion f (A.immersion a)
    (by rwa [A.range_immersion])
  have h := finiteModel_pullback Λ g _ hM
  apply finiteModel_of_iso Λ ((upperStarComp Λ g (A.immersion a)).symm.app M) at h
  rwa [hg] at h

private theorem noetherian_qc {Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (f : Y ⟶ Z) : QuasiCompact f :=
  ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact (f ⁻¹' U)⟩

private theorem exists_reduced_complement {X : Scheme.{u}} (U : X.Opens) :
    ∃ (S : Scheme.{u}) (t : S ⟶ X), IsClosedImmersion t ∧ IsReduced S ∧
      Set.range t = (U : Set X)ᶜ := by
  let T : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  have h := Scheme.IdealSheafData.reduced_induced_closed_subscheme X T
  exact ⟨I.subscheme, I.subschemeι, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem exists_geometric_filtration (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstantModelConstructible Λ X F) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last r) = ⊤ ∧
      ∃ (S : Fin r → Scheme.{u}) (t : ∀ k : Fin r, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin r, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin r, HasFiniteConstantLocalModel Λ (S k)
          ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj F))) ∧
        (∀ k : Fin (r + 1), QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin r,
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hF' : IsFiniteConstantStratified Λ X F := by
    simpa only [IsConstantModelConstructible, if_pos hX] using hF
  obtain ⟨A, hA⟩ := hF'
  obtain ⟨r, V, hV0, hVr, hstep⟩ := A.toStratification.exists_chain_opens (⊥ : X.Opens)
  change Fin (r + 1) → X.Opens at V
  have hV : Monotone V := Fin.monotone_iff_le_succ.mpr fun k ↦ (hstep k).1
  have hc (k : Fin r) := exists_reduced_complement ((V k.succ).ι ⁻¹ᵁ V k.castSucc)
  choose S t ht hred hrange using hc
  refine ⟨r, V, hV, hV0, hVr, S, t, fun k ↦ ⟨ht k, hred k, hrange k⟩,
    ?_, ?_, ?_⟩
  · intro k
    have := ht k
    have := hred k
    obtain ⟨a, ha⟩ := (hstep k).2
    have hsub : Set.range (t k ≫ (V k.succ).ι) ⊆ A.stratum a := by
      rintro _ ⟨s, rfl⟩
      apply ha
      refine ⟨by simp, ?_⟩
      have hs : t k s ∈ Set.range (t k) := Set.mem_range_self s
      rw [hrange k] at hs
      exact hs
    have h := finiteModel_on_reduced_substratum Λ A a (t k ≫ (V k.succ).ι)
      hsub F (hA a)
    exact finiteModel_of_iso Λ ((upperStarComp Λ (t k) (V k.succ).ι).app F) h
  · intro k
    have : TopologicalSpace.NoetherianSpace (V k).toScheme :=
      inferInstanceAs (TopologicalSpace.NoetherianSpace (V k : Set X))
    exact ⟨noetherian_qc _, inferInstance⟩
  · intro k
    have : TopologicalSpace.NoetherianSpace (V k.succ).toScheme :=
      inferInstanceAs (TopologicalSpace.NoetherianSpace (V k.succ : Set X))
    have : TopologicalSpace.NoetherianSpace
        (((V k.succ).ι ⁻¹ᵁ V k.castSucc).toScheme) :=
      inferInstanceAs (TopologicalSpace.NoetherianSpace
        (((V k.succ).ι ⁻¹ᵁ V k.castSucc : (V k.succ).toScheme.Opens) :
          Set (V k.succ).toScheme))
    exact ⟨noetherian_qc _, inferInstance⟩

private theorem openFiltrationPiece_bot_zero {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero ((openFiltrationPiece Λ (⊥ : X.Opens)).obj F) := by
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  exact (openImmersionLowerShriek Λ (⊥ : X.Opens).ι).map_isZero
    (module_zero_of_empty _ _)

private theorem openFiltrationCounit_top_iso {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((openFiltrationCounit Λ (⊤ : X.Opens)).app F) := by
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact iso_condensed_counit Λ _ F

/-- Finite open filtration of a constructible module with finite scalar local models.
Source: Stacks Tag 09Y5 and Tag 09AH; blueprint constructibility, clauses (1)--(2)
(blueprint: lem-sfb-finite-model-stratum-filtration).

Proof plan:
1. `lem-sfb-noetherian-space-compact-subsets` makes all subsets compact. This gives
qcqs for the scheme and all open immersions and allows the finite-stratification
clause of `sk-def-sfb-constructible` to be applied to F.
2. `lem-sfb-noetherian-good-stratification-refinement` gives a finite good refinement
of that partition, including the empty partition for the empty scheme.
3. Order maximal strata first. Their prefixes are open by the closure formula of
Tag 09Y0. Give each difference its reduced closed structure by
`lem-weil-pbc-reduced-induced-closed-subscheme`. Compactness of subsets gives qcqs.
4. The reduced-source factorization lemma factors each new stratum through its old
stratum. Composition of module pullbacks identifies the restrictions. Base change
of the trivializing pro-etale cover and the monoidal inverse image, using
`lem-sfb-alpha-iso`, pull back the same finite scalar presentation, even with torsion.
5. Apply `lem-weil-pbc-proetale-ringed-open-closed` to every open and its reduced
closed complement. The internal/sectionwise module equivalence and alpha comparison
identify its open extension with the specified module lower shriek. Its counit is
monic; the empty and total opens give the zero and whole objects.
6. Apply the same localization sequence inside each successive open and its exact
extension by zero to X. The composite left-adjoint comparison, with
`def-sfb-module-upper-star-comp`, identifies the first term with the preceding
piece and identifies its map to F with the preceding counit. Thus the cokernel
is the ordinary closed direct image of the stratum restriction, extended by zero.
7. All localization maps and adjunction comparisons are natural in the module.
Taking cokernels in the functor category gives the displayed natural isomorphisms.
-/
theorem exists_finiteModelStratumFiltration (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstantModelConstructible Λ X F) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last r) = ⊤ ∧
      ∃ (S : Fin r → Scheme.{u}) (t : ∀ k : Fin r, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin r, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin r, HasFiniteConstantLocalModel Λ (S k)
          ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj F))) ∧
        (∀ k : Fin (r + 1), QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin r,
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι) ∧
        (∀ k : Fin (r + 1), Mono ((openFiltrationCounit Λ (V k)).app F)) ∧
        IsZero ((openFiltrationPiece Λ (V 0)).obj F) ∧
        IsIso ((openFiltrationCounit Λ (V (Fin.last r))).app F) ∧
        ∃ d : ∀ k : Fin r,
          openFiltrationPiece Λ (V k.castSucc) ⟶ openFiltrationPiece Λ (V k.succ),
          (∀ k : Fin r,
            d k ≫ openFiltrationCounit Λ (V k.succ) =
              openFiltrationCounit Λ (V k.castSucc)) ∧
          (∀ k : Fin r, Mono ((d k).app F)) ∧
          (∀ k : Fin r,
            Nonempty (cokernel (d k) ≅ openFiltrationStratum Λ (V k.succ) (t k))) := by
  classical
  obtain ⟨r, V, hV, hV0, hVr, S, t, ht, hmodel, hqc, hqc'⟩ :=
    exists_geometric_filtration Λ X F hF
  have hstep (k : Fin r) :
      ∃ d : openFiltrationPiece Λ (V k.castSucc) ⟶ openFiltrationPiece Λ (V k.succ),
        d ≫ openFiltrationCounit Λ (V k.succ) = openFiltrationCounit Λ (V k.castSucc) ∧
        Nonempty (cokernel d ≅ openFiltrationStratum Λ (V k.succ) (t k)) := by
    have := (hqc k.castSucc).1
    have := (hqc k.castSucc).2
    have := (hqc k.succ).1
    have := (hqc k.succ).2
    have := (hqc' k).1
    have := (hqc' k).2
    have := (ht k).1
    exact exists_openFiltrationSuccessor Λ _ _ (hV (Fin.castSucc_le_succ k))
      (t k) (ht k).2.2
  choose d hd he using hstep
  refine ⟨r, V, hV, hV0, hVr, S, t, ht, hmodel, hqc, hqc', ?_, ?_, ?_,
    d, hd, ?_, he⟩
  · intro k
    exact mono_condensed_counit Λ _ F
  · rw [hV0]
    exact openFiltrationPiece_bot_zero Λ F
  · rw [hVr]
    exact openFiltrationCounit_top_iso Λ F
  · intro k
    have : Mono ((openFiltrationCounit Λ (V k.castSucc)).app F) :=
      mono_condensed_counit Λ (V k.castSucc).ι F
    have h := congrArg (fun e ↦ e.app F) (hd k)
    change (d k).app F ≫ (openFiltrationCounit Λ (V k.succ)).app F = _ at h
    exact mono_of_mono_fac h

end AlgebraicGeometry.ProEtale.CondensedRing
