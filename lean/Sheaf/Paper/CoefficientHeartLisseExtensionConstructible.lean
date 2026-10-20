/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.Paper.CoefficientHeart
import all Sheaf.Paper.CondensedOpenClosedRecollement
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.ConstantModelTorAmplitude
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Constructibility of locally closed lisse extensions
Source: blueprint generation, Converse paragraph.
(blueprint: lem-sfb-coefficient-heart-lisse-extension-constructible)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finiteModel_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU a
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f a)).mapIso e.symm) ≪≫ eP⟩⟩

private theorem openClosed_adapted {U Z X : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i = (Set.range j)ᶜ)
    (SU : Scheme.Stratification U) (SZ : Scheme.Stratification Z)
    (P : ∀ S : Scheme.{u}, (S ⟶ X) → Prop)
    (hU : ∀ a, P (SU.domain a) (SU.immersion a ≫ j))
    (hZ : ∀ a, P (SZ.domain a) (SZ.immersion a ≫ i)) :
    ∀ a, P ((Scheme.Stratification.openClosed j i hij SU SZ).domain a)
      ((Scheme.Stratification.openClosed j i hij SU SZ).immersion a) := by
  intro a
  change P _ (Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
    (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
    (finSumFinEquiv.symm a))
  generalize finSumFinEquiv.symm a = b
  rcases b with b | b
  · exact hU b
  · exact hZ b

private theorem stratified_of_restrictions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z X : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i = (Set.range j)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : IsFiniteConstantStratified Λ U ((CondensedRing.upperStar Λ j).obj M))
    (hZ : IsFiniteConstantStratified Λ Z ((CondensedRing.upperStar Λ i).obj M)) :
    IsFiniteConstantStratified Λ X M := by
  obtain ⟨SU, hSU⟩ := hU
  obtain ⟨SZ, hSZ⟩ := hZ
  refine ⟨Scheme.Stratification.openClosed j i hij SU SZ, ?_⟩
  apply openClosed_adapted j i hij SU SZ
    (fun S a ↦ HasFiniteConstantLocalModel Λ S ((CondensedRing.upperStar Λ a).obj M))
  · intro b
    exact finiteModel_iso Λ _
      ((CondensedRing.upperStarComp Λ (SU.immersion b) j).app M).symm (hSU b)
  · intro b
    exact finiteModel_iso Λ _
      ((CondensedRing.upperStarComp Λ (SZ.immersion b) i).app M).symm (hSZ b)

variable (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ₀] [IsCommMonObj Λ₀]

private def mapRegularIso {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

private def pointFiniteFreeIso (X : Scheme.{u}) (r : ℕ) :
    ((upperStarFromPoint X).mapMod Λ₀).obj (Mod.finiteFree Λ₀ r) ≅
      Mod.finiteFree (condensedRingObj Λ₀ X) r := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : ((upperStarFromPoint X).mapMod Λ₀).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ((upperStarFromPoint X).mapMod Λ₀).mapBiproduct
      (fun _ : Fin r ↦ Mod.regular Λ₀) ≪≫
    biproduct.mapIso (fun _ ↦ mapRegularIso (upperStarFromPoint X) Λ₀)

private theorem lisse_finiteModel (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (hM : IsLisseCoefficientModule Λ₀ M) : HasFiniteConstantLocalModel Λ₀ X M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hU i
  refine ⟨Mod.finiteFree Λ₀ r, ⟨r, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨?_⟩⟩
  exact e ≪≫ (pointFiniteFreeIso Λ₀ (U.X i) r).symm

private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)


private theorem stratified_of_finiteModel (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (hM : HasFiniteConstantLocalModel Λ₀ X M) : IsFiniteConstantStratified Λ₀ X M := by
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  exact finiteModel_iso Λ₀ X ((CondensedRing.upperStarId Λ₀ X).app M).symm hM

private theorem stratified_openExtension {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₀ U))
    (hM : IsFiniteConstantStratified Λ₀ U M) :
    IsFiniteConstantStratified Λ₀ X ((CondensedRing.openImmersionLowerShriek Λ₀ j).obj M) := by
  have : IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ₀ j).unit :=
    CondensedRing.openUnitIsIso Λ₀ j
  apply stratified_of_restrictions Λ₀ j j.closedComplement
    (by simp)
  · obtain ⟨R, hR⟩ := hM
    refine ⟨R, fun a ↦ ?_⟩
    exact finiteModel_iso Λ₀ _
      ((CondensedRing.upperStar Λ₀ (R.immersion a)).mapIso
        (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ₀ j).unit.app M)))
      (hR a)
  · apply finiteConstantStratified_of_isZero
    have hz := pullback_lowerShriek_isZero j j.closedComplement
      (by rw [j.range_closedComplement]; exact Set.inter_compl_self _) M.X
    have hz' := hz.of_iso
      ((profinitePointModuleForgetPullbackIso Λ₀ j.closedComplement).app
        ((CondensedRing.openImmersionLowerShriek Λ₀ j).obj M))
    apply (IsZero.iff_id_eq_zero _).2
    apply (Mod.forget _).map_injective
    exact hz'.eq_of_src _ _

private theorem stratified_closedPush {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ₀ Z))
    (hM : IsFiniteConstantStratified Λ₀ Z M) :
    IsFiniteConstantStratified Λ₀ X ((CondensedRing.lowerStar Λ₀ i).obj M) := by
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hij : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  have hji : Set.range i = (Set.range U.ι)ᶜ := by rw [hij, compl_compl]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩ :=
    CondensedRing.condensed_open_closed_recollement Λ₀ i U.ι hij
  apply stratified_of_restrictions Λ₀ U.ι i hji
  · exact finiteConstantStratified_of_isZero Λ₀ _ _
      (CondensedRing.openRestrictionPushforwardZero Λ₀ i U.ι hij M)
  · obtain ⟨R, hR⟩ := hM
    refine ⟨R, fun a ↦ ?_⟩
    exact finiteModel_iso Λ₀ _
      ((CondensedRing.upperStar Λ₀ (R.immersion a)).mapIso (e.app M).symm) (hR a)

private theorem single_constructible (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (hM : IsConstantModelConstructible Λ₀ X M) :
    constantModelBoundedConstructible Λ₀ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X)
  let K := (DerivedCategory.singleFunctor A 0).obj M
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ₀ X) :=
    (constantModelConstructibleFiniteTor_wellDefined Λ₀ X).1
  constructor
  · exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  · intro q
    by_cases hq : q = 0
    · subst q
      exact (show ObjectProperty A from IsConstantModelConstructible Λ₀ X).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M).symm hM
    · apply constantModelConstructible_of_isZero
      rcases lt_or_gt_of_ne hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE K 0 q hq
      · exact DerivedCategory.isZero_of_isLE K 0 q hq

/-- The degree-zero derived object of a lisse locally closed extension is bounded
constructible for the finite-constant-model convention.

Source: blueprint generation, Converse paragraph; Stacks Tags 09AA, 09BM, 09BN, 09AH,
and 09AG (blueprint: lem-sfb-coefficient-heart-lisse-extension-constructible).

Proof: factor a through its scheme-theoretic closure as an open immersion followed by
a closed immersion. Both ambient spaces are topologically Noetherian, so all their
opens are quasi-compact, as are the complementary open immersions. The ringed
open-closed formulas and Cartesian coefficient comparisons identify the three
restrictions of i_*u_!L with L on S and zero on the two complementary pieces. These
are locally finite free, including rank zero on the complements. The finite-constant
local model criterion gives constructibility of i_*u_!L on this finite constructible
stratification. Its degree-zero complex has only this cohomology sheaf, and therefore
is bounded constructible. Empty pieces may be discarded; the zero and empty cases
require no separate hypothesis. -/
theorem coefficientHeart_lisse_extension_constructible (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    constantModelBoundedConstructible (coefficientHeartRingObj Λ) X
      ((DerivedCategory.singleFunctor _ 0).obj
        ((coefficientHeartLocallyClosedExtension (coefficientHeartRingObj Λ) a ha).obj L))  := by
  have : IsImmersion a := ha
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have hL' := stratified_of_finiteModel (coefficientHeartRingObj Λ) S L
    (lisse_finiteModel (coefficientHeartRingObj Λ) S L hL)
  have hu := stratified_openExtension (coefficientHeartRingObj Λ) a.toImage L hL'
  have hi := stratified_closedPush (coefficientHeartRingObj Λ) a.imageι _ hu
  apply single_constructible (coefficientHeartRingObj Λ) X
  have hcpt : CompactSpace X := inferInstance
  have hqs : QuasiSeparatedSpace X := inferInstance
  change IsConstantModelConstructible (coefficientHeartRingObj Λ) X _
  rw [IsConstantModelConstructible, if_pos (And.intro hcpt hqs)]
  exact hi

end AlgebraicGeometry.ProEtale
