/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.CoefficientHeartCommonStratification
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
import Sheaf.Paper.CoefficientHeartFiltrationCore
import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.ContinuousConstructibleIntegralGluing
import WeilConjectures.ConstructibleSheaf.Devissage

/-!
# The filtration associated to an adapted coefficient stratification

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-filtration.md and its proof
(blueprint: det-lem-coefficient-heart-filtration).

The filtration steps are the images of the actual open-extension counits. The theorem
asserts that those counits are monomorphisms, so the images represent exactly the given
extensions by zero as subsheaves of F. Locally closed extension is the open extension
into the scheme-theoretic closure followed by its closed direct image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def cokernelSubobjectCongr {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasCokernels C] {F : C} {A B A' B' : Subobject F}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    cokernel (Subobject.ofLE A B h) ≅ cokernel (Subobject.ofLE A' B' h') := by
  subst A'
  subst B'
  exact Iso.refl _

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The specified object `v_! v^* F` for an open subscheme V.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of F_k
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartOpenTerm {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) :=
  (CondensedRing.openImmersionLowerShriek Λ V.ι).obj
    ((CondensedRing.upperStar Λ V.ι).obj F)

/-- The canonical map from the open-extension term to F, namely the adjunction counit.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of the inclusions
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartOpenCounit {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : coefficientHeartOpenTerm Λ F V ⟶ F :=
  (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit.app F

/-- The open counit is monic for every module, without constructibility hypotheses.
Source: the open-adjunction argument of the filtration proof
(blueprint: det-lem-coefficient-heart-filtration). -/
private theorem coefficientHeartOpenCounit_mono {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : Mono (coefficientHeartOpenCounit Λ F V) :=
  CondensedRing.mono_condensed_counit Λ V.ι F

/-- The subsheaf represented by the image of the canonical counit. Its equality with the
open-extension object as a subsheaf follows from the monomorphism assertion below.
Source: blueprint sk-lem-coefficient-heart-filtration, F_k as a subsheaf of F
(blueprint: det-lem-coefficient-heart-filtration). -/
abbrev coefficientHeartFiltrationStep {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : Subobject F :=
  imageSubobject (coefficientHeartOpenCounit Λ F V)

/-- For a locally closed immersion a into a topologically Noetherian scheme, use its
canonical scheme-theoretic closure: `a.toImage` is open and `a.imageι` is closed.
The source is topologically Noetherian because an immersion is a topological embedding;
therefore a is quasi-compact and the existing open-immersion instance for `a.toImage`
applies. No choice of an extension functor is made.
Source: blueprint sk-lem-coefficient-heart-filtration, definition `a_! = i_* u_!`
(blueprint: det-lem-coefficient-heart-filtration). -/
def coefficientHeartLocallyClosedExtension {S X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  CondensedRing.openImmersionLowerShriek Λ a.toImage ⋙ CondensedRing.lowerStar Λ a.imageι

private theorem coefficientHeart_localQuotient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U V : X.Opens) (h : U ≤ V)
    {S : Scheme.{u}} (a : S ⟶ X) (ha : IsImmersion a)
    (hrange : Set.range a = (V : Set X) \ (U : Set X)) :
    Nonempty (
      (CondensedRing.openImmersionLowerShriek Λ V.ι).obj
        (cokernel ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ
          (X.homOfLE h)).counit.app ((CondensedRing.upperStar Λ V.ι).obj F))) ≅
      (coefficientHeartLocallyClosedExtension Λ a ha).obj
        ((CondensedRing.upperStar Λ a).obj F)) := by
  have : IsImmersion a := ha
  let c : S ⟶ V := IsOpenImmersion.lift V.ι a (by
    rw [Scheme.Opens.range_ι, hrange]
    exact Set.sdiff_subset)
  have hc : c ≫ V.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hcrange : Set.range c = V.ι ⁻¹' ((V : Set X) \ (U : Set X)) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      rw [Set.mem_preimage]
      rw [← hrange]
      exact ⟨s, (congrArg (fun f : S ⟶ X ↦ f s) hc).symm⟩
    · intro hy
      obtain ⟨s, hs⟩ := hrange.symm ▸ hy
      refine ⟨s, V.ι.isEmbedding.injective ?_⟩
      exact (congrArg (fun f : S ⟶ X ↦ f s) hc).trans hs
  have : IsImmersion (c ≫ V.ι) := hc.symm ▸ ha
  have : IsImmersion c := IsImmersion.of_comp c V.ι
  have : IsClosedImmersion c := IsClosedImmersion.of_isPreimmersion c (by
    rw [hcrange]
    have heq : V.ι ⁻¹' ((V : Set X) \ (U : Set X)) =
        (V.ι ⁻¹' (U : Set X))ᶜ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff]
      exact and_iff_right y.property
    rw [heq]
    exact (U.isOpen.preimage V.ι.continuous).isClosed_compl)
  have hij : Set.range (X.homOfLE h) = (Set.range c)ᶜ := by
    rw [hcrange]
    ext y
    constructor
    · rintro ⟨x, rfl⟩ hy
      apply hy.2
      change ((X.homOfLE h) x).val ∈ U
      rw [Scheme.homOfLE_apply]
      exact x.property
    · intro hy
      have hyU : V.ι y ∈ (U : Set X) := by
        by_contra hn
        exact hy ⟨y.property, hn⟩
      refine ⟨⟨y.val, hyU⟩, ?_⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply h _
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let G := (CondensedRing.upperStar Λ V.ι).obj F
  let Q := cokernel ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ
    (X.homOfLE h)).counit.app G)
  have : TopologicalSpace.NoetherianSpace V :=
    V.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (X.homOfLE h) := inferInstance
  have hQ := CondensedRing.open_cokernel_zero Λ (X.homOfLE h) G
  have : IsIso ((CondensedRing.upperStarLowerStarAdjunction Λ c).unit.app Q) :=
    CondensedRing.supported_unit Λ c (X.homOfLE h) hij Q hQ
  let eQ : Q ≅ (CondensedRing.lowerStar Λ c).obj
      ((CondensedRing.upperStar Λ c).obj G) :=
    asIso ((CondensedRing.upperStarLowerStarAdjunction Λ c).unit.app Q) ≪≫
      (CondensedRing.lowerStar Λ c).mapIso
        (CondensedRing.closed_cokernel_iso Λ c (X.homOfLE h) hij G).symm
  let ePull : (CondensedRing.upperStar Λ c).obj G ≅
      (CondensedRing.upperStar Λ a).obj F :=
    ((CondensedRing.upperStarComp Λ c V.ι).app F).symm ≪≫
      (eqToIso (congrArg (CondensedRing.upperStar Λ) hc)).app F
  obtain ⟨e⟩ := coefficientHeart_filtration_core Λ c V.ι a ha hc
  exact ⟨(CondensedRing.openImmersionLowerShriek Λ V.ι).mapIso eQ ≪≫
    e.app _ ≪≫
      (CondensedRing.openImmersionLowerShriek Λ a.toImage ⋙
        CondensedRing.lowerStar Λ a.imageι).mapIso ePull⟩

/-- The given ordered adapted stratification produces the counit filtration, with its
successive quotients the extensions by zero of the lisse restrictions. `V` is simply a
presentation of the open prefixes; its carrier equation fixes every V_k, including
V_0 and V_m. No connectedness or strictness condition is imposed.

Source: blueprint sk-lem-coefficient-heart-filtration and its proof
(blueprint: det-lem-coefficient-heart-filtration).

Proof in words.
1. The proved condensed open-counit API in ContinuousConstructibleIntegralGluing
makes the counits monic. Composition of the open adjunctions and upperStarComp
factor the smaller counit through the larger one, so their images are nested.
The empty source has only zero modules, and the full-open counit is invertible;
these give the bottom and top endpoints.
2. The stratum is the closed complement of the previous prefix inside the next
prefix. The condensed localization lemmas open_cokernel_zero, supported_unit and
closed_cokernel_iso identify the local cokernel with direct image of the restriction
to this closed stratum. Preservation of cokernels by open extension, followed by
Subobject.cokernelOfLEMkIso, identifies the quotient of the image subobjects.
3. coefficientHeart_filtration_core compares this closed-then-open extension with
open extension into the scheme-theoretic image followed by closed direct image.
Functoriality of pullback identifies the coefficient object with restriction to
the original stratum.
4. The lisse restriction clause of coefficientHeart_commonStratification, applied
to the given stratification as its own refinement, makes each restriction lisse.
The inclusions can be equal, including for the zero sheaf. -/
theorem coefficientHeart_filtration (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X))
    (hF : IsConstantModelConstructible (coefficientHeartRingObj L) X F)
    (R : X.FiniteLocallyClosedStratification)
    (hadapt : ∀ a : Fin R.n,
      HasFiniteConstantLocalModel (coefficientHeartRingObj L) (R.domain a)
        ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F))
    (V : Fin (R.n + 1) → X.Opens)
    (hV : ∀ k : Fin (R.n + 1),
      (V k : Set X) = ⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) :
    (∀ k : Fin (R.n + 1),
      Mono (coefficientHeartOpenCounit (coefficientHeartRingObj L) F (V k))) ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V 0) = ⊥ ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V (Fin.last R.n)) = ⊤ ∧
    ∃ h : ∀ a : Fin R.n,
      coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc) ≤
        coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ),
      ∀ a : Fin R.n,
        Nonempty (cokernel (Subobject.ofLE
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc))
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ)) (h a)) ≅
          (coefficientHeartLocallyClosedExtension (coefficientHeartRingObj L)
            (R.immersion a) (R.isImmersion a)).obj
              ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F)) ∧
        IsLisseCoefficientModule (coefficientHeartRingObj L)
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F) := by
  have _ := hF
  let ε (W : X.Opens) := coefficientHeartOpenCounit (coefficientHeartRingObj L) F W
  have hε (W : X.Opens) : Mono (ε W) := coefficientHeartOpenCounit_mono
    (coefficientHeartRingObj L) F W
  have hmono (W : X.Opens) :
      Mono (coefficientHeartOpenCounit (coefficientHeartRingObj L) F W) := hε W
  simp_rw [coefficientHeartFiltrationStep, imageSubobject_mono]
  have hfac (U W : X.Opens) (h : U ≤ W) :
      ∃ α : (CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) U.ι).obj
          ((CondensedRing.upperStar (coefficientHeartRingObj L) U.ι).obj F) ≅
          (CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) W.ι).obj
            ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) (X.homOfLE h)).obj
              ((CondensedRing.upperStar (coefficientHeartRingObj L) (X.homOfLE h)).obj
                ((CondensedRing.upperStar (coefficientHeartRingObj L) W.ι).obj F))),
        ε U = α.hom ≫ (CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) W.ι).map
          ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficientHeartRingObj L)
            (X.homOfLE h)).counit.app ((CondensedRing.upperStar (coefficientHeartRingObj L)
              W.ι).obj F)) ≫ ε W := by
    obtain ⟨α, hα⟩ := Adjunction.exists_iso_counit_app
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficientHeartRingObj L) U.ι)
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficientHeartRingObj L)
        (X.homOfLE h)).comp
        (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficientHeartRingObj L) W.ι))
      (eqToIso (congrArg (CondensedRing.upperStar (coefficientHeartRingObj L)) (X.homOfLE_ι
        h).symm) ≪≫
        CondensedRing.upperStarComp (coefficientHeartRingObj L) (X.homOfLE h) W.ι) F
    exact ⟨α, hα.trans (by rw [Adjunction.comp_counit_app])⟩
  have hV0 : V 0 = ⊥ := by
    ext x
    simp [hV]
  have hVlast : V (Fin.last R.n) = ⊤ := by
    apply SetLike.coe_injective
    rw [hV]
    simpa using R.iUnion_stratum_eq_univ
  have hVle (a : Fin R.n) : V a.castSucc ≤ V a.succ := by
    intro x hx
    change x ∈ (V a.castSucc : Set X) at hx
    change x ∈ (V a.succ : Set X)
    rw [hV] at hx ⊢
    rcases Set.mem_iUnion.mp hx with ⟨b, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hb, hx⟩
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by
      change b.val < a.val at hb
      change b.val < a.val + 1
      omega, hx⟩⟩
  have hstep (a : Fin R.n) :
      Subobject.mk (ε (V a.castSucc)) ≤ Subobject.mk (ε (V a.succ)) := by
    obtain ⟨α, hα⟩ := hfac _ _ (hVle a)
    exact Subobject.mk_le_mk_of_comm (α.hom ≫ _) (by rw [hα, Category.assoc])
  refine ⟨fun k ↦ hε (V k), ?_, ?_, hstep, ?_⟩
  · apply Subobject.mk_eq_bot_iff_zero.mpr
    have hzero : IsZero ((CondensedRing.upperStar (coefficientHeartRingObj L) (V 0).ι).obj F) := by
      rw [hV0]
      have : IsEmpty (⊥ : X.Opens).toScheme :=
        ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
      exact CondensedRing.module_zero_of_empty _ _
    exact ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) (V
      0).ι).map_isZero hzero).eq_of_src _ _
  · have : IsIso (ε (V (Fin.last R.n))) := by
      change IsIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        (coefficientHeartRingObj L)
        (V (Fin.last R.n)).ι).counit.app F)
      rw [hVlast]
      have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
        inferInstanceAs (IsIso X.topIso.hom)
      exact CondensedRing.iso_condensed_counit (coefficientHeartRingObj L) _ F
    exact Subobject.mk_eq_top_of_isIso _
  · intro a
    constructor
    · have hrange : Set.range (R.immersion a) =
          (V a.succ : Set X) \ (V a.castSucc : Set X) := by
        rw [R.range_immersion, hV, hV]
        ext x
        simp only [Set.mem_sdiff, Set.mem_iUnion]
        constructor
        · intro hx
          refine ⟨⟨a, by simp, hx⟩, ?_⟩
          rintro ⟨b, hb, hbx⟩
          have hne : b ≠ a := by intro heq; subst b; simp at hb
          exact Set.disjoint_left.mp (R.pairwise_disjoint_stratum hne) hbx hx
        · rintro ⟨⟨b, hb, hx⟩, hnot⟩
          have hab : b = a := by
            apply Fin.ext
            by_contra hne
            exact hnot ⟨b, by dsimp at hb ⊢; omega, hx⟩
          simpa [hab] using hx
      obtain ⟨α, hα⟩ := hfac (V a.castSucc) (V a.succ) (hVle a)
      let φ := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        (coefficientHeartRingObj L)
        (X.homOfLE (hVle a))).counit.app
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (V a.succ).ι).obj F)
      let e₁ := Subobject.cokernelOfLEMkIso (ε (V a.castSucc)) (ε (V a.succ)) α
        ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) (V a.succ).ι).map
          φ) hα (hstep a)
      let e₂ := (PreservesCokernel.iso
        (CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj L) (V a.succ).ι) φ).symm
      obtain ⟨e⟩ := coefficientHeart_localQuotient (coefficientHeartRingObj L) F (V
        a.castSucc) (V a.succ)
        (hVle a) (R.immersion a) (R.isImmersion a) hrange
      have heq₀ := imageSubobject_mono (ε (V a.castSucc))
      have heq₁ := imageSubobject_mono (ε (V a.succ))
      exact ⟨cokernelSubobjectCongr heq₀ heq₁ _ _ ≪≫ e₁ ≪≫ e₂ ≪≫ e⟩
    · have hs := coefficientHeart_commonStratification ℓ L X hL
      exact hs.2.1.2 R R F hadapt (fun a ↦ ⟨a, Set.Subset.rfl⟩) a

end AlgebraicGeometry.ProEtale
