/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedReconstruction
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

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
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

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

private theorem filtrationEssentiallySmall
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C
attribute [local instance 2000] filtrationEssentiallySmall

namespace CondensedRing

-- Use the earlier abelian support and module-transport interfaces directly. The
-- generator-tensor module containing analogous private wrappers imports this file.
attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction upperStar upperStarComp upperStarCongr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedOpen_to_closure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S V X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a]
    (t : S ⟶ V) [IsClosedImmersion t] (v : V ⟶ X) [IsOpenImmersion v]
    (htv : t ≫ v = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M) ≅
      (coefficientHeartLocallyClosedExtension Λ a inferInstance).obj M) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian a.image := LocallyOfFiniteType.isLocallyNoetherian a.imageι
  have : TopologicalSpace.NoetherianSpace a.image :=
    a.imageι.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian a.image := ⟨⟩
  let N := (openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M)
  have hs {Y : Scheme.{u}} (g : Y ⟶ X)
      (hg : Disjoint (Set.range g) (Set.range a)) :
      IsZero ((upperStar Λ g).obj N) := by
    have hdis : Disjoint (Set.range (pullback.snd g v)) (Set.range t) := by
      rw [Set.disjoint_left]
      rintro x ⟨y, rfl⟩ ⟨z, hz⟩
      apply Set.disjoint_left.mp hg
        (show v (pullback.snd g v y) ∈ Set.range g from
          ⟨pullback.fst g v y, by
            exact congrArg (fun f : pullback g v ⟶ X ↦ f y) pullback.condition⟩)
      exact ⟨z, (congrArg (fun f : S ⟶ X ↦ f z) htv).symm.trans (congrArg v hz)⟩
    let O : V.Opens := ⟨(Set.range t)ᶜ, t.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hO : Set.range O.ι = (Set.range t)ᶜ := O.range_ι
    have hfactor : Set.range (pullback.snd g v) ⊆ Set.range O.ι := by
      rw [hO]
      exact hdis.subset_compl_right
    let f := IsOpenImmersion.lift O.ι (pullback.snd g v) hfactor
    have hf : f ≫ O.ι = pullback.snd g v := IsOpenImmersion.lift_fac _ _ hfactor
    have hz := ((upperStar Λ f).map_isZero
      (openRestrictionPushforwardZero Λ t O.ι hO M)).of_iso
        ((upperStarCongr Λ hf.symm).app _ ≪≫ (upperStarComp Λ f O.ι).app _)
    have hz' := ((Mod.forget _).map_isZero hz).of_iso
      (upperStarObjXIso Λ (pullback.snd g v) _).symm
    have ebc := (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
      (IsPullback.of_hasPullback g v).flip).app ((lowerStar Λ t).obj M).X
    exact isZero_of_isZero_X Λ
      (((ProEtale.openImmersionLowerShriek Ab.{u + 1} (pullback.fst g v)).map_isZero
        hz').of_iso (upperStarObjXIso Λ g _ ≪≫ ebc.symm))
  have hc : IsIso (upperStarLowerStarAdjunction Λ t).counit :=
    moduleCounitOfAbelian Λ t (ProEtale.abelian_closed_counit t)
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ v).unit :=
    openUnitIsIso Λ v
  let e : (upperStar Λ a).obj N ≅ M :=
    ((upperStarCongr Λ htv.symm).app N) ≪≫
      ((upperStarComp Λ t v).app N) ≪≫
      (upperStar Λ t).mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
          ((lowerStar Λ t).obj M))).symm ≪≫
      asIso ((upperStarLowerStarAdjunction Λ t).counit.app M)
  let U : X.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range a.imageι)ᶜ := by
    exact U.range_ι
  have houter : Disjoint (Set.range U.ι) (Set.range a) := by
    rw [hU, Set.disjoint_left]
    rintro x hx ⟨z, rfl⟩
    apply hx
    exact ⟨a.toImage z, (congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).symm⟩
  have houterAb := ((Mod.forget _).map_isZero (hs U.ι houter)).of_iso
    (upperStarObjXIso Λ U.ι N).symm
  have ho := moduleUnitOfAbelian Λ a.imageι N
    ((ProEtale.abelian_closed_support_counit_and_unit a.imageι U.ι hU).2 N.X houterAb)
  have hd : Disjoint (Set.range (a.toImage.closedComplement ≫ a.imageι))
      (Set.range a) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    have he : a.toImage z = a.toImage.closedComplement y :=
      a.imageι.isEmbedding.injective
        ((congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).trans hz)
    have hy : a.toImage.closedComplement y ∈ (Set.range a.toImage)ᶜ := by
      rw [← a.toImage.range_closedComplement]
      exact ⟨y, rfl⟩
    exact hy ⟨z, he⟩
  have hz := (hs (a.toImage.closedComplement ≫ a.imageι) hd).of_iso
    ((upperStarComp Λ a.toImage.closedComplement a.imageι).app N).symm
  have hzAb := ((Mod.forget _).map_isZero hz).of_iso
    (upperStarObjXIso Λ a.toImage.closedComplement _).symm
  have hopenAb := ProEtale.abelian_open_supported_counit
    a.toImage.closedComplement a.toImage
    (by rw [a.toImage.range_closedComplement, compl_compl])
    ((upperStar Λ a.imageι).obj N).X hzAb
  have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
      ((upperStar Λ a.imageι).obj N)) := by
    apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
    apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ a.toImage
    exact (Adjunction.isIso_counit_app_iff_mem_essImage _).1 hopenAb
  refine ⟨asIso ((upperStarLowerStarAdjunction Λ a.imageι).unit.app N) ≪≫
    (lowerStar Λ a.imageι).mapIso
      (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
        ((upperStar Λ a.imageι).obj N))).symm ≪≫ ?_⟩
  exact (lowerStar Λ a.imageι).mapIso ((openImmersionLowerShriek Λ a.toImage).mapIso
    (((upperStarComp Λ a.toImage a.imageι).symm ≪≫
      upperStarCongr Λ a.toImage_imageι).app N ≪≫ e))

end CondensedRing

attribute [local irreducible] CondensedRing.openImmersionLowerShriekUpperStarAdjunction
  CondensedRing.upperStarLowerStarAdjunction coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  CondensedRing.upperStarComp CondensedRing.upperStarCongr

private theorem evaluated_cokernel
    {C D : Type*} [Category C] [Category D] [Abelian D]
    {P Q H : C ⥤ D} (d : P ⟶ Q) (e : cokernel d ≅ H) (F : C) :
    Nonempty (cokernel (d.app F) ≅ H.obj F) := by
  let ev := (evaluation C D).obj F
  exact ⟨(PreservesCokernel.iso ev d).symm ≪≫ e.app F⟩

-- Keep the representative transport abstract, so it does not unfold the scheme
-- pullback and open-extension definitions while transporting a dependent cokernel.
private theorem image_subobject_cokernel
    {C : Type*} [Category C] [Abelian C] {B A₁ A₂ : C}
    (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g]
    (d : A₁ ⟶ A₂) (hd : d ≫ g = f)
    (h : imageSubobject f ≤ imageSubobject g) :
    Nonempty (cokernel (Subobject.ofLE _ _ h) ≅ cokernel d) := by
  have aux (P Q : Subobject B) (hP : P = Subobject.mk f) (hQ : Q = Subobject.mk g)
      (hPQ : P ≤ Q) : Nonempty (cokernel (Subobject.ofLE P Q hPQ) ≅ cokernel d) := by
    subst P
    subst Q
    exact ⟨Subobject.cokernelOfLEMkIso f g (Iso.refl _) d (by simpa using hd.symm) hPQ⟩
  exact aux _ _ (imageSubobject_mono _) (imageSubobject_mono _) h

-- Work with the counits as variables when comparing their actual image subobjects.
private theorem successor_image_quotient
    {C : Type*} [Category C] [Abelian C] {P Q H : C ⥤ C}
    (εP : P ⟶ 𝟭 C) (εQ : Q ⟶ 𝟭 C)
    (hP : ∀ F, Mono (εP.app F)) (hQ : ∀ F, Mono (εQ.app F))
    (hs : ∃ d : P ⟶ Q, d ≫ εQ = εP ∧ Nonempty (cokernel d ≅ H)) (F : C) :
    ∃ h : imageSubobject (εP.app F) ≤ imageSubobject (εQ.app F),
      Nonempty (cokernel (Subobject.ofLE _ _ h) ≅ H.obj F) := by
  obtain ⟨d, hd, ⟨ed⟩⟩ := hs
  have := hP F
  have := hQ F
  have hdF : d.app F ≫ εQ.app F = εP.app F := congr_app hd F
  have h : imageSubobject (εP.app F) ≤ imageSubobject (εQ.app F) := by
    rw [imageSubobject_mono, imageSubobject_mono]
    exact Subobject.mk_le_mk_of_comm (d.app F) hdF
  refine ⟨h, ?_⟩
  obtain ⟨e⟩ := image_subobject_cokernel (εP.app F) (εQ.app F) (d.app F) hdF h
  obtain ⟨e'⟩ := evaluated_cokernel d ed F
  exact ⟨e ≪≫ e'⟩

-- The successor interface compares the actual chosen image subobjects and closure extension.
private theorem nestedOpen_quotient
    {X : Scheme.{u}} [IsNoetherian X] (W T : X.Opens) (hWT : W ≤ T)
    {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (t : S ⟶ T.toScheme) [IsClosedImmersion t] (htv : t ≫ T.ι = a)
    (ht : Set.range t = {x | T.ι x ∉ W})
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ h : coefficientHeartFiltrationStep Λ F W ≤ coefficientHeartFiltrationStep Λ F T,
      Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
        (coefficientHeartLocallyClosedExtension Λ a inferInstance).obj
          ((CondensedRing.upperStar Λ a).obj F)) := by
  classical
  obtain ⟨h, he⟩ := successor_image_quotient
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ W.ι).counit
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ T.ι).counit
    (CondensedRing.mono_condensed_counit Λ W.ι)
    (CondensedRing.mono_condensed_counit Λ T.ι)
    (CondensedRing.exists_openFiltrationSuccessor Λ W T hWT t ht) F
  refine ⟨h, ?_⟩
  obtain ⟨e⟩ := he
  let M := (CondensedRing.upperStar Λ a).obj F
  let er : (CondensedRing.upperStar Λ t).obj ((CondensedRing.upperStar Λ T.ι).obj F) ≅ M :=
    ((CondensedRing.upperStarComp Λ t T.ι).symm ≪≫
      CondensedRing.upperStarCongr Λ htv).app F
  obtain ⟨ec⟩ := CondensedRing.closedOpen_to_closure Λ a t T.ι htv M
  exact ⟨e ≪≫
    (CondensedRing.openImmersionLowerShriek Λ T.ι).mapIso
      ((CondensedRing.lowerStar Λ t).mapIso er) ≪≫ ec⟩

-- The filtration construction is independent of the coefficient-specific lisseness criterion.
private theorem openPrefix_filtration
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (R : X.FiniteLocallyClosedStratification)
    (V : Fin (R.n + 1) → X.Opens)
    (hV : ∀ k : Fin (R.n + 1),
      (V k : Set X) = ⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) :
    (∀ k : Fin (R.n + 1),
      Mono (coefficientHeartOpenCounit Λ F (V k))) ∧
    coefficientHeartFiltrationStep Λ F (V 0) = ⊥ ∧
    coefficientHeartFiltrationStep Λ F (V (Fin.last R.n)) = ⊤ ∧
    ∃ h : ∀ a : Fin R.n,
      coefficientHeartFiltrationStep Λ F (V a.castSucc) ≤
        coefficientHeartFiltrationStep Λ F (V a.succ),
      ∀ a : Fin R.n,
        Nonempty (cokernel (Subobject.ofLE
          (coefficientHeartFiltrationStep Λ F (V a.castSucc))
          (coefficientHeartFiltrationStep Λ F (V a.succ)) (h a)) ≅
          (coefficientHeartLocallyClosedExtension Λ
            (R.immersion a) (R.isImmersion a)).obj
              ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) := by
  classical
  let ε (W : X.Opens) := coefficientHeartOpenCounit Λ F W
  have hm (W : X.Opens) : Mono (ε W) :=
    CondensedRing.mono_condensed_counit Λ W.ι F
  have h0 : V 0 = ⊥ := by
    ext x
    simp [hV]
  have htop : V (Fin.last R.n) = ⊤ := by
    apply SetLike.coe_injective
    rw [hV]
    simpa using R.iUnion_stratum_eq_univ
  have hnest (a : Fin R.n) : V a.castSucc ≤ V a.succ := by
    intro x hx
    rw [← SetLike.mem_coe, hV] at hx ⊢
    obtain ⟨b, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hb, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by simpa using Nat.lt_succ_of_lt hb, hx⟩⟩
  have hbot : coefficientHeartFiltrationStep Λ F (V 0) = ⊥ := by
    have : Mono (coefficientHeartOpenCounit Λ F (V 0)) := hm _
    rw [coefficientHeartFiltrationStep, imageSubobject_mono]
    apply Subobject.mk_eq_bot_iff_zero.mpr
    have hz : IsZero ((CondensedRing.upperStar Λ (V 0).ι).obj F) := by
      have : IsEmpty (V 0).toScheme := ⟨fun x ↦ by
        have hx : x.val ∈ (V 0 : Set X) := x.2
        have hempty : (V 0 : Set X) = ∅ := congrArg SetLike.coe h0
        exact Set.notMem_empty x.val (hempty ▸ hx)⟩
      exact CondensedRing.module_zero_of_empty _ _
    have hz' : IsZero (coefficientHeartOpenTerm Λ F (V 0)) :=
      (CondensedRing.openImmersionLowerShriek Λ (V 0).ι).map_isZero hz
    exact hz'.eq_of_src (coefficientHeartOpenCounit Λ F (V 0)) 0
  have hlast : coefficientHeartFiltrationStep Λ F (V (Fin.last R.n)) = ⊤ := by
    have : Mono (coefficientHeartOpenCounit Λ F (V (Fin.last R.n))) := hm _
    rw [coefficientHeartFiltrationStep, imageSubobject_mono]
    have hi : IsIso (coefficientHeartOpenCounit Λ F (V (Fin.last R.n))) := by
      have : IsIso (V (Fin.last R.n)).ι := by
        apply (isIso_iff_isOpenImmersion_and_surjective _).2
        refine ⟨inferInstance, ⟨?_⟩⟩
        intro x
        have hx : x ∈ (V (Fin.last R.n) : Set X) := by
          simp only [htop, TopologicalSpace.Opens.coe_top, Set.mem_univ]
        exact ⟨⟨x, hx⟩, rfl⟩
      exact CondensedRing.iso_condensed_counit Λ _ F
    exact Subobject.mk_eq_top_of_isIso _
  have hs (a : Fin R.n) :
      ∃ h : coefficientHeartFiltrationStep Λ F (V a.castSucc) ≤
          coefficientHeartFiltrationStep Λ F (V a.succ),
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          (coefficientHeartLocallyClosedExtension Λ
            (R.immersion a) (R.isImmersion a)).obj
            ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) := by
    let W := V a.castSucc
    let T := V a.succ
    have haT : R.stratum a ⊆ (T : Set X) := by
      intro x hx
      rw [show (T : Set X) = _ from hV a.succ]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨Nat.lt_succ_self _, hx⟩⟩
    have hdiff (x : T.toScheme) : T.ι x ∉ W ↔ T.ι x ∈ R.stratum a := by
      constructor
      · intro hx
        have hxT : T.ι x ∈ (T : Set X) := x.property
        rw [show (T : Set X) = _ from hV a.succ] at hxT
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxT
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        by_cases hba : b = a
        · simpa [hba] using hxb
        · apply False.elim (hx ?_)
          rw [← SetLike.mem_coe, show (W : Set X) = _ from hV a.castSucc]
          refine Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨?_, hxb⟩⟩
          have hne : b.val ≠ a.val := fun h ↦ hba (Fin.ext h)
          change b.val < a.val
          change b.val < a.val + 1 at hb
          omega
      · intro hx hxW
        rw [← SetLike.mem_coe, show (W : Set X) = _ from hV a.castSucc] at hxW
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxW
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        have hba : b ≠ a := by
          intro he
          subst b
          exact (Nat.lt_irrefl a.val) hb
        exact Set.disjoint_left.mp (R.pairwise_disjoint_stratum hba) hxb hx
    have : IsImmersion (R.immersion a) := R.isImmersion a
    let t := IsOpenImmersion.lift T.ι (R.immersion a) (by
      rw [T.range_ι, R.range_immersion]
      exact haT)
    have htv : t ≫ T.ι = R.immersion a := IsOpenImmersion.lift_fac _ _ _
    have : IsImmersion (t ≫ T.ι) := htv.symm ▸ inferInstance
    have : IsImmersion t := IsImmersion.of_comp t T.ι
    have ht : Set.range t = {x | T.ι x ∉ W} := by
      ext x
      rw [Set.mem_ofPred_eq, hdiff]
      constructor
      · rintro ⟨y, rfl⟩
        rw [← R.range_immersion a]
        exact ⟨y, (congrArg (fun f ↦ f y) htv).symm⟩
      · intro hx
        rw [← R.range_immersion a] at hx
        obtain ⟨y, hy⟩ := hx
        refine ⟨y, T.ι.isEmbedding.injective ?_⟩
        exact (congrArg (fun f ↦ f y) htv).trans hy
    have : IsClosedImmersion t := IsClosedImmersion.of_isPreimmersion t (by
      rw [ht]
      exact (W.isOpen.preimage T.ι.continuous).isClosed_compl)
    exact nestedOpen_quotient Λ W T (hnest a) (R.immersion a) t htv ht F
  exact ⟨fun k ↦ hm (V k), hbot, hlast, Classical.axiomOfChoice hs⟩

set_option linter.unusedVariables false in
/-- The given ordered adapted stratification produces the counit filtration, with its
successive quotients the extensions by zero of the lisse restrictions. `V` is simply a
presentation of the open prefixes; its carrier equation fixes every V_k, including
V_0 and V_m. No connectedness or strictness condition is imposed.

Source: blueprint sk-lem-coefficient-heart-filtration and its proof
(blueprint: det-lem-coefficient-heart-filtration).

Proof:
1. The actual open counits are monic. The empty prefix has zero restriction and zero
extension; the full prefix inclusion is an isomorphism. Their images are therefore
bottom and top.
2. Consecutive open prefixes differ by exactly the given stratum. Lift its immersion
into the larger prefix and use its closed image to obtain a closed immersion there.
The open-filtration successor theorem gives a map between the two open extensions,
its counit identity over F, and its cokernel. Monicity identifies the counit images
with their represented subobjects. The existing subobject cokernel comparison and
preservation of cokernels by evaluation give the required quotient object.
3. The closed-then-open extension vanishes after restriction along every map whose
image misses the stratum. Its restriction to the stratum is the original module,
by the open unit and closed counit. Closed support reconstructs it from the closure;
open support inside the closure reconstructs it from the stratum. Composing these
adjunction isomorphisms gives the specified open-then-closed extension.
4. The existing common-stratification lisse theorem, applied to the stratification
and its identity refinement, makes every adapted restriction lisse. -/
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
  obtain ⟨hm, hbot, htop, h, eh⟩ := openPrefix_filtration (coefficientHeartRingObj L) X F R V hV
  refine ⟨hm, hbot, htop, h, fun a ↦ ⟨eh a, ?_⟩⟩
  exact (coefficientHeart_commonStratification_lisse ℓ L X hL).2 R R F hadapt
    (fun a ↦ ⟨a, Set.Subset.rfl⟩) a

end AlgebraicGeometry.ProEtale
