/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper

/-! # The proper counit restricted to the distinguished open component

Source: the clopen-section argument in Step 15 of the compact-support condensed
realization prerequisite, and Stacks Project, Tag 0F7B.
(blueprint: lem-pur-condensed-open-restricted-counit). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace WeilConjectures.CompactSupportCondensedRealization

-- Lift the fully faithful abelian direct image through the coefficient equivalence.
private noncomputable def openDirectImageFullyFaithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] : (CondensedRing.lowerStar Λ j).FullyFaithful := by
  let a := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).mapModAdjunction
    (condensedRingObj Λ T)
  have hf := (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
    ).fullyFaithfulROfIsIsoCounit
  have := hf.full
  have := hf.faithful
  have ha (M) : IsIso (a.counit.app M) := by
    have : IsIso ((Mod.forget _).map (a.counit.app M)) := by
      change IsIso (a.counit.app M).hom
      dsimp only [a]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso a.counit := NatIso.isIso_of_isIso_app _
  exact ((Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    a.fullyFaithfulROfIsIsoCounit).ofIso (CondensedRing.comapPullbackHomCompIso Λ j)

-- On a clopen, the underlying direct image lies in the image of extension by zero.
-- Its open counit and the direct-image counit therefore identify the two functors.
private noncomputable def clopenExtensionRightAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (hj : IsClosed (Set.range j)) :
    CondensedRing.upperStar Λ j ⊣ CondensedRing.openImmersionLowerShriek Λ j := by
  let J := CondensedRing.openImmersionLowerShriek Λ j
  let V := CondensedRing.upperStar Λ j
  let R := CondensedRing.lowerStar Λ j
  let a := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j
  let b := CondensedRing.upperStarLowerStarAdjunction Λ j
  have hf := openDirectImageFullyFaithful Λ j
  have := hf.full
  have := hf.faithful
  have : IsIso b.counit := b.counit_isIso_of_R_fully_faithful
  have hab : IsIso (ProEtale.openImmersionLowerShriekToLowerStar Ab.{u + 1} j) :=
    ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range _ j hj
  have hmem (M) : J.essImage (R.obj M) := by
    apply CondensedRing.mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ j
    exact ⟨M.X, ⟨(asIso (ProEtale.openImmersionLowerShriekToLowerStar
      Ab.{u + 1} j)).app M.X⟩⟩
  have ht (M) : IsIso (a.counit.app (R.obj M)) :=
    a.isIso_counit_app_iff_mem_essImage.mpr (hmem M)
  have : IsIso (Functor.whiskerLeft R a.counit) :=
    (NatTrans.isIso_iff_isIso_app _).mpr ht
  let e : J ≅ R :=
    (Functor.leftUnitor J).symm ≪≫
      Functor.isoWhiskerRight (asIso b.counit).symm J ≪≫
      Functor.associator R V J ≪≫ asIso (Functor.whiskerLeft R a.counit) ≪≫
      Functor.rightUnitor R
  exact b.ofNatIsoRight e.symm

-- A retraction makes the composite pullback an equivalence. Its counit factors
-- through the section counit, so restriction of the first counit is invertible.
private theorem sectionCounit
    {C A : Type*} [Category C] [Category A]
    {F : C ⥤ A} {R : A ⥤ C} {V : A ⥤ C} {J : C ⥤ A}
    (a : F ⊣ R) (b : V ⊣ J) (e : F ⋙ V ≅ 𝟭 C) (K : C)
    [J.Full] [J.Faithful] : IsIso (V.map (a.counit.app (J.obj K))) := by
  have : (F ⋙ V).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have : IsIso (a.comp b).counit := inferInstance
  have : IsIso (V.map (a.counit.app (J.obj K)) ≫ b.counit.app K) := by
    simpa only [Adjunction.comp_counit_app] using
      (inferInstance : IsIso ((a.comp b).counit.app K))
  exact IsIso.of_isIso_comp_right _ (b.counit.app K)

-- Invertibility survives changing the left adjoint while fixing the right adjoint.
private theorem mapCounitOfIsoLeft
    {C A B : Type*} [Category C] [Category A] [Category B]
    {F F' : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ R) (b : F' ⊣ R) (U : A ⥤ B) (M : A)
    [IsIso (U.map (b.counit.app M))] : IsIso (U.map (a.counit.app M)) := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit a b M, Functor.map_comp]
  infer_instance

/-- Restriction to the distinguished open makes the proper counit invertible on
extension by zero. Source: Step 15 of the compact-support condensed realization
prerequisite; Stacks Project, Tag 0F7B, clopen-section argument.
(blueprint: lem-pur-condensed-open-restricted-counit).

Proof: form W = c.Z ×[d.Z] X using d.i. The map (c.i, id) is an open section of
W → X. This projection is proper and hence separated, so its section is also closed.
Decompose W into that section and its open complement. Restriction of c.i_! K to W
is extension by zero from the section and vanishes on the complement. Restriction
along d.i commutes with derived direct image: open restriction is exact and its exact
left adjoint implies preservation of K-injectives by restriction. Compute the proper
counit on a K-injective resolution after this restriction. On the section its component
is the counit for the identity map of X and on the complementary component the input
is zero. Pulling back further along the section therefore gives an isomorphism. The
canonical inverse-image compositor identifies this map with the displayed restriction
of the original proper counit. These computations apply to arbitrary unbounded K:
only exact open restriction and the identity direct image on the supported component
are used. They also include the empty open and the identity refinement. -/
theorem condensedOpen_restrictedCounit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso ((CondensedRing.upperStar Λ c.i).leftDerivedFunctor.map
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K))) := by
  -- The refinement square need not be Cartesian; pull back its target open first.
  let g := pullback.fst r.hom d.i
  let p := pullback.snd r.hom d.i
  let s : X ⟶ pullback r.hom d.i :=
    pullback.lift c.i (𝟙 X) (by simpa using r.i_hom)
  have hsg : s ≫ g = c.i := pullback.lift_fst _ _ _
  have hsp : s ≫ p = 𝟙 X := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ g) := hsg ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s g
  have hc := (open_section_clopen p s hsp).1.isClosed
  let U := fun {A B : Scheme.{u}} (h : A ⟶ B) ↦
    (CondensedRing.upperStar Λ h).mapDerivedCategory
  let J := fun {A B : Scheme.{u}} (h : A ⟶ B) [IsOpenImmersion h] ↦
    (CondensedRing.openImmersionLowerShriek Λ h).mapDerivedCategory
  let ag := CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g
  let as := CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ s
  let ac := CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i
  let ar := (CondensedRing.upperStarLowerStarAdjunction Λ r.hom
    ).mapDerivedCategoryRightDerivedAdjunction
  let ap := (CondensedRing.upperStarLowerStarAdjunction Λ p
    ).mapDerivedCategoryRightDerivedAdjunction
  let bs := (clopenExtensionRightAdjunction Λ s hc).mapDerivedCategoryAdjunction
  have : IsIso ag.unit := by
    change IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      Λ g).mapDerivedCategoryAdjunction.unit
    infer_instance
  have : IsIso as.unit := by
    change IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      Λ s).mapDerivedCategoryAdjunction.unit
    infer_instance
  have hff := as.fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  let k : U c.i ≅ U g ⋙ U s :=
    eqToIso (congrArg (fun h ↦ U h) hsg.symm) ≪≫
      CondensedRing.openCoherenceRestrictionComp Λ s g
  -- Composition of open adjunctions identifies the restricted supported object.
  let ec : J c.i ≅ J s ⋙ J g := ac.leftAdjointUniq ((as.comp ag).ofNatIsoRight k.symm)
  let M := (J c.i).obj K
  let eM : (U g).obj M ≅ (J s).obj K :=
    (U g).mapIso (ec.app K) ≪≫ (asIso (ag.unit.app ((J s).obj K))).symm
  let ep : U p ⋙ U s ≅ 𝟭 _ :=
    (CondensedRing.openCoherenceRestrictionComp Λ s p).symm ≪≫
      eqToIso (congrArg (fun h ↦ U h) hsp) ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _
  have hs : IsIso ((U s).map (ap.counit.app ((J s).obj K))) :=
    sectionCounit ap bs ep K
  have hM : IsIso ((U s).map (ap.counit.app ((U g).obj M))) :=
    (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight ap.counit (U s)) eM).mpr hs
  let sq := (IsPullback.of_hasPullback r.hom d.i).toCommSq
  let β := CondensedRing.derivedDirectImageOpenRestriction Λ sq
  have hβ : IsIso β := (CondensedRing.derivedOpenRestrictionNormalization Λ
    (IsPullback.of_hasPullback r.hom d.i)).1
  -- The mate equation transfers the section calculation to the original counit.
  have hm := mateEquiv_counit ar ap
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedOpenCoherencePullbackSquare Λ sq).hom) M
  have hh : IsIso ((U s).map ((CondensedRing.derivedOpenCoherencePullbackSquare
      Λ sq).hom.app (_)) ≫ (U s).map ((U g).map (ar.counit.app M))) := by
    rw [← Functor.map_comp, ← hm, Functor.map_comp]
    change IsIso ((U s).map ((U p).map (β.app M)) ≫
      (U s).map (ap.counit.app ((U g).obj M)))
    infer_instance
  have hi : IsIso ((U s).map ((U g).map (ar.counit.app M))) :=
    IsIso.of_isIso_comp_left
      ((U s).map ((CondensedRing.derivedOpenCoherencePullbackSquare Λ sq).hom.app _)) _
  have hi' : IsIso ((U c.i).map (ar.counit.app M)) :=
    (NatIso.isIso_map_iff k (ar.counit.app M)).mpr hi
  -- Uniqueness compares the exact-left and total-derived adjunctions.
  let a := CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.hom
  have hi'' : IsIso ((U c.i).map (a.counit.app M)) :=
    mapCounitOfIsoLeft a ar (U c.i) M
  exact (NatIso.isIso_map_iff
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.i) _).mpr hi''

end WeilConjectures.CompactSupportCondensedRealization
