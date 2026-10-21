/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.ReesBaseChange
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.ReesConeNormalization
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.StalkFiniteFree
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.SectionReesNoetherianGeometry
import Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Functoriality of the extended-Rees deformation of a smooth section

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction, explicit base-change maps and etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).

The deformation, augmentation, punctured chart and two fibres are the existing
extended-Rees constructions. All maps below are fixed coefficientwise on every affine
restriction, including the quotient by t. Pushout assertions encode the displayed
canonical tensor-product isomorphisms, without a flatness hypothesis on the base map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace AlgebraicGeometry.SectionReesBaseChange

/-- The canonical conormal comparison already characterized by its adjunction and
representative formulas. Source: sk-thm-dnc, Local construction; Stacks 01R4
(blueprint: lem-trf-section-rees-base-change-etale). -/
def conormalMap {V V' S S' : Scheme.{u}} (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) :
    (Scheme.Modules.tensorPullback b).obj
        ((Scheme.Modules.tensorPullback s).obj s.ker.toModules) ⟶
      (Scheme.Modules.tensorPullback s').obj s'.ker.toModules :=
  Classical.choose ((Classical.choose_spec
    (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).2).2)

/-- The coefficientwise canonical map of Rees spaces for a commuting square of centres.
Source: sk-thm-dnc, Local construction, t and b/t
(blueprint: lem-trf-section-rees-base-change-etale). -/
def pairMap {V V' S S' : Scheme.{u}} (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) : s'.ker.deformationSpace ⟶ s.ker.deformationSpace :=
  Scheme.IdealSheafData.deformationSpaceMap h s.ker s'.ker fun {U' U} hU ↦
    (s.ker.ideal_map_appLE_le_ideal_comap h ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).1 ⟨U'.1, U'.2⟩)

/-- The affine coefficientwise comparison on the zero fibre, obtained by quotienting
the existing extended-Rees map by t. Source: sk-thm-dnc, Local construction; Stacks 0632
(blueprint: lem-trf-section-rees-base-change-etale). -/
def zeroAlgebraMap {R R' : Type u} [CommRing R] [CommRing R']
    (I : Ideal R) (J : Ideal R') (a : R →+* R') (ha : I.map a ≤ J) :
    I.extendedReesAlgebra ⧸ Ideal.span {I.extendedReesAlgebraT} →+*
      J.extendedReesAlgebra ⧸ Ideal.span {J.extendedReesAlgebraT} :=
  Ideal.quotientMap _ (I.extendedReesAlgebraMap a J ha)
    (Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.extendedReesAlgebraMap_T]))

/-- Compatibility with the augmented pair and both fibre identifications. The zero
and punctured maps are specified on EVERY affine restriction by their coefficient maps.
In particular the zero map is the associated-graded map, hence its degree-one map is
the canonical conormal comparison, rather than an arbitrary normal-bundle isomorphism.
Source: sk-thm-dnc, Local construction, restriction and homogeneous-class formulas
(blueprint: lem-trf-section-rees-base-change-etale). -/
def Compatible {V V' S S' : Scheme.{u}} (g : V ⟶ S) (g' : V' ⟶ S')
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (h : V' ⟶ V) (b : S' ⟶ S)
    (φ : s'.ker.deformationSpace ⟶ s.ker.deformationSpace) : Prop :=
  φ ≫ Scheme.Hom.deformationSpaceProj g s =
      Scheme.Hom.deformationSpaceProj g' s' ≫ AffineSpace.map (ULift.{u} (Fin 1)) b ∧
  s'.deformationSpaceSection ≫ φ =
      AffineSpace.map (ULift.{u} (Fin 1)) b ≫ s.deformationSpaceSection ∧
  Scheme.Hom.deformationSpaceOneFibre g' s' ≫ φ =
      h ≫ Scheme.Hom.deformationSpaceOneFibre g s ∧
  ∃ (ν : s'.ker.normalCone ⟶ s.ker.normalCone) (l : V'.laurentSpec ⟶ V.laurentSpec),
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ∃ ha : (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U',
        colimit.ι (relativeGluingData s'.ker.coequifibered_toReesPresheaf).functor U' ≫ φ =
          Spec.map (CommRingCat.ofHom ((s.ker.siteIdeal U).extendedReesAlgebraMap
            (h.appLE U.1 U'.1 hU).hom (s'.ker.siteIdeal U') ha)) ≫
              colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U) ∧
    ν ≫ s.ker.normalConeToDeformationSpace = s'.ker.normalConeToDeformationSpace ≫ φ ∧
    ν ≫ Scheme.Hom.normalConeProj g s = Scheme.Hom.normalConeProj g' s' ≫ b ∧
    s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection ∧
    l ≫ s.ker.laurentSpecToDeformationSpace = s'.ker.laurentSpecToDeformationSpace ≫ φ ∧
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      ∃ ha : (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U',
        colimit.ι (relativeGluingData s'.ker.coequifibered_toNormalConePresheaf).functor U' ≫ ν =
          Spec.map (CommRingCat.ofHom (zeroAlgebraMap (s.ker.siteIdeal U)
            (s'.ker.siteIdeal U') (h.appLE U.1 U'.1 hU).hom ha)) ≫
              colimit.ι (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).functor U) ∧
    (∀ (U' : V'.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      colimit.ι (relativeGluingData V'.coequifibered_toLaurentPresheaf).functor U' ≫ l =
        Spec.map (CommRingCat.ofHom
          (LaurentPolynomial.mapRingHom (h.appLE U.1 U'.1 hU).hom)) ≫
            colimit.ι (relativeGluingData V.coequifibered_toLaurentPresheaf).functor U)

private def laurentPairData {X X' : Scheme.{u}} (h : X' ⟶ X) :
    PullbackData h X.toLaurentPresheaf X'.toLaurentPresheaf where
  map hU := CommRingCat.laurentFunctor.map (h.appLE _ _ hU)
  map_naturality i' i h₁ h₂ := by
    have he := congrArg (CommRingCat.laurentFunctor.map)
      (h.affineStructurePresheaf_map_appLE i' i h₁ h₂)
    rw [Functor.map_comp, Functor.map_comp] at he
    exact he
  app_comp_map hU := (CommRingCat.laurentC.naturality _).symm

private theorem laurentPairData_toRees {X X' : Scheme.{u}} (h : X' ⟶ X)
    (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U') :
    (laurentPairData h).comparison _ _ ≫ I.laurentSpecToDeformationSpace =
      J.laurentSpecToDeformationSpace ≫
        Scheme.IdealSheafData.deformationSpaceMap h I J hJ := by
  exact PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
    (fun hU ↦ by ext x; rfl)

private theorem laurentPairData_toPolynomial {X X' : Scheme.{u}} (h : X' ⟶ X) :
    (laurentPairData h).comparison _ _ ≫ X.laurentSpecToPolynomialSpec =
      X'.laurentSpecToPolynomialSpec ≫ Scheme.polynomialSpecMap h := by
  exact PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
    (fun hU ↦ (CommRingCat.polynomialToLaurent.naturality _).symm)

private def oneLaurent {V S : Scheme.{u}} (g : V ⟶ S) : V ⟶ V.laurentSpec :=
  pullback.lift (𝟙 V) (g ≫ Scheme.Hom.oneSectionToPuncturedLine S) (by
    rw [Category.assoc, Scheme.Hom.oneSectionToPuncturedLine_ι_over,
      Category.id_comp, Category.comp_id]) ≫
        (Scheme.Hom.isPullback_laurentSpec g).isoPullback.inv

private theorem oneLaurent_toPolynomial {V S : Scheme.{u}} (g : V ⟶ S) :
    oneLaurent g ≫ V.laurentSpecToPolynomialSpec =
      AffineSpace.oneSection (ULift.{u} (Fin 1)) V ≫ inv V.polynomialSpecToAffineSpace := by
  apply (Scheme.Hom.isPullback_polynomialSpecProj g).hom_ext
  · simp only [oneLaurent, Category.assoc,
      IsPullback.isoPullback_inv_fst, pullback.lift_fst]
    rw [← Scheme.polynomialSpecToAffineSpace_over,
      IsIso.inv_hom_id_assoc, AffineSpace.oneSection_comp_over]
  · rw [Category.assoc, (Scheme.Hom.isPullback_laurentSpecToPuncturedLine g).w]
    simp only [oneLaurent, Category.assoc, IsPullback.isoPullback_inv_snd_assoc,
      pullback.lift_snd_assoc, Scheme.Hom.oneSectionToPuncturedLine_ι,
      IsIso.inv_hom_id_assoc, AffineSpace.oneSection_comp_map]

private theorem oneLaurent_naturality {V V' S S' : Scheme.{u}}
    (g : V ⟶ S) (g' : V' ⟶ S') (h : V' ⟶ V) :
    oneLaurent g' ≫ (laurentPairData h).comparison _ _ = h ≫ oneLaurent g := by
  apply (cancel_mono V.laurentSpecToPolynomialSpec).mp
  calc
    (oneLaurent g' ≫ (laurentPairData h).comparison _ _) ≫
        V.laurentSpecToPolynomialSpec =
      (oneLaurent g' ≫ V'.laurentSpecToPolynomialSpec) ≫ Scheme.polynomialSpecMap h := by
        rw [Category.assoc, laurentPairData_toPolynomial, ← Category.assoc]
    _ = (AffineSpace.oneSection (ULift.{u} (Fin 1)) V' ≫
        inv V'.polynomialSpecToAffineSpace) ≫ Scheme.polynomialSpecMap h := by
          rw [oneLaurent_toPolynomial]
    _ = h ≫ (AffineSpace.oneSection (ULift.{u} (Fin 1)) V ≫
        inv V.polynomialSpecToAffineSpace) := by
      apply (cancel_mono V.polynomialSpecToAffineSpace).mp
      simp only [Category.assoc, Category.comp_id, IsIso.inv_hom_id,
        Scheme.polynomialSpecMap_polynomialSpecToAffineSpace,
        IsIso.inv_hom_id_assoc, AffineSpace.oneSection_comp_map]
    _ = (h ≫ oneLaurent g) ≫ V.laurentSpecToPolynomialSpec := by
      rw [Category.assoc, oneLaurent_toPolynomial]

private theorem pairMap_oneFibre {V V' S S' : Scheme.{u}}
    (g : V ⟶ S) (g' : V' ⟶ S') (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) :
    Scheme.Hom.deformationSpaceOneFibre g' s' ≫ pairMap s s' h b w =
      h ≫ Scheme.Hom.deformationSpaceOneFibre g s := by
  change (oneLaurent g' ≫ s'.ker.laurentSpecToDeformationSpace) ≫
    Scheme.IdealSheafData.deformationSpaceMap h s.ker s'.ker _ =
      h ≫ (oneLaurent g ≫ s.ker.laurentSpecToDeformationSpace)
  rw [Category.assoc, ← laurentPairData_toRees, ← Category.assoc,
    oneLaurent_naturality, Category.assoc]

private def quotientPairData {X X' : Scheme.{u}} {h : X' ⟶ X}
    {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {F' : X'.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : X.affineStructurePresheaf ⟶ F} {α' : X'.affineStructurePresheaf ⟶ F'}
    (D : PullbackData h α α')
    (K : ∀ U, Ideal (F.obj U))
    (hK : ∀ ⦃U W⦄ (i : U ⟶ W), (K U).map (F.map i).hom = K W)
    (K' : ∀ U, Ideal (F'.obj U))
    (hK' : ∀ ⦃U W⦄ (i : U ⟶ W), (K' U).map (F'.map i).hom = K' W)
    (hD : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1), (K (op U)).map (D.map hU).hom ≤ K' (op U')) :
    PullbackData h (α ≫ Scheme.toQuotientPresheaf K hK)
      (α' ≫ Scheme.toQuotientPresheaf K' hK') where
  map hU := CommRingCat.ofHom (Ideal.quotientMap _ (D.map hU).hom
    (Ideal.map_le_iff_le_comap.mp (hD hU)))
  map_naturality i' i h₁ h₂ := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact congrArg (Ideal.Quotient.mk _)
      (ConcreteCategory.congr_hom (D.map_naturality i' i h₁ h₂) x)
  app_comp_map hU := by
    ext x
    exact congrArg (Ideal.Quotient.mk _)
      (ConcreteCategory.congr_hom (D.app_comp_map hU) x)

private def zeroPairData {X X' : Scheme.{u}} (h : X' ⟶ X)
    (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U') :
    PullbackData h (I.toReesPresheaf ≫
      Scheme.toQuotientPresheaf I.tIdeal I.map_tIdeal)
      (J.toReesPresheaf ≫ Scheme.toQuotientPresheaf J.tIdeal J.map_tIdeal) :=
  quotientPairData (Scheme.IdealSheafData.extendedReesPullbackData h I J hJ)
    I.tIdeal I.map_tIdeal J.tIdeal J.map_tIdeal fun {U' U} hU ↦ by
      change (Ideal.span {(I.siteIdeal U).extendedReesAlgebraT}).map
        ((I.siteIdeal U).extendedReesAlgebraMap (h.appLE U.1 U'.1 hU).hom
          (J.siteIdeal U') (hJ hU)) ≤
        Ideal.span {(J.siteIdeal U').extendedReesAlgebraT}
      rw [Ideal.map_span, Set.image_singleton, Ideal.extendedReesAlgebraMap_T]

private theorem zeroPairData_toRees {X X' : Scheme.{u}} (h : X' ⟶ X)
    (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U') :
    (zeroPairData h I J hJ).comparison _ _ ≫ I.normalConeToDeformationSpace =
      J.normalConeToDeformationSpace ≫
        Scheme.IdealSheafData.deformationSpaceMap h I J hJ := by
  exact PullbackData.comparison_comp_relativeGluingMap _ _ _ _ _ _ _ _
    (fun hU ↦ by ext x; rfl)

private theorem zeroPairData_isPullback {X X' : Scheme.{u}} (h : X' ⟶ X)
    (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')
    (hcov : ∀ x : X', ∃ (U' : X'.AffineZariskiSite) (U : X.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1), x ∈ U'.1 ∧
      IsPushout (h.appLE U.1 U'.1 hU) (I.toReesPresheaf.app (op U))
        (J.toReesPresheaf.app (op U'))
        ((Scheme.IdealSheafData.extendedReesPullbackData h I J hJ).map hU)) :
    IsPullback ((zeroPairData h I J hJ).comparison _ _)
      (relativeGluingData J.coequifibered_toNormalConePresheaf).toBase
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase h := by
  apply (zeroPairData h I J hJ).isPullback_comparison
    I.coequifibered_toNormalConePresheaf J.coequifibered_toNormalConePresheaf
  intro x
  obtain ⟨U', U, hU, hx, H⟩ := hcov x
  let r := (Scheme.IdealSheafData.extendedReesPullbackData h I J hJ).map hU
  have e : (I.tIdeal (op U)).map r.hom = J.tIdeal (op U') := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun t ↦ Ideal.span {t})
      (Ideal.extendedReesAlgebraMap_T _ _ (hJ hU))
  have Hq : IsPushout r (CommRingCat.ofHom (Ideal.Quotient.mk (I.tIdeal (op U))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.tIdeal (op U'))))
      (CommRingCat.ofHom (zeroAlgebraMap (I.siteIdeal U) (J.siteIdeal U')
        (h.appLE U.1 U'.1 hU).hom (hJ hU))) := by
    refine (CommRingCat.isPushout_quotient r (I.tIdeal (op U))).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Ideal.quotEquivOfEq e).toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext a; rfl
    · ext a; rfl
  exact ⟨U', U, hU, hx, H.paste_vert Hq⟩

private theorem rees_flat_pushout {R R' : Type u} [CommRing R] [CommRing R']
    (I : Ideal R) (J : Ideal R') (a : R →+* R') (ha : a.Flat)
    (hJ : I.map a = J) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom (algebraMap R I.extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap R' J.extendedReesAlgebra))
      (CommRingCat.ofHom (I.extendedReesAlgebraMap a J hJ.le)) := by
  subst J
  exact Ideal.isPushout_extendedReesAlgebraMap_of_flat a ha I

private theorem pairMap_section {V V' S S' : Scheme.{u}}
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (h : V' ⟶ V) (b : S' ⟶ S) (w : s' ≫ h = b ≫ s) :
    s'.deformationSpaceSection ≫ pairMap s s' h b w =
      AffineSpace.map (ULift.{u} (Fin 1)) b ≫ s.deformationSpaceSection := by
  let hJ : ∀ ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
    fun {U' U} hU ↦
    (s.ker.ideal_map_appLE_le_ideal_comap h ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).1 ⟨U'.1, U'.2⟩)
  have hsection : s'.affineSpaceToQuotientPolynomialSpec ≫
      (Scheme.IdealSheafData.quotientPolynomialPullbackData h s.ker s'.ker hJ).comparison _ _ =
      AffineSpace.map (ULift.{u} (Fin 1)) b ≫ s.affineSpaceToQuotientPolynomialSpec := by
    rw [← cancel_mono (relativeGluingMap V.coequifibered_toPolynomialPresheaf
      s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.polynomialToQuotientPolynomial),
      Category.assoc, PullbackData.comparison_comp_relativeGluingMap
        (H := V.coequifibered_toPolynomialPresheaf)
        (H' := V'.coequifibered_toPolynomialPresheaf) _ _ _ _ _ _
       (Scheme.IdealSheafData.polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
          _ _ _ _),
      Scheme.Hom.affineSpaceToQuotientPolynomialSpec_toPolynomialSpec_assoc, Category.assoc,
      Scheme.Hom.affineSpaceToQuotientPolynomialSpec_toPolynomialSpec,
      ← Scheme.polynomialSpecMap,
      (IsIso.eq_comp_inv _).mpr (Scheme.polynomialSpecMap_polynomialSpecToAffineSpace h)]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp_assoc, w]
  change s'.deformationSpaceSection ≫
    Scheme.IdealSheafData.deformationSpaceMap h s.ker s'.ker hJ = _
  rw [Scheme.Hom.deformationSpaceSection, Scheme.Hom.deformationSpaceSection, Category.assoc,
    Scheme.IdealSheafData.deformationSpaceMap,
    ← PullbackData.comparison_comp_relativeGluingMap
      (HG := s.ker.coequifibered_toQuotientPolynomialAlgebra) _ _ _ _ _ _ _
      (Scheme.IdealSheafData.reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
        _ _ _ _), ← Category.assoc, hsection, Category.assoc]

private theorem pairMap_compatible {V V' S S' : Scheme.{u}}
    (g : V ⟶ S) (g' : V' ⟶ S') (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (h : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ h = b ≫ s) (over : h ≫ g = g' ≫ b) :
    Compatible g g' s s' h b (pairMap s s' h b w) := by
  let hJ : ∀ ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
    fun {U' U} hU ↦
      (s.ker.ideal_map_appLE_le_ideal_comap h ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s' s h b w).1 ⟨U'.1, U'.2⟩)
  let D := zeroPairData h s.ker s'.ker hJ
  let ν := D.comparison s.ker.coequifibered_toNormalConePresheaf
    s'.ker.coequifibered_toNormalConePresheaf
  have hν : ν ≫ s.ker.normalConeToDeformationSpace =
      s'.ker.normalConeToDeformationSpace ≫ pairMap s s' h b w :=
    zeroPairData_toRees h s.ker s'.ker hJ
  have hπ : ν ≫ Scheme.Hom.normalConeProj g s =
      Scheme.Hom.normalConeProj g' s' ≫ b := by
    change ν ≫ ((relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase ≫ g) = _
    rw [← Category.assoc, PullbackData.comparison_toBase, Category.assoc, over]
    simp only [Scheme.Hom.normalConeProj, Category.assoc]
  refine ⟨Scheme.IdealSheafData.deformationSpaceMap_proj h s.ker s'.ker hJ g g' b over,
    pairMap_section s s' h b w, pairMap_oneFibre g g' s s' h b w,
    ν, (laurentPairData h).comparison _ _, ?_, hν, hπ, ?_,
    laurentPairData_toRees h s.ker s'.ker hJ, ?_, ?_⟩
  · intro U' U hU
    exact ⟨hJ hU, PullbackData.ι_comparison _ _ _ hU⟩
  · have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
    apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
    rw [Category.assoc, hν,
      ← Category.assoc, Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace,
      Category.assoc, pairMap_section,
      ← Category.assoc, AffineSpace.zeroSection_comp_map]
    simp only [Category.assoc,
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]
  · intro U' U hU
    exact ⟨hJ hU, PullbackData.ι_comparison _ _ _ hU⟩
  · intro U' U hU
    exact PullbackData.ι_comparison _ _ _ hU

private theorem epi_fixedRank_isIso {S : Scheme.{u}} {M N : S.Modules}
    (r : ℕ) [M.IsFiniteLocallyFreeOfRank r] [N.IsFiniteLocallyFreeOfRank r]
    (a : M ⟶ N) [Epi a] : IsIso a := by
  classical
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N r
  apply Scheme.Modules.isIso_of_bijective_stalkLinearMap
  intro x
  obtain ⟨_, _⟩ := Scheme.Modules.stalk_isFiniteFree_of_isFiniteLocallyFree M x
  obtain ⟨_, _⟩ := Scheme.Modules.stalk_isFiniteFree_of_isFiniteLocallyFree N x
  let F := RingedSpace.moduleStalkFunctor S.toRingedSpace x
  have : Epi (Abelian.image.ι a) := epi_of_epi_fac (Abelian.image.fac a)
  have : IsIso (Abelian.image.ι a) := isIso_of_mono_of_epi _
  have : Epi (F.map (Abelian.factorThruImage a)) :=
    (RingedSpace.module_stalk_exact S.toRingedSpace a).2.2.2.1 x |>.1
  have hsurj : Function.Surjective (F.map a).hom := by
    apply (ModuleCat.epi_iff_surjective _).mp
    rw [← Abelian.image.fac a, F.map_comp]
    infer_instance
  let e := LinearEquiv.ofFinrankEq (F.obj M) (F.obj N)
    ((Scheme.Modules.finiteLocallyFreeOfRank_stalk_finrank M r x).trans
      (Scheme.Modules.finiteLocallyFreeOfRank_stalk_finrank N r x).symm)
  have hinj := Module.End.injective_of_surjective (S.presheaf.stalk x) (F.obj M)
    (f := e.symm.toLinearMap.comp (F.map a).hom) (e.symm.surjective.comp hsurj)
  exact ⟨fun _ _ h ↦ hinj (congrArg e.symm h), hsurj⟩

private theorem conormalRank {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s]
    (d : ℕ) [(ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d] :
    ((Scheme.Modules.tensorPullback s).obj s.ker.toModules).IsFiniteLocallyFreeOfRank d := by
  obtain ⟨e, _⟩ := (ConormalGradedAlgebra.presentation s).powerIdentification 1
  let q : ConormalGradedAlgebra.piece s 1 ≅
      (Scheme.Modules.tensorPullback s).obj s.ker.toModules :=
    (Scheme.Modules.tensorPullback s).mapIso
      (e ≪≫ eqToIso (by rw [pow_one]))
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso q

private theorem conormalMap_isIso {V V' S S' : Scheme.{u}}
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    (h : V' ⟶ V) (b : S' ⟶ S) (w : s' ≫ h = b ≫ s)
    (centres : IsPullback s' b h s) (d : ℕ)
    [(ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d]
    [(ConormalGradedAlgebra.piece s' 1).IsFiniteLocallyFreeOfRank d] :
    IsIso (conormalMap s s' h b w) := by
  have := conormalRank s d
  have := conormalRank s' d
  let E := (Scheme.Modules.tensorPullback s).obj s.ker.toModules
  let q : Scheme.Modules.tensorPullback b ≅ Scheme.Modules.pullback b :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction b).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction b)
  have : ((Scheme.Modules.tensorPullback b).obj E).IsFiniteLocallyFreeOfRank d :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (q.app E).symm
  have : Epi (conormalMap s s' h b w) :=
    (Scheme.Modules.closedImmersion_conormal_flat_base_change s' s h b w
      centres.isLimit _ rfl).1
  exact epi_fixedRank_isIso d _

/-- Arbitrary base change of a section Rees family, with the augmented pair at zero
and one and the punctured trivialization. Source: sk-thm-dnc, Local construction
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: The upstream covering Rees-pushout theorem and relative-gluing comparison give
the deformation pullback. Coefficientwise Laurent and t-quotient comparisons preserve
augmentation and both fibres. The Cartesian conormal comparison is an epimorphism
between bundles of the same rank d; stalkwise surjective endomorphisms of finite free
modules are injective. Cancelling the zero-fibre square gives the normal-cone pullback.
All chart formulas are the existing comparison's coefficient formulas. -/
theorem base_change {V S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    ∃ (s' : S' ⟶ pullback g b) (_ : IsClosedImmersion s')
      (w : s' ≫ pullback.fst g b = b ≫ s),
      s' = Scheme.Hom.baseChangeSection g s hs b ∧
      IsPullback (pairMap s s' (pullback.fst g b) b w)
        (s'.ker.deformationSpaceProj ≫ pullback.snd g b)
        (s.ker.deformationSpaceProj ≫ g) b ∧
      Compatible g (pullback.snd g b) s s' (pullback.fst g b) b
        (pairMap s s' (pullback.fst g b) b w) ∧
      IsIso (conormalMap s s' (pullback.fst g b) b w) ∧
      ∃ ν : s'.ker.normalCone ⟶ s.ker.normalCone,
        ν ≫ s.ker.normalConeToDeformationSpace =
          s'.ker.normalConeToDeformationSpace ≫ pairMap s s' (pullback.fst g b) b w ∧
        IsPullback ν (Scheme.Hom.normalConeProj (pullback.snd g b) s')
          (Scheme.Hom.normalConeProj g s) b := by
  let s' := Scheme.Hom.baseChangeSection g s hs b
  have : IsClosedImmersion s' := MorphismProperty.of_isPullback
    (Scheme.Hom.isPullback_baseChangeSection g s hs b).flip inferInstance
  let w := Scheme.Hom.baseChangeSection_fst g s hs b
  let D := Scheme.IdealSheafData.extendedReesPullbackData (pullback.fst g b)
    s.ker s'.ker (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection g s hs b)
  have hcov : ∀ x : (pullback g b : Scheme.{u}),
      ∃ (U' : (pullback g b).AffineZariskiSite) (U : V.AffineZariskiSite)
        (hU : U'.1 ≤ pullback.fst g b ⁻¹ᵁ U.1), x ∈ U'.1 ∧
        IsPushout ((pullback.fst g b).appLE U.1 U'.1 hU)
          (s.ker.toReesPresheaf.app (op U)) (s'.ker.toReesPresheaf.app (op U'))
          (D.map hU) := by
    intro x
    obtain ⟨U', U, hU, hx, _, H⟩ :=
      Scheme.Hom.exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d x
    exact ⟨U', U, hU, hx, H⟩
  have hp := (D.isPullback_comparison s.ker.coequifibered_toReesPresheaf
    s'.ker.coequifibered_toReesPresheaf hcov).paste_vert
    (IsPullback.of_hasPullback g b)
  have hq : IsPullback (pairMap s s' (pullback.fst g b) b w)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s')
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) b) :=
    Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
    (pullback.fst g b) s.ker s'.ker
    (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection g s hs b) hcov
    g (pullback.snd g b) b (IsPullback.of_hasPullback g b)
  have hc := pairMap_compatible g (pullback.snd g b) s s'
    (pullback.fst g b) b w pullback.condition
  obtain ⟨ν, _, _, hν, hπ, _⟩ := hc.2.2.2
  have he : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d :=
    (SmoothSectionCentredCoordinates.exists_centred_coordinates d g s hs).2.2.1
  have he' : (ConormalGradedAlgebra.piece s' 1).IsFiniteLocallyFreeOfRank d :=
    (SmoothSectionCentredCoordinates.exists_centred_coordinates d (pullback.snd g b) s'
      (Scheme.Hom.baseChangeSection_snd g s hs b)).2.2.1
  refine ⟨s', inferInstance, w, rfl, hp, hc,
    conormalMap_isIso s s' (pullback.fst g b) b w
      (Scheme.Hom.isPullback_baseChangeSection g s hs b) d, ν, hν, ?_⟩
  have outer := (Scheme.Hom.isPullback_normalConeToDeformationSpace
    (pullback.snd g b) s').paste_horiz hq
  rw [AffineSpace.zeroSection_comp_map, ← hν] at outer
  exact IsPullback.of_right outer hπ
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)

/-- Smooth separated dimension-d geometry and compactifiability of the new structural
maps; these are conclusions, not additional base-change assumptions.
Source: sk-thm-dnc, Local construction
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Reapply the upstream smoothness and compactification theorems to the
base-changed section. The zero-fibre pullback preserves smooth dimension, separatedness
and quasi-compactness. Nagata compactification applies to its normal projection.
No flatness or finite type of b is used. -/
theorem base_change_geometry {V S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (b : S' ⟶ S) :
    ∃ (s' : S' ⟶ pullback g b) (_ : IsClosedImmersion s'),
      s' = Scheme.Hom.baseChangeSection g s hs b ∧
      SmoothOfRelativeDimension d (pullback.snd g b) ∧
      IsSeparated (pullback.snd g b) ∧ LocallyOfFiniteType (pullback.snd g b) ∧
      QuasiCompact (pullback.snd g b) ∧ s' ≫ pullback.snd g b = 𝟙 S' ∧
      SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      IsSeparated (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') ∧
      SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj (pullback.snd g b) s') ∧
      IsSeparated (Scheme.Hom.normalConeProj (pullback.snd g b) s') ∧
      HasCompactification (Scheme.Hom.normalConeProj (pullback.snd g b) s') := by
  let s' := Scheme.Hom.baseChangeSection g s hs b
  have : IsClosedImmersion s' := MorphismProperty.of_isPullback
    (Scheme.Hom.isPullback_baseChangeSection g s hs b).flip inferInstance
  have hs' : s' ≫ pullback.snd g b = 𝟙 S' :=
    Scheme.Hom.baseChangeSection_snd g s hs b
  have hq : SmoothOfRelativeDimension d
      (Scheme.Hom.deformationSpaceProj (pullback.snd g b) s') :=
    Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d _ _ hs'
  have sq := Scheme.Hom.isPullback_normalConeToDeformationSpace (pullback.snd g b) s'
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have hn : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.snd g b) s') :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq hq
  have : IsSeparated (Scheme.Hom.normalConeProj (pullback.snd g b) s') :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact (Scheme.Hom.normalConeProj (pullback.snd g b) s') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have := SmoothOfRelativeDimension.smooth d
    (Scheme.Hom.normalConeProj (pullback.snd g b) s')
  exact ⟨s', inferInstance, rfl, inferInstance, inferInstance, inferInstance,
    inferInstance, hs', hq, inferInstance,
    Scheme.Hom.hasCompactification_deformationSpaceProj (d := d) _ _ hs', hn, inferInstance,
    (NagataCompactification (Scheme.Hom.normalConeProj (pullback.snd g b) s')).hasCompactification⟩

/-- Etale maps of pairs with Cartesian centres give the canonical pullback of the Rees
space, preserve augmentation and both fibres, and induce the linear normal-bundle
isomorphism. Source: sk-thm-dnc, Local construction, etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Cartesian centres identify the new kernel ideal with the pulled-back ideal.
Etaleness makes every affine coefficient map flat; the upstream flat Rees pushout gives
the deformation pullback and hence its etaleness. Generic coefficientwise compatibility
gives the augmentation, zero and one formulas. Flat Cartesian conormal base change gives
the conormal isomorphism. Quotienting the chart pushouts by t gives a normal-cone
pullback over the ambient schemes; cancelling the Cartesian centre square makes the
normal comparison a pullback of the identity of S, hence an isomorphism. -/
theorem etale {V V₁ S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (h : V₁ ⟶ V) [Etale h] [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h] (s₁ : S ⟶ V₁) [IsClosedImmersion s₁]
    (hs₁ : s₁ ≫ (h ≫ g) = 𝟙 S) (w : s₁ ≫ h = (𝟙 S) ≫ s)
    (centres : IsPullback s₁ (𝟙 S) h s) :
    IsPullback (pairMap s s₁ h (𝟙 S) w) s₁.ker.deformationSpaceProj
      s.ker.deformationSpaceProj h ∧
    Etale (pairMap s s₁ h (𝟙 S) w) ∧
    Compatible g (h ≫ g) s s₁ h (𝟙 S) (pairMap s s₁ h (𝟙 S) w) ∧
    IsIso (conormalMap s s₁ h (𝟙 S) w) ∧
    ∃ ν : s₁.ker.normalCone ⟶ s.ker.normalCone,
      ν ≫ s.ker.normalConeToDeformationSpace =
        s₁.ker.normalConeToDeformationSpace ≫ pairMap s s₁ h (𝟙 S) w ∧ IsIso ν := by
  let hJ : ∀ ⦃U' : V₁.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ s₁.ker.siteIdeal U' :=
    fun {U' U} hU ↦
      (s.ker.ideal_map_appLE_le_ideal_comap h ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s₁ s h (𝟙 S) w).1 ⟨U'.1, U'.2⟩)
  let D := Scheme.IdealSheafData.extendedReesPullbackData h s.ker s₁.ker hJ
  have hideal : s₁.ker = s.ker.comap h := by
    rw [← centres.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hcov : ∀ x : V₁, ∃ (U' : V₁.AffineZariskiSite) (U : V.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1), x ∈ U'.1 ∧
      IsPushout (h.appLE U.1 U'.1 hU) (s.ker.toReesPresheaf.app (op U))
        (s₁.ker.toReesPresheaf.app (op U')) (D.map hU) := by
    intro x
    obtain ⟨q, hx⟩ := Pairs.exists_mem h x
    refine ⟨q.1.1, q.1.2, q.2, hx, ?_⟩
    have e : (s.ker.siteIdeal q.1.2).map (h.appLE _ _ q.2).hom =
        s₁.ker.siteIdeal q.1.1 := by
      rw [hideal]
      exact (Scheme.IdealSheafData.ideal_comap_appLE s.ker h
        ⟨q.1.2.1, q.1.2.2⟩ ⟨q.1.1.1, q.1.1.2⟩ q.2).symm
    exact rees_flat_pushout _ _ _ (h.flat_appLE q.1.2.2 q.1.1.2 q.2) e
  have hp : IsPullback (pairMap s s₁ h (𝟙 S) w) s₁.ker.deformationSpaceProj
      s.ker.deformationSpaceProj h :=
    D.isPullback_comparison s.ker.coequifibered_toReesPresheaf
      s₁.ker.coequifibered_toReesPresheaf hcov
  have hc := pairMap_compatible g (h ≫ g) s s₁ h (𝟙 S) w (by simp)
  obtain ⟨ν, _, _, hν, hπ, _⟩ := hc.2.2.2
  have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
  have hνeq : ν = (zeroPairData h s.ker s₁.ker hJ).comparison _ _ := by
    apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
    exact hν.trans (zeroPairData_toRees h s.ker s₁.ker hJ).symm
  have hn := zeroPairData_isPullback h s.ker s₁.ker hJ hcov
  rw [← hνeq] at hn
  have hb : Scheme.Hom.normalConeProj g s ≫ s =
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase := by
    rw [← Scheme.Hom.purityNormalProjection_eq s g hs]
    exact IsClosedImmersion.lift_fac _ _ _
  have hb₁ : Scheme.Hom.normalConeProj (h ≫ g) s₁ ≫ s₁ =
      (relativeGluingData s₁.ker.coequifibered_toNormalConePresheaf).toBase := by
    rw [← Scheme.Hom.purityNormalProjection_eq s₁ (h ≫ g) hs₁]
    exact IsClosedImmersion.lift_fac _ _ _
  rw [← hb, ← hb₁] at hn
  have hnormal := IsPullback.of_bot hn hπ centres.flip
  refine ⟨hp, MorphismProperty.of_isPullback (P := @Etale) hp.flip inferInstance, hc,
    (Scheme.Modules.closedImmersion_conormal_flat_base_change s₁ s h (𝟙 S) w
      centres.isLimit _ rfl).2 inferInstance, ν, hν, ?_⟩
  exact hnormal.isIso_fst_of_isIso

/-- The affine algebra identification, encoded by pushout squares of the specified
coefficient maps. The last two pushouts are the presentations B tensor_P R[t,u]
and B' tensor_P' R'[t,u], using mvPolynomialExtendedReesAlgebraEquiv. The first
pushout is B[t,I/t] tensor_R R' = B'[t,I'/t].
Source: sk-thm-dnc, Local construction, x_j=t*u_j
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: The polynomial coefficient square is a pushout. Cancelling it from hB gives
the coordinate-map pushout, so the new coordinate map is etale and therefore flat.
Apply the upstream flat extended-Rees pushout theorem to both coordinate maps. The
upstream compatible-polynomial-origin Rees pushout, pasted with hB, gives the first
square. No flatness of the coefficient extension is required. -/
theorem affine_base_change (R R' B B' : Type u)
    [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [IsNoetherianRing R] [IsNoetherianRing R'] (d : ℕ)
    (κ : R →+* R') (ψ : MvPolynomial (Fin d) R →+* B)
    (ψ' : MvPolynomial (Fin d) R' →+* B') (a : B →+* B')
    (σ : B →+* R) (hσ : σ.comp (ψ.comp MvPolynomial.C) = RingHom.id R)
    (hI : (Ideal.mvPolynomialOrigin R (Fin d)).map ψ = RingHom.ker σ)
    (he : ψ.Etale) (w : a.comp ψ = ψ'.comp (MvPolynomial.map κ))
    (hB : IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (ψ.comp MvPolynomial.C))
      (CommRingCat.ofHom (ψ'.comp MvPolynomial.C)) (CommRingCat.ofHom a)) :
    IsPushout (CommRingCat.ofHom κ)
      (CommRingCat.ofHom ((algebraMap B
        ((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebra).comp
          (ψ.comp MvPolynomial.C)))
      (CommRingCat.ofHom ((algebraMap B'
        ((Ideal.mvPolynomialOrigin R' (Fin d)).map ψ').extendedReesAlgebra).comp
          (ψ'.comp MvPolynomial.C)))
      (CommRingCat.ofHom (((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebraMap
        a _ (Ideal.map_map_mvPolynomialOrigin κ ψ ψ' a w).le)) ∧
    IsPushout (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) R)
        (Ideal.mvPolynomialOrigin R (Fin d)).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B
        ((Ideal.mvPolynomialOrigin R (Fin d)).map ψ).extendedReesAlgebra))
      (CommRingCat.ofHom ((Ideal.mvPolynomialOrigin R (Fin d)).extendedReesAlgebraMap
        ψ _ le_rfl)) ∧
    IsPushout (CommRingCat.ofHom ψ')
      (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) R')
        (Ideal.mvPolynomialOrigin R' (Fin d)).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B'
        ((Ideal.mvPolynomialOrigin R' (Fin d)).map ψ').extendedReesAlgebra))
      (CommRingCat.ofHom ((Ideal.mvPolynomialOrigin R' (Fin d)).extendedReesAlgebraMap
        ψ' _ le_rfl)) := by
  have _ := hσ
  have _ := hI
  have hP : IsPushout (CommRingCat.ofHom κ)
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))
      (CommRingCat.ofHom (MvPolynomial.C : R' →+* MvPolynomial (Fin d) R'))
      (CommRingCat.ofHom (MvPolynomial.map κ)) := by
    let := κ.toAlgebra
    let := MvPolynomial.algebraMvPolynomial (σ := Fin d) (R := R) (S := R')
    exact CommRingCat.isPushout_of_isPushout R R'
      (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')
  have hψ : IsPushout (CommRingCat.ofHom (MvPolynomial.map κ))
      (CommRingCat.ofHom ψ) (CommRingCat.ofHom ψ') (CommRingCat.ofHom a) :=
    IsPushout.of_top hB (by ext1; exact w.symm) hP
  have he' : ψ'.Etale :=
    RingHom.Etale.isStableUnderBaseChange.of_isPushout RingHom.Etale.respectsIso hψ.flip he
  have hf := (RingHom.Etale.iff_flat_and_formallyUnramified.mp he).1
  have hf' := (RingHom.Etale.iff_flat_and_formallyUnramified.mp he').1
  exact ⟨hB.paste_vert
      (Ideal.isPushout_extendedReesAlgebraMap_map_mvPolynomialOrigin κ ψ ψ' a hf hf' w),
    Ideal.isPushout_extendedReesAlgebraMap_of_flat ψ hf _,
    Ideal.isPushout_extendedReesAlgebraMap_of_flat ψ' hf' _⟩

/-- On an affine etale restriction the tensor-product algebra map is the specified
coefficientwise extended-Rees map. Source: sk-thm-dnc, etale maps of pairs
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Etaleness implies flatness. Apply the upstream flat extended-Rees pushout
theorem to the specified coefficientwise comparison. -/
theorem affine_etale (B B₁ : Type u) [CommRing B] [CommRing B₁]
    (I : Ideal B) (a : B →+* B₁) (ha : a.Etale) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom (algebraMap B I.extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap B₁ (I.map a).extendedReesAlgebra))
      (CommRingCat.ofHom (I.extendedReesAlgebraMap a (I.map a) le_rfl)) := by
  exact Ideal.isPushout_extendedReesAlgebraMap_of_flat a
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp ha).1 I

/-- Identification of the same normal cone with the symmetric-algebra bundle, including
its normalized representative map and its zero section. This makes explicit the bundle
used in both functoriality assertions: their zero-fibre comparison on every chart sends
[a/t] to [h-sharp(a)/t], hence is the linear map of these bundles induced by conormalMap.
Source: sk-thm-dnc, Local construction; Stacks 0632--0633
(blueprint: lem-trf-section-rees-base-change-etale).
Proof: Centred coordinates give the conormal rank and invertibility of the canonical
symmetric comparison. Take the existing normalized Rees-cone comparison and the
isomorphism induced by the symmetric-algebra anti-equivalence. Their composite is the
coneToBundle map specified by section geometry, which supplies its projection and
zero-section identities. -/
theorem normal_bundle {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    ∃ (_ : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d)
      (_ : IsIso (ConormalGradedAlgebra.symmetricComparison s))
      (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (e : PurityNormalBundle.normalCone s ≅
        VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1)),
      Etale.FiniteSmoothPurity.ReesConeNormalized s q ∧
      e = (Over.forget S).mapIso
        ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
          (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
            (ObjectProperty.isoMk _
              (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop)) ∧
      (q ≪≫ e).hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
        Scheme.Hom.normalConeProj g s ∧
      s.normalConeZeroSection ≫ (q ≪≫ e).hom =
        VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
  obtain ⟨_, _, hE, hSym⟩ :=
    SmoothSectionCentredCoordinates.exists_centred_coordinates d g s hs
  let := hE
  let := hSym
  let q := Etale.FiniteSmoothPurity.reesConeComparison s
  let e : PurityNormalBundle.normalCone s ≅
      VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1) :=
    (Over.forget S).mapIso
      ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
        (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
          (ObjectProperty.isoMk _
            (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop))
  obtain ⟨_, e', he', hπ, hz, _⟩ := SectionReesNoetherianGeometry.geometry d g s hs
  have he : (q ≪≫ e).hom = e'.hom := by
    rw [he']
    rfl
  exact ⟨hE, hSym, q, e, Etale.FiniteSmoothPurity.reesConeComparison_spec s, rfl,
    he ▸ hπ, he ▸ hz⟩

end AlgebraicGeometry.SectionReesBaseChange
