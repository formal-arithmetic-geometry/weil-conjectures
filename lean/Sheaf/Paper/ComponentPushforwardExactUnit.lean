/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.GenericComponentData
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.Paper.ComponentRelativeProfiniteSite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ComponentModuleUnitStonean
import all Mathlib.AlgebraicGeometry.Spec
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Comma.Over.Basic
import all Mathlib.Topology.Category.Stonean.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Abelian.Exact
import all Sheaf.CategoryTheory.InternalRingSheafPresentation
import all Sheaf.AlgebraicGeometry.GenericComponentSiteComparison
import Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ULift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.Topology.WLocalComponents
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact component direct image and its ordinary unit

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), proof; Bhatt--Scholze,
Lemmas 2.2.8, 2.4.8 and 4.2.13(1)
(blueprint: lem-sfb-component-pushforward-exact-unit).

All functors below are ordinary functors on module sheaves. The slice coefficient is
restriction of the given condensed ring; the scheme coefficient is its actual point
inverse image. Module direct image is Mathlib's restriction with the ring-unit action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.ProEt

/-- The section-ring presentation of the restricted arbitrary condensed coefficient.
Source: HRS Section 3 and (4.1)
(blueprint: lem-sfb-component-pushforward-exact-unit). -/
abbrev componentUnitSliceRing (W : Scheme.{u}) [IsAffine W]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1} :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (coherentTopology Profinite.{u}) Λ.X).over (componentProfinite W))

/-- The section-ring presentation of the actual coefficient p_W^*Λ.
Source: HRS Section 3 and Proposition 4.3(1)
(blueprint: lem-sfb-component-pushforward-exact-unit). -/
abbrev componentUnitSchemeRing (W : Scheme.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    Sheaf (topology W) RingCat.{u + 1} :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (topology W)
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ.X W))

/-- The ring map defining module direct image is the adjunct of the coefficient iso.
It is the ordinary ring-sheaf unit followed by direct image of that iso.
Source: HRS (4.1), Stacks Tags 03D3 and 03D7
(blueprint: lem-sfb-component-pushforward-exact-unit). -/
def componentUnitRingMap (W : Scheme.{u}) [IsAffine W]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (L : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1}
      ⥤ Sheaf (topology W) RingCat.{u + 1})
    (adj : L ⊣ genericComponentRingPush W)
    (c : L.obj (componentUnitSliceRing W Λ) ≅ componentUnitSchemeRing W Λ) :
    componentUnitSliceRing W Λ ⟶
      (genericComponentRingPush W).obj (componentUnitSchemeRing W Λ) :=
  adj.unit.app (componentUnitSliceRing W Λ) ≫ (genericComponentRingPush W).map c.hom

/-- Evaluation of direct image is actual evaluation at W_E with the coefficient-unit
scalar action. This natural isomorphism is the identity on every section and morphism.
Source: HRS Proposition 4.3(1), Stacks Tag 03D7
(blueprint: lem-sfb-component-pushforward-exact-unit). -/
def componentUnitDirectEvaluation (W : Scheme.{u}) [IsAffine W]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (L : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1}
      ⥤ Sheaf (topology W) RingCat.{u + 1})
    (adj : L ⊣ genericComponentRingPush W)
    (c : L.obj (componentUnitSliceRing W Λ) ≅ componentUnitSchemeRing W Λ)
    (E : Over (componentProfinite W)) :
    SheafOfModules.pushforward.{u + 1} (componentUnitRingMap W Λ L adj c) ⋙
        SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E) ≅
      SheafOfModules.evaluation (componentUnitSchemeRing W Λ)
          (op ((genericComponentFunctor W).obj E)) ⋙
        ModuleCat.restrictScalars.{u + 1}
          ((componentUnitRingMap W Λ L adj c).hom.app (op E)).hom :=
  Iso.refl _

private theorem componentUnitRecoveredRing {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Mon (Sheaf J Ab.{u + 1})) [IsCommMonObj R.X] :
    Nonempty (Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R.X))) ≅ R) := by
  open InternalAbelianSheafModule in
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R.X)
  let E := Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}
  let M := (sheafToPresheaf J Ab.{u + 1}).mapMon.obj R
  let k : A.obj.toMonAb ≅ M :=
    E.inverse.mapIso (Functor.isoWhiskerLeft (E.functor.obj M) recoveredMonNatIso) ≪≫
      E.unitIso.symm.app M
  let z := (presheafToSheaf J Ab.{u + 1}).mapMon.mapIso k
  let h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_counitAlgHom R.X
  let a : (presheafToSheaf J Ab.{u + 1}).mapMon.obj A.obj.toMonAb ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj A) :=
    Mon.mkIso (Sheaf.sheafifyRingPresheafIso J A)
      (Sheaf.isMonHom_sheafifyRingPresheafIso_hom J A).one_hom
      (Sheaf.isMonHom_sheafifyRingPresheafIso_hom J A).mul_hom
  let b : (presheafToSheaf J Ab.{u + 1}).mapMon.obj M ≅ R :=
    Mon.mkIso (asIso ((sheafificationAdjunction J Ab.{u + 1}).counit.app R.X))
      h.one_hom h.mul_hom
  exact ⟨a.symm ≪≫ z ≪≫ b⟩

private theorem componentUnitCoefficient (W : Scheme.{u}) [IsAffine W]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    ∃ (L : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1}
        ⥤ Sheaf (topology W) RingCat.{u + 1})
      (_adj : L ⊣ genericComponentRingPush W),
      Nonempty (L.obj (componentUnitSliceRing W Λ) ≅ componentUnitSchemeRing W Λ) := by
  let Ω := AlgebraicClosure (ULift.{u} ℚ)
  let V : Scheme.{u} := Spec (CommRingCat.of Ω)
  have : IsAffine (ProEt.mk (𝟙 V)).left := by
    change IsAffine V
    dsimp [V]
    infer_instance
  have : (genericComponentProjection V).inverse.IsEquivalence :=
    field_generic_equivalence Ω (ProEt.mk (𝟙 V))
  have : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  have : EssentiallySmall.{u + 1} V.ProEt := essentiallySmallSelf.{0} _
  let hW := SheafOfModules.coefficientSheafification.{u + 1, u, u + 1} (topology W)
  let hV := SheafOfModules.coefficientSheafification.{u + 1, u, u + 1} (topology V)
  let := hW.1
  let := hV.1
  have : IsCommMonObj (AlgebraicGeometry.ProEtale.coefficientRing W Λ).X := by
    change IsCommMonObj (AlgebraicGeometry.ProEtale.condensedRingObj Λ.X W)
    infer_instance
  have : IsCommMonObj (AlgebraicGeometry.ProEtale.coefficientRing V Λ).X := by
    change IsCommMonObj (AlgebraicGeometry.ProEtale.condensedRingObj Λ.X V)
    infer_instance
  let A := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) Λ.X)
  obtain ⟨d⟩ := generic_component_coefficient_comparison W V Λ A
    (componentUnitSchemeRing W Λ) (componentUnitSchemeRing V Λ)
    (componentUnitRecoveredRing _ Λ)
    (componentUnitRecoveredRing _ (AlgebraicGeometry.ProEtale.coefficientRing W Λ))
    (componentUnitRecoveredRing _ (AlgebraicGeometry.ProEtale.coefficientRing V Λ))
  exact ⟨d.LU, d.adjU, ⟨d.iU⟩⟩

private theorem componentUnitStoneanCover {S : Profinite.{u}} (T : Over S)
    (R : Sieve T)
    (hR : ∀ (E : Over S) [ExtremallyDisconnected E.left] (f : E ⟶ T), R f) :
    R ∈ ((coherentTopology Profinite.{u}).over S) T := by
  rw [GrothendieckTopology.mem_over_iff]
  apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  let P := Stonean.toProfinite.obj T.left.presentation
  let p : P ⟶ T.left := Profinite.presentation.π T.left
  refine ⟨PUnit, inferInstance, fun _ ↦ P, fun _ ↦ p, ?_, ?_⟩
  · apply ((Profinite.effectiveEpiFamily_tfae _ _).out 0 2).mpr
    intro x
    obtain ⟨y, hy⟩ := (Profinite.epi_iff_surjective p).mp inferInstance x
    exact ⟨PUnit.unit, y, hy⟩
  · intro _
    rw [Sieve.overEquiv_iff]
    let Q : Over S := Over.mk (p ≫ T.hom)
    have : ExtremallyDisconnected Q.left := by
      change ExtremallyDisconnected T.left.presentation
      infer_instance
    exact hR Q (Over.homMk p)

private theorem componentUnitAbSurjective {S : Profinite.{u}}
    {F G : Sheaf ((coherentTopology Profinite.{u}).over S) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G)
    (ha : ∀ (E : Over S) [ExtremallyDisconnected E.left],
      Function.Surjective (a.hom.app (op E))) : Sheaf.IsLocallySurjective a := by
  constructor
  intro T x
  apply componentUnitStoneanCover T
  intro E hE f
  exact ha E (G.obj.map f.op x)

private theorem componentUnitAbInjective {S : Profinite.{u}}
    {F G : Sheaf ((coherentTopology Profinite.{u}).over S) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G)
    (ha : ∀ (E : Over S) [ExtremallyDisconnected E.left],
      Function.Injective (a.hom.app (op E))) : Sheaf.IsLocallyInjective a := by
  constructor
  intro T x y hxy
  apply componentUnitStoneanCover T.unop
  intro E hE f
  apply ha E
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

private theorem componentUnitAbIso {S : Profinite.{u}}
    {F G : Sheaf ((coherentTopology Profinite.{u}).over S) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G)
    (ha : ∀ (E : Over S) [ExtremallyDisconnected E.left],
      Function.Bijective (a.hom.app (op E))) : IsIso a := by
  exact (Sheaf.isLocallyBijective_iff_isIso a).mp
    ⟨componentUnitAbInjective a (fun E _ ↦ (ha E).1),
      componentUnitAbSurjective a (fun E _ ↦ (ha E).2)⟩

private theorem componentUnitStrictStalk (W : Scheme.{u}) [IsAffine W]
    [IsWStrictlyLocalRing Γ(W, ⊤)] (x : W) (hx : IsClosed ({x} : Set W)) :
    IsStrictlyHenselianLocalRing (W.presheaf.stalk x) := by
  let y : PrimeSpectrum Γ(W, ⊤) := W.isoSpec.hom x
  have hy : IsClosed ({y} : Set (PrimeSpectrum Γ(W, ⊤))) := by
    simpa only [Set.image_singleton, Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso W.isoSpec).isClosedMap _ hx
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
    (R := Γ(W, ⊤)) y.asIdeal
  let e : CommRingCat.of (Localization.AtPrime y.asIdeal) ≅ W.presheaf.stalk x :=
    (Spec.stalkIso (CommRingCat.of Γ(W, ⊤)) y).symm ≪≫ asIso (W.isoSpec.hom.stalkMap x)
  exact IsStrictlyHenselianLocalRing.of_ringEquiv e.commRingCatIsoToRingEquiv

private theorem componentUnitGeometry (W : Scheme.{u}) [IsAffine W]
    [IsWContractibleRing Γ(W, ⊤)] (E : Over (componentProfinite W))
    [ExtremallyDisconnected E.left] :
    IsAffine ((genericComponentFunctor W).obj E).left ∧
      Nonempty (IsWContractibleRing Γ(((genericComponentFunctor W).obj E).left, ⊤)) ∧
      (∀ x : ((genericComponentFunctor W).obj E).left,
        IsIso (((genericComponentFunctor W).obj E).hom.stalkMap x)) ∧
      (∀ x : ((genericComponentFunctor W).obj E).left,
        IsClosed ({x} : Set ((genericComponentFunctor W).obj E).left) ↔
          IsClosed ({((genericComponentFunctor W).obj E).hom x} : Set W)) ∧
      ∃ e : ConnectedComponents ((genericComponentFunctor W).obj E).left ≃ₜ E.left,
        ∀ x : ((genericComponentFunctor W).obj E).left,
          e (ConnectedComponents.mk x) = genericComponentCoordinates W E x := by
  classical
  have hg := (affine_component_site_projection W).choose_spec.choose_spec.1 E
  change IsAffine ((genericComponentFunctor W).obj E).left ∧ _ at hg
  obtain ⟨haff, hind, hstalk, ⟨h, hf, hp⟩, ⟨e, he⟩⟩ := hg
  let V := ((genericComponentFunctor W).obj E).left
  let f : V ⟶ W := ((genericComponentFunctor W).obj E).hom
  have : IsAffine V := haff
  have : WLocalSpace (Spec Γ(W, ⊤)) :=
    inferInstanceAs (WLocalSpace (PrimeSpectrum Γ(W, ⊤)))
  have : WLocalSpace W := (Scheme.homeoOfIso W.isoSpec).isClosedEmbedding.wLocalSpace
  have : WLocalSpace (W × E.left) :=
    (Homeomorph.prodComm W E.left).isClosedEmbedding.wLocalSpace
  have hc : IsClosed {z : W × E.left | ConnectedComponents.mk z.1 = E.hom z.2} :=
    isClosed_eq (ConnectedComponents.continuous_coe.comp continuous_fst)
      (E.hom.hom.hom.continuous.comp continuous_snd)
  have : WLocalSpace {z : W × E.left | ConnectedComponents.mk z.1 = E.hom z.2} :=
    hc.isClosedEmbedding_subtypeVal.wLocalSpace
  have : WLocalSpace V := h.isClosedEmbedding.wLocalSpace
  have hclosed (x : V) : IsClosed ({x} : Set V) ↔ IsClosed ({f x} : Set W) := by
    have h₁ := h.isEmbedding.closedPoints_eq_preimage
      (h.surjective.range_eq ▸ fun _ _ _ _ ↦ Set.mem_univ _)
    have h₂ := hc.isClosedEmbedding_subtypeVal.isEmbedding.closedPoints_eq_preimage
      (Subtype.range_val ▸ hc.stableUnderSpecialization)
    have h₃ := (Homeomorph.prodComm W E.left).isEmbedding.closedPoints_eq_preimage
      ((Homeomorph.prodComm W E.left).surjective.range_eq ▸
        fun _ _ _ _ ↦ Set.mem_univ _)
    change x ∈ closedPoints ((genericComponentFunctor W).obj E).left ↔
      f x ∈ closedPoints W
    change closedPoints ((genericComponentFunctor W).obj E).left = _ at h₁
    erw [h₁, h₂, h₃, closedPoints_prod]
    change IsClosed ({(h x).val.1} : Set W) ↔ IsClosed ({f x} : Set W)
    rw [hf]
    rfl
  have : IsWLocalRing Γ(V, ⊤) :=
    ⟨(Scheme.homeoOfIso V.isoSpec).symm.isClosedEmbedding.wLocalSpace⟩
  have hstrict : IsWStrictlyLocalRing Γ(V, ⊤) := by
    refine ⟨fun m hm ↦ ?_⟩
    let y : PrimeSpectrum Γ(V, ⊤) := ⟨m, hm.isPrime⟩
    let x : V := V.isoSpec.inv y
    have hy : IsClosed ({y} : Set (PrimeSpectrum Γ(V, ⊤))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
    have hx : IsClosed ({x} : Set V) := by
      simpa only [Set.image_singleton, Scheme.homeoOfIso_symm, Scheme.coe_homeoOfIso_symm] using
        (Scheme.homeoOfIso V.isoSpec).symm.isClosedMap _ hy
    have : IsStrictlyHenselianLocalRing (W.presheaf.stalk (f x)) :=
      componentUnitStrictStalk W (f x) ((hclosed x).mp hx)
    have : IsIso (f.stalkMap x) := hstalk x
    let a : W.presheaf.stalk (f x) ≅ CommRingCat.of (Localization.AtPrime m) :=
      asIso (f.stalkMap x) ≪≫ asIso (V.isoSpec.inv.stalkMap y) ≪≫
        Spec.stalkIso (CommRingCat.of Γ(V, ⊤)) y
    exact IsStrictlyHenselianLocalRing.of_ringEquiv a.commRingCatIsoToRingEquiv
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum Γ(V, ⊤))) := by
    let q := (Scheme.homeoOfIso V.isoSpec).symm
    let qcc : ConnectedComponents (PrimeSpectrum Γ(V, ⊤)) ≃ₜ ConnectedComponents V :=
      q.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
        (fun y ↦ by
          have hq : q ⁻¹' {y} = {q.symm y} := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact q.toEquiv.eq_symm_apply.symm
          rw [hq]
          exact isConnected_singleton)
    exact extremallyDisconnected_of_homeo (qcc.trans e).symm
  exact ⟨haff, ⟨{ extremallyDisconnected_connectedComponents := inferInstance }⟩,
    hstalk, hclosed, e, he⟩

private theorem componentUnitExact (W : Scheme.{u}) [IsAffine W]
    [IsWContractibleRing Γ(W, ⊤)]
    (A : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1})
    (B : Sheaf (topology W) RingCat.{u + 1})
    (a : A ⟶ (genericComponentRingPush W).obj B) :
    (SheafOfModules.pushforward.{u + 1} a).Additive ∧
    PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1} a) ∧
    PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} a) := by
  have : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : HasSheafify (topology W) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} (topology W) _
  have : (topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1, u + 1, u + 1} (topology W)
  let G := SheafOfModules.pushforward.{u + 1} a
  have : G.Additive := ⟨by intros; rfl⟩
  have : G.IsRightAdjoint :=
    SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0} a
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} B) :=
    (moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} B).2.2.1
  have : G.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf A).map (G.map f)
    have hg : Sheaf.IsLocallySurjective g := by
      apply componentUnitAbSurjective
      intro E hE
      have hgeom := componentUnitGeometry W E
      have : IsAffine ((genericComponentFunctor W).obj E).left := hgeom.1
      have : IsWContractibleRing Γ(((genericComponentFunctor W).obj E).left, ⊤) :=
        hgeom.2.1.some
      have hweak : (topology W).IsWeaklyContractible.{u + 1}
          ((genericComponentFunctor W).obj E) :=
        isWeaklyContractible_of_iso.{u + 1, u} ((genericComponentFunctor W).obj E).left.isoSpec
      let fAb := (SheafOfModules.toSheaf B).map f
      have : Epi fAb := inferInstance
      have : Sheaf.IsLocallySurjective fAb :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} fAb).mpr inferInstance
      let fs := (sheafCompose (topology W) (CategoryTheory.forget AddCommGrpCat.{u + 1})).map fAb
      exact hweak fs inferInstance
    have : Epi g := Sheaf.epi_of_isLocallySurjective g
    exact Functor.epi_of_epi_map (SheafOfModules.toSheaf A) inferInstance
  have : G.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels G
  exact ⟨inferInstance, inferInstance,
    Functor.preservesFiniteColimits_of_preservesHomology G⟩

/-- The component direct image is exact, and its actual module-adjunction unit is
invertible and evaluates to the identity on every extremally disconnected test.
The natural isomorphisms are linear over the source section ring; the direct-image
formula includes scalar restriction along the displayed coefficient unit.

Source: HRS Proposition 4.3(1), proof; BS Lemmas 2.2.8, 2.4.8 and 4.2.13(1)
(blueprint: lem-sfb-component-pushforward-exact-unit).

Proof:
1. Present the condensed coefficient and its actual point inverse images as section
   rings. Ring reconstruction supplies the canonical internal-ring isomorphisms.
   Apply generic component coefficient comparison, using an algebraically closed
   field as its second affine scheme, to obtain L, its adjunction and c.
2. The affine component-site theorem gives the fibre-space homeomorphism, stalk
   isomorphisms and component quotient E. Transport w-locality through the closed
   pullback subspace. Closed points are exactly pairs with closed first coordinate.
   At these points the local rings are strictly henselian. The component quotient
   is extremally disconnected, so the test scheme is w-contractible.
3. Module pushforward is additive sectionwise and preserves limits as a right
   adjoint. A module epimorphism is locally surjective after forgetting. The proved
   weak-contractibility theorem makes its evaluation on every W_E surjective.
   Stonean presentations cover all profinite tests, so its pushforward is locally
   surjective and therefore epi. Preservation of kernels and epis gives homology
   preservation, and hence preservation of finite colimits.
4. The separate local-unit theorem component_module_unit_bijective_on_stonean_tests
   is the split-cover and Kan-extension unit calculation of HRS Proposition 4.3(1),
   including its scalar-action normalization. Apply it to the specified L, adj and c.
5. Stonean presentations give covering sieves on every slice object. The local-unit
   bijections imply local injectivity and local surjectivity of the underlying
   abelian sheaf unit. Hence it is an isomorphism; module forgetting reflects this.
6. Whisker the inverse unit natural isomorphism with evaluation, using associators
   and the left unitor. The inverse law gives the stated unit formula. Naturality
   of its inverse as a module-sheaf morphism gives the restriction formula.
7. No argument imposes nonemptiness, finite generation or discrete coefficients.
   Stonean covers, the empty-cover condition and the source weak-contractibility
   theorem include the empty scheme and empty test. All functors are ordinary
   module-sheaf functors in the stipulated universes. -/
theorem component_pushforward_exact_unit
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    (∀ (E : Over (componentProfinite W)) [ExtremallyDisconnected E.left],
      IsAffine ((genericComponentFunctor W).obj E).left ∧
      Nonempty (IsWContractibleRing Γ(((genericComponentFunctor W).obj E).left, ⊤)) ∧
      (∀ x : ((genericComponentFunctor W).obj E).left,
        IsIso (((genericComponentFunctor W).obj E).hom.stalkMap x)) ∧
      (∀ x : ((genericComponentFunctor W).obj E).left,
        IsClosed ({x} : Set ((genericComponentFunctor W).obj E).left) ↔
          IsClosed ({((genericComponentFunctor W).obj E).hom x} : Set W)) ∧
      ∃ e : ConnectedComponents ((genericComponentFunctor W).obj E).left ≃ₜ E.left,
        ∀ x : ((genericComponentFunctor W).obj E).left,
          e (ConnectedComponents.mk x) = genericComponentCoordinates W E x) ∧
    ∃ (L : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite W)) RingCat.{u + 1}
        ⥤ Sheaf (topology W) RingCat.{u + 1})
      (adj : L ⊣ genericComponentRingPush W)
      (c : L.obj (componentUnitSliceRing W Λ) ≅ componentUnitSchemeRing W Λ)
      (_ : (SheafOfModules.pushforward.{u + 1} (componentUnitRingMap W Λ L adj c)).IsRightAdjoint),
      (SheafOfModules.pushforward.{u + 1} (componentUnitRingMap W Λ L adj c)).Additive ∧
      PreservesFiniteLimits
        (SheafOfModules.pushforward.{u + 1} (componentUnitRingMap W Λ L adj c)) ∧
      PreservesFiniteColimits
        (SheafOfModules.pushforward.{u + 1} (componentUnitRingMap W Λ L adj c)) ∧
      (∀ M : ringedSiteModules.{u + 1} (componentUnitSliceRing W Λ),
        IsIso ((SheafOfModules.pullbackPushforwardAdjunction
          (componentUnitRingMap W Λ L adj c)).unit.app M)) ∧
      ∃ e : ∀ (E : Over (componentProfinite W)) [ExtremallyDisconnected E.left],
          SheafOfModules.pullback.{u + 1} (componentUnitRingMap W Λ L adj c) ⋙
              SheafOfModules.pushforward (componentUnitRingMap W Λ L adj c) ⋙
              SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E) ≅
            SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E),
        (∀ (E : Over (componentProfinite W)) [ExtremallyDisconnected E.left]
          (M : ringedSiteModules.{u + 1} (componentUnitSliceRing W Λ)),
          (SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E)).map
              ((SheafOfModules.pullbackPushforwardAdjunction
                (componentUnitRingMap W Λ L adj c)).unit.app M) ≫
            (e E).hom.app M = 𝟙 _) ∧
        ∀ (E E' : Over (componentProfinite W))
          [ExtremallyDisconnected E.left] [ExtremallyDisconnected E'.left]
          (f : E ⟶ E') (M : ringedSiteModules.{u + 1} (componentUnitSliceRing W Λ))
          (x : ((SheafOfModules.pushforward (componentUnitRingMap W Λ L adj c)).obj
            ((SheafOfModules.pullback (componentUnitRingMap W Λ L adj c)).obj M)).val.obj
              (op E')),
          (e E).hom.app M
              (((SheafOfModules.pushforward (componentUnitRingMap W Λ L adj c)).obj
                ((SheafOfModules.pullback (componentUnitRingMap W Λ L adj c)).obj M)).val.map
                  f.op x) =
            M.val.map f.op ((e E').hom.app M x) := by
  classical
  obtain ⟨L, adj, ⟨c⟩⟩ := componentUnitCoefficient W Λ
  let a := componentUnitRingMap W Λ L adj c
  have : (SheafOfModules.pushforward.{u + 1} a).IsRightAdjoint :=
    SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0} a
  have hunit (M : ringedSiteModules.{u + 1} (componentUnitSliceRing W Λ)) :
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction a).unit.app M) := by
    have : (SheafOfModules.pushforward.{u + 1}
        (adj.unit.app (componentUnitSliceRing W Λ) ≫
          (genericComponentRingPush W).map c.hom)).IsRightAdjoint :=
      inferInstanceAs (SheafOfModules.pushforward.{u + 1} a).IsRightAdjoint
    have : IsIso ((SheafOfModules.toSheaf (componentUnitSliceRing W Λ)).map
        ((SheafOfModules.pullbackPushforwardAdjunction a).unit.app M)) := by
      apply componentUnitAbIso
      intro E hE
      exact component_module_unit_bijective_on_stonean_tests W
        (componentUnitSliceRing W Λ) (componentUnitSchemeRing W Λ) L adj c E M
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (componentUnitSliceRing W Λ))
  have hex := componentUnitExact W (componentUnitSliceRing W Λ)
    (componentUnitSchemeRing W Λ) a
  refine ⟨fun E ↦ componentUnitGeometry W E, L, adj, c, inferInstance,
    hex.1, hex.2.1, hex.2.2, hunit, ?_⟩
  let η := (SheafOfModules.pullbackPushforwardAdjunction a).unit
  have : ∀ M, IsIso (η.app M) := hunit
  have : IsIso η := NatIso.isIso_of_isIso_app _
  let e (E : Over (componentProfinite W)) :
      SheafOfModules.pullback.{u + 1} a ⋙ SheafOfModules.pushforward a ⋙
          SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E) ≅
        SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso η).symm _ ≪≫ (Functor.leftUnitor _)
  refine ⟨fun E _ ↦ e E, ?_, ?_⟩
  · intro E hE M
    change (SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E)).map
      (η.app M) ≫ (SheafOfModules.evaluation (componentUnitSliceRing W Λ) (op E)).map
        ((asIso η).inv.app M) = _
    rw [← Functor.map_comp]
    simp
  · intro E E' hE hE' f M x
    exact PresheafOfModules.naturality_apply ((asIso η).inv.app M).val f.op x

end AlgebraicGeometry.Scheme.ProEt
