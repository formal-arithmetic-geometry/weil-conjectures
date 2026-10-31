/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.CategoryTheory.SixFunctors.YonedaDerivedExtComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorAddition
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.BinaryTorsorQuotient
import all WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import all WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Tensor addition of framed Cartier pairs

Source: Stacks Project, Tags 01WT, 01WU, 03AJ, 010L, 0117 and 0G78;
blueprint main-20261015, lem-pur-divisor-class, clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition)

The geometric, framed-torsor, relative-class, extension-class and naturality clauses
are recorded separately. Restriction uses the actual shifted cone, and the relative
class is minus the raw lifting class, as required by the Ext normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

local instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities


/-- The existing frame torsor of the dual Cartier ideal, with its canonical invertibility
instances supplied by the recorded divisor-line-bundle theorem.
Source: Stacks 03AJ and blueprint divisor-class clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairFrameTorsor {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible) :
    Sheaf.Torsor T.gmSheaf :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)

/-- The underlying ordinary-pullback frame, using the recorded frame-torsor API.
Source: Stacks 03AJ, frames of O(D).
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairFrameVal {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible)
    {U : T.Etaleᵒᵖ} (x : (cartierPairFrameTorsor i hI).sheaf.obj.obj U) :
    (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.dual i.ker.toModules) :=
  x.down.1

/-- Tensor two pulled-back frames via the canonical monoidal pullback comparisons.
Source: blueprint divisor-class clause (b), map (x,y) to x tensor y.
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairTensorFrames {T : Scheme.{u}} (L M : T.Modules) (U : T.Etale)
    (x : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj L)
    (y : (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj M) :
    (Scheme.Modules.pullback U.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.hom).obj (L ⊗ M) :=
  Scheme.Modules.tensorPullbackFrames L M
    ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U).hom x y

/-- Inclusion of one open in another as an object of the small etale site.
Source: Stacks 0G78, restriction of the open term.
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairOpenInclusion {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V) :
    Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk V.ι :=
  MorphismProperty.Over.homMk (T.homOfLE h) (T.homOfLE_ι h)

/-- The identity on global sections and restriction on open sections form a commuting
square. Source: Stacks 0G78, signed-cone refinement.
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof: restriction from the terminal object factors through V; functoriality of
sections gives the equality degreewise, and extension by zero preserves it. -/
theorem cartierPairRestriction_square {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I)) ≫
        relativeSectionRestriction T (Scheme.Etale.mk W.ι) I =
      relativeSectionRestriction T (Scheme.Etale.mk V.ι) I ≫
        HomologicalComplex.extendMap (etaleSectionMap (cartierPairOpenInclusion h) I)
          ComplexShape.embeddingUpNat := by
  rw [Category.id_comp]
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change (I.X n).obj.map _ = (I.X n).obj.map _ ≫ (I.X n).obj.map _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (MorphismProperty.Over.mkIdTerminal @Etale T).hom_ext _ _

/-- Enlargement of support in the actual signed shifted-cone model. Its coordinates
are (x,y) to (x,y restricted to W), so there is no independently chosen sign.
Source: Stacks 0G78 (blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairRestriction {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionComplex T (Scheme.Etale.mk V.ι) I ⟶
      relativeSectionComplex T (Scheme.Etale.mk W.ι) I :=
  relativeFiberMap (relativeSectionRestriction T (Scheme.Etale.mk V.ι) I)
    (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) (𝟙 _)
    (HomologicalComplex.extendMap (etaleSectionMap (cartierPairOpenInclusion h) I)
      ComplexShape.embeddingUpNat) (cartierPairRestriction_square h I)

set_option backward.isDefEq.respectTransparency false in
private lemma cartierPairRestriction_map {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) :
    cartierPairRestriction h I ≫ relativeSectionMap T (Scheme.Etale.mk W.ι) f =
      relativeSectionMap T (Scheme.Etale.mk V.ι) f ≫ cartierPairRestriction h J := by
  unfold cartierPairRestriction relativeSectionMap relativeFiberMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 1
  congr 1
  apply Arrow.hom_ext
  · change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    rfl
  · change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
      HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro n
    change (I.X n).obj.map _ ≫ (f.f n).hom.app _ =
      (f.f n).hom.app _ ≫ (J.X n).obj.map _
    exact (f.f n).hom.naturality _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ideal_mul_mem {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens)
    (x : Γ(I.toModules, U)) (y : Γ(J.toModules, U)) :
    (show Γ(X, U) from I.toModulesι.app U x) *
        (show Γ(X, U) from J.toModulesι.app U y) ∈
      (I * J).idealOfOpens U := by
  refine (I * J).mem_idealOfOpens_of_forall
    (fun V : {V : X.affineOpens // V.1 ≤ U} ↦ V.1.1) (fun V ↦ V.2)
    (fun z hz ↦ ?_) (fun V ↦ ?_)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz U.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hzV⟩
  · rw [map_mul, Scheme.IdealSheafData.idealOfOpens_eq_ideal,
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    apply Ideal.mul_mem_mul
    · have hx := I.map_mem_idealOfOpens V.2
        ((I.range_toModulesι_app_eq_idealOfOpens U).subset ⟨x, rfl⟩)
      exact I.idealOfOpens_eq_ideal V.1 ▸ hx
    · have hy := J.map_mem_idealOfOpens V.2
        ((J.range_toModulesι_app_eq_idealOfOpens U).subset ⟨y, rfl⟩)
      exact J.idealOfOpens_eq_ideal V.1 ▸ hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ideal_tensor_multiplication {X : Scheme.{u}} (I J : X.IdealSheafData) :
    ∃ μ : I.toModules ⊗ J.toModules ⟶ (I * J).toModules,
      μ ≫ (I * J).toModulesι =
        (I.toModulesι ⊗ₘ J.toModulesι) ≫ (λ_ (Scheme.Modules.unit X)).hom := by
  let d := (I.toModulesι ⊗ₘ J.toModulesι) ≫ (λ_ (Scheme.Modules.unit X)).hom
  have hd (U : X.Opens) (x : Γ(I.toModules, U)) (y : Γ(J.toModules, U)) :
      d.app U (Scheme.Modules.tmulSection x y) =
        (show Γ(X, U) from I.toModulesι.app U x) *
        (show Γ(X, U) from J.toModulesι.app U y) := by
    dsimp only [d]
    change (λ_ (Scheme.Modules.unit X)).hom.app U
      ((I.toModulesι ⊗ₘ J.toModulesι).app U (Scheme.Modules.tmulSection x y)) = _
    rw [Scheme.Modules.tensorHom_app_tmulSection,
      Scheme.Modules.leftUnitor_hom_app_tmulSection']
    rfl
  have hz : d ≫ (I * J).toPushforwardSubscheme = 0 := by
    obtain ⟨φ, hφ, huniq⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf
      I.toModules J.toModules
      ((SheafOfModules.pushforward (I * J).subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit (I * J).subscheme.ringCatSheaf))
      (fun _ ↦ 0) (by intros; simp only [LinearMap.zero_apply, map_zero])
    apply (huniq _ ?_).trans (huniq _ ?_).symm
    · intro U x y
      change (I * J).subschemeι.app U.unop
        (d.app U.unop (Scheme.Modules.tmulSection x y)) = 0
      rw [hd]
      exact (I * J).mem_idealOfOpens_iff.mp (ideal_mul_mem I J U.unop x y)
    · intro U x y
      rfl
  exact ⟨kernel.lift _ d hz, kernel.lift_ι _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ideal_tensor_multiplication_iso {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    ∃ μ : I.toModules ⊗ J.toModules ≅ (I * J).toModules,
      μ.hom ≫ (I * J).toModulesι =
        (I.toModulesι ⊗ₘ J.toModulesι) ≫ (λ_ (Scheme.Modules.unit X)).hom := by
  obtain ⟨μ, hμ⟩ := ideal_tensor_multiplication I J
  have hμapp (U : X.Opens) (s : Γ(I.toModules, U)) (t : Γ(J.toModules, U)) :
      (I * J).toModulesι.app U (μ.app U (Scheme.Modules.tmulSection s t)) =
        (show Γ(X, U) from I.toModulesι.app U s) *
        (show Γ(X, U) from J.toModulesι.app U t) := by
    have he := congrArg (fun f ↦ f.app U (Scheme.Modules.tmulSection s t)) hμ
    change _ = (λ_ (Scheme.Modules.unit X)).hom.app U
      ((I.toModulesι ⊗ₘ J.toModulesι).app U (Scheme.Modules.tmulSection s t)) at he
    rw [Scheme.Modules.tensorHom_app_tmulSection,
      Scheme.Modules.leftUnitor_hom_app_tmulSection'] at he
    exact he
  have hIso : IsIso μ := Scheme.Modules.isIso_of_isFreeGenerator μ fun x ↦ by
    obtain ⟨U, hxU, -, ⟨a, ha, hIa⟩, ⟨b, hb, hJb⟩⟩ :=
      Scheme.IdealSheafData.exists_affineOpens_isRegularPrincipal hI hJ (O := ⊤) trivial
    obtain ⟨s, hs⟩ := I.exists_toModulesι_app_eq (hIa ▸ Ideal.mem_span_singleton_self a)
    obtain ⟨t, ht⟩ := J.exists_toModulesι_app_eq (hJb ▸ Ideal.mem_span_singleton_self b)
    have hsg := hI.isFreeGenerator s fun V h ↦ by
      rw [hs, ← I.map_ideal h, hIa, Ideal.map_span, Set.image_singleton]
      rfl
    have htg := hJ.isFreeGenerator t fun V h ↦ by
      rw [ht, ← J.map_ideal h, hJb, Ideal.map_span, Set.image_singleton]
      rfl
    refine ⟨U.1, Scheme.Modules.tmulSection s t, hxU, hsg.tmulSection htg,
      (hI.mul_effectiveCartier hJ).isFreeGenerator _ fun V h ↦ ?_⟩
    rw [hμapp, hs, ht, ← (I * J).map_ideal h, Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, hIa, hJb, Ideal.span_singleton_mul_span_singleton,
      Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨asIso μ, hμ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2000 in
private lemma dual_tensor_iso {X : Scheme.{u}} (A B C : X.Modules)
    [A.IsInvertible] [B.IsInvertible] [C.IsInvertible] (μ : A ⊗ B ≅ C) :
    ∃ e : Cᵛ ≅ Aᵛ ⊗ Bᵛ,
      (μ.hom ⊗ₘ 𝟙 Cᵛ) ≫ Scheme.Modules.dualEvaluation C =
        (𝟙 (A ⊗ B) ⊗ₘ e.hom) ≫ tensorμ A B Aᵛ Bᵛ ≫
          (Scheme.Modules.dualEvaluation A ⊗ₘ Scheme.Modules.dualEvaluation B) ≫
          (λ_ (Scheme.Modules.unit X)).hom := by
  let q := tensorμ A B Aᵛ Bᵛ ≫
    (Scheme.Modules.dualEvaluation A ⊗ₘ Scheme.Modules.dualEvaluation B) ≫
    (λ_ (Scheme.Modules.unit X)).hom
  have hq : IsIso (tensorμ A B Aᵛ Bᵛ) :=
    ⟨tensorδ A B Aᵛ Bᵛ, tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩
  have : IsIso q := by dsimp only [q]; infer_instance
  have hAB : CategoryTheory.IsInvertible (A ⊗ B) := by
    exact (CategoryTheory.isInvertible_iff_of_braided _).2
      ⟨Cᵛ, ⟨tensorIso μ (Iso.refl Cᵛ) ≪≫
        asIso (Scheme.Modules.dualEvaluation C)⟩⟩
  have := hAB.isEquivalence_tensorLeft
  let w : (A ⊗ B) ⊗ Cᵛ ≅ (A ⊗ B) ⊗ (Aᵛ ⊗ Bᵛ) :=
    tensorIso μ (Iso.refl Cᵛ) ≪≫ asIso (Scheme.Modules.dualEvaluation C) ≪≫
      (asIso q).symm
  let e : Cᵛ ≅ Aᵛ ⊗ Bᵛ := (tensorLeft (A ⊗ B)).preimageIso w
  have he : (A ⊗ B) ◁ e.hom = w.hom :=
    (tensorLeft (A ⊗ B)).map_preimage w.hom
  refine ⟨e, ?_⟩
  rw [id_tensorHom]
  change _ = (A ⊗ B) ◁ e.hom ≫ q
  rw [he]
  simp only [w, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma dual_evaluation_tmul {X : Scheme.{u}} (A : X.Modules) (U : X.Opens)
    (s : Γ(A, U)) (f : Γ(Aᵛ, U)) :
    (Scheme.Modules.dualEvaluation A).app U (Scheme.Modules.tmulSection s f) =
      f.app (op (Over.mk (𝟙 U))) s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let q := (adj.homEquiv _ (Scheme.Modules.unit X)).symm
    (Scheme.Modules.presheafDualEvaluation A)
  have hh := (adj.homEquiv _ (Scheme.Modules.unit X)).apply_symm_apply
    (Scheme.Modules.presheafDualEvaluation A)
  rw [Adjunction.homEquiv_unit] at hh
  have he := congrArg (fun t ↦ t.app (op U) (s ⊗ₜ[Γ(X, U)] f)) hh
  change Scheme.Modules.Hom.app q U ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U)
    (s ⊗ₜ[Γ(X, U)] f)) = _ at he
  change Scheme.Modules.Hom.app q U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).hom U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv U
      ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U)
        (s ⊗ₜ[Γ(X, U)] f)))) = _
  have hi := congrArg (fun t ↦ Scheme.Modules.Hom.app t U
    ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U) (s ⊗ₜ[Γ(X, U)] f)))
    (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv_hom_id
  change Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).hom U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv U _) = _ at hi
  rw [hi]
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma divisor_section_evaluation {D X : Scheme.{u}} (i : D ⟶ X) :
    i.ker.toModules ◁ supportedDivisorSection i ≫
      Scheme.Modules.dualEvaluation i.ker.toModules =
        (ρ_ i.ker.toModules).hom ≫ i.ker.toModulesι := by
  apply (cancel_epi (ρ_ i.ker.toModules).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (Scheme.Modules.dualEvaluation i.ker.toModules).app U
    ((i.ker.toModules ◁ supportedDivisorSection i).app U
      ((ρ_ i.ker.toModules).inv.app U x)) = _
  rw [Scheme.Modules.rightUnitor_inv_app, Scheme.Modules.whiskerLeft_app_tmulSection,
    dual_evaluation_tmul]
  have hs := (SheafOfModules.unitHomEquiv _).apply_symm_apply
    ((SheafOfModules.homObjSectionsEquiv i.ker.toModules (Scheme.Modules.unit X)).symm
      i.ker.toModulesι)
  have he := congrArg (fun z ↦ (z.val (op U)).app (op (Over.mk (𝟙 U))) x) hs
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma tensor_section_evaluation {X : Scheme.{u}} (A B : X.Modules)
    (s : Scheme.Modules.unit X ⟶ Aᵛ) (t : Scheme.Modules.unit X ⟶ Bᵛ)
    (a : A ⟶ Scheme.Modules.unit X) (b : B ⟶ Scheme.Modules.unit X)
    (hs : A ◁ s ≫ Scheme.Modules.dualEvaluation A = (ρ_ A).hom ≫ a)
    (ht : B ◁ t ≫ Scheme.Modules.dualEvaluation B = (ρ_ B).hom ≫ b) :
    (A ⊗ B) ◁ ((λ_ (Scheme.Modules.unit X)).inv ≫ (s ⊗ₘ t)) ≫
      tensorμ A B Aᵛ Bᵛ ≫
        (Scheme.Modules.dualEvaluation A ⊗ₘ Scheme.Modules.dualEvaluation B) ≫
        (λ_ (Scheme.Modules.unit X)).hom =
      (ρ_ (A ⊗ B)).hom ≫ (a ⊗ₘ b) ≫ (λ_ (Scheme.Modules.unit X)).hom := by
  rw [whiskerLeft_comp_assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom_assoc, hs, ht, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  erw [← tensor_right_unitality_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma product_divisor_framed_iso {D₁ D₂ Z X : Scheme.{u}}
    (i₁ : D₁ ⟶ X) (i₂ : D₂ ⟶ X) (k : Z ⟶ X)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hk : k.ker = i₁.ker * i₂.ker) :
    ∃ (μ : i₁.ker.toModules ⊗ i₂.ker.toModules ≅ k.ker.toModules)
      (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ),
      μ.hom ≫ k.ker.toModulesι =
        (i₁.ker.toModulesι ⊗ₘ i₂.ker.toModulesι) ≫ (λ_ (Scheme.Modules.unit X)).hom ∧
      (μ.hom ⊗ₘ 𝟙 k.ker.toModulesᵛ) ≫ Scheme.Modules.dualEvaluation k.ker.toModules =
        (𝟙 (i₁.ker.toModules ⊗ i₂.ker.toModules) ⊗ₘ e.hom) ≫
          tensorμ i₁.ker.toModules i₂.ker.toModules i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ ≫
          (Scheme.Modules.dualEvaluation i₁.ker.toModules ⊗ₘ
            Scheme.Modules.dualEvaluation i₂.ker.toModules) ≫
          (λ_ (Scheme.Modules.unit X)).hom ∧
      supportedDivisorSection k ≫ e.hom = (λ_ (Scheme.Modules.unit X)).inv ≫
        (supportedDivisorSection i₁ ⊗ₘ supportedDivisorSection i₂) := by
  have hZ : k.ker.IsInvertible := by rw [hk]; exact h₁.mul_effectiveCartier h₂
  have := h₁.isInvertible_toModules
  have := h₂.isInvertible_toModules
  have := hZ.isInvertible_toModules
  obtain ⟨μ, hμ⟩ : ∃ μ : i₁.ker.toModules ⊗ i₂.ker.toModules ≅ k.ker.toModules,
      μ.hom ≫ k.ker.toModulesι =
        (i₁.ker.toModulesι ⊗ₘ i₂.ker.toModulesι) ≫ (λ_ (Scheme.Modules.unit X)).hom := by
    rw [hk]
    exact ideal_tensor_multiplication_iso _ _ h₁ h₂
  obtain ⟨e, he⟩ := dual_tensor_iso _ _ _ μ
  refine ⟨μ, e, hμ, he, ?_⟩
  let A := i₁.ker.toModules
  let B := i₂.ker.toModules
  let C := k.ker.toModules
  let q := tensorμ A B Aᵛ Bᵛ ≫
    (Scheme.Modules.dualEvaluation A ⊗ₘ Scheme.Modules.dualEvaluation B) ≫
    (λ_ (Scheme.Modules.unit X)).hom
  have : IsIso (tensorμ A B Aᵛ Bᵛ) :=
    ⟨tensorδ A B Aᵛ Bᵛ, tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩
  have : IsIso q := by dsimp only [q]; infer_instance
  have hAB : CategoryTheory.IsInvertible (A ⊗ B) :=
    (CategoryTheory.isInvertible_iff_of_braided _).2
      ⟨Cᵛ, ⟨tensorIso μ (Iso.refl Cᵛ) ≪≫ asIso (Scheme.Modules.dualEvaluation C)⟩⟩
  have := hAB.isEquivalence_tensorLeft
  apply (tensorLeft (A ⊗ B)).map_injective
  apply (cancel_mono q).1
  change (A ⊗ B) ◁ (supportedDivisorSection k ≫ e.hom) ≫ q = _
  rw [id_tensorHom, tensorHom_id] at he
  rw [whiskerLeft_comp_assoc, ← he, whisker_exchange_assoc, divisor_section_evaluation]
  erw [rightUnitor_naturality_assoc]
  rw [hμ]
  exact (tensor_section_evaluation A B
    (supportedDivisorSection i₁) (supportedDivisorSection i₂)
    i₁.ker.toModulesι i₂.ker.toModulesι
    (divisor_section_evaluation i₁) (divisor_section_evaluation i₂)).symm

section
attribute [local irreducible] supportedDivisorSection Scheme.Modules.dualEvaluation
  Scheme.IdealSheafData.toModules

/-- Multiplication of Cartier ideals, dual evaluation, and the canonical section.
Source: Stacks 01WT, 01WU; blueprint divisor-class clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof (DAG steps 1--2): on a common affine refinement the ideals have regular
bases f1 and f2. Their product f1*f2 is regular by two cancellations. Primality
identifies its support with the union. Ideal multiplication sends f1 tensor f2
to f1*f2, hence is an isomorphism. Dual evaluation identifies the inverse dual
map with the tensor of dual bases. The transpose section f1*f2 times its dual
basis maps to the tensor of the two transpose sections. These global maps and
their inverses glue, with no reducedness or intersection assumption. -/
theorem cartierPairTensor_geometry {D₁ D₂ Z T : Scheme.{u}}
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (k : Z ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion k]
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hk : k.ker = i₁.ker * i₂.ker) :
    k.ker.IsInvertible ∧ Set.range k = Set.range i₁ ∪ Set.range i₂ ∧
    k.openComplement = i₁.openComplement ⊓ i₂.openComplement ∧
    (∀ (U : T.affineOpens) (f₁ f₂ : Γ(T, U.1)),
      i₁.ker.ideal U = Ideal.span {f₁} → i₂.ker.ideal U = Ideal.span {f₂} →
      k.ker.ideal U = Ideal.span {f₁ * f₂}) ∧
    ∃ (μ : i₁.ker.toModules ⊗ i₂.ker.toModules ≅ k.ker.toModules)
      (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ),
      μ.hom ≫ k.ker.toModulesι =
        (i₁.ker.toModulesι ⊗ₘ i₂.ker.toModulesι) ≫ (λ_ (Scheme.Modules.unit T)).hom ∧
      (μ.hom ⊗ₘ 𝟙 k.ker.toModulesᵛ) ≫ Scheme.Modules.dualEvaluation k.ker.toModules =
        (𝟙 (i₁.ker.toModules ⊗ i₂.ker.toModules) ⊗ₘ e.hom) ≫
          tensorμ i₁.ker.toModules i₂.ker.toModules i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ ≫
          (Scheme.Modules.dualEvaluation i₁.ker.toModules ⊗ₘ
            Scheme.Modules.dualEvaluation i₂.ker.toModules) ≫
          (λ_ (Scheme.Modules.unit T)).hom ∧
      supportedDivisorSection k ≫ e.hom =
        (λ_ (Scheme.Modules.unit T)).inv ≫
          (supportedDivisorSection i₁ ⊗ₘ supportedDivisorSection i₂) := by
  have hZ : k.ker.IsInvertible := by rw [hk]; exact h₁.mul_effectiveCartier h₂
  have hs (D : Scheme.{u}) (i : D ⟶ T) [IsClosedImmersion i] :
      (i.ker.support : Set T) = Set.range i := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  have hr : Set.range k = Set.range i₁ ∪ Set.range i₂ := by
    rw [← hs Z k, hk, Scheme.IdealSheafData.support_mul]
    change (i₁.ker.support : Set T) ∪ (i₂.ker.support : Set T) = _
    rw [hs D₁ i₁, hs D₂ i₂]
  refine ⟨hZ, hr, ?_, ?_, product_divisor_framed_iso i₁ i₂ k h₁ h₂ hk⟩
  · ext x
    change x ∉ Set.range k ↔ x ∉ Set.range i₁ ∧ x ∉ Set.range i₂
    rw [hr, Set.mem_union, not_or]
  · intro U f₁ f₂ hf₁ hf₂
    rw [hk, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hf₁, hf₂,
      Ideal.span_singleton_mul_span_singleton]

end

set_option backward.isDefEq.respectTransparency false in
private theorem frame_val_map {D T : Scheme.{u}} (i : D ⟶ T)
    (hI : i.ker.IsInvertible) {U V : T.Etaleᵒᵖ} (f : U ⟶ V)
    (x : (cartierPairFrameTorsor i hI).sheaf.obj.obj U) :
    ((cartierPairFrameTorsor i hI).sheaf.obj.map f x).down.1 =
      (modulesPseudofunctor.presheafHom (Scheme.Modules.unitObj T) i.ker.toModulesᵛ).map
        ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).map f.unop).op x.down.1 := by
  simp only [cartierPairFrameTorsor, Scheme.Modules.etaleIsoTorsor, Functor.comp_map, uliftFunctor,
    Subfunctor.toFunctor_map, TypeCat.ofHom_apply, Scheme.Modules.etaleHom,
    Functor.op_map]
  rfl


set_option backward.isDefEq.respectTransparency false in
@[irreducible]
private def tensorFrameMap {D₁ D₂ Z T : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T)
    (k : Z ⟶ T)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    (U : T.Etaleᵒᵖ) (x : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U)
    (y : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U) :
    (cartierPairFrameTorsor k hZ).sheaf.obj.obj U :=
  letI := h₁.isInvertible_dual_toModules
  letI := h₂.isInvertible_dual_toModules
  letI := hZ.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₁.ker.toModulesᵛ
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₂.ker.toModulesᵛ
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible k.ker.toModulesᵛ
  Scheme.Modules.etaleIsoTorsorMk (X := T) k.ker.toModulesᵛ (U := U)
    (Scheme.Modules.tensorPullbackFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ
      ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom x.down.1 y.down.1 ≫
      (Scheme.Modules.pullback
        ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom).map e.inv) (by
      have : IsIso x.down.1 := x.down.2
      have : IsIso y.down.1 := y.down.2
      exact IsIso.comp_isIso' (inferInstance : IsIso
        (Scheme.Modules.tensorPullbackFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ
          ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom x.down.1 y.down.1))
        (inferInstance : IsIso ((Scheme.Modules.pullback
          ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom).map e.inv)))

set_option backward.isDefEq.respectTransparency false in
private theorem tensorFrameMap_natural {D₁ D₂ Z T : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T)
    (k : Z ⟶ T)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    {U V : T.Etaleᵒᵖ} (f : U ⟶ V)
    (x : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U)
    (y : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U) :
    (cartierPairFrameTorsor k hZ).sheaf.obj.map f (tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U x y) =
      tensorFrameMap i₁ i₂ k h₁ h₂ hZ e V
        ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map f x)
        ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map f y) := by
  have := h₁.isInvertible_dual_toModules
  have := h₂.isInvertible_dual_toModules
  have := hZ.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₁.ker.toModulesᵛ
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₂.ker.toModulesᵛ
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible k.ker.toModulesᵛ
  apply ULift.ext
  apply Subtype.ext
  rw [frame_val_map k hZ]
  unfold tensorFrameMap
  dsimp only [Scheme.Modules.etaleIsoTorsorMk]
  rw [frame_val_map i₁ h₁, frame_val_map i₂ h₂]
  exact Scheme.Modules.tensorPullbackFrames_presheaf_map _ _ _
    ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).map f.unop) e.inv x.down.1 y.down.1

set_option backward.isDefEq.respectTransparency false in
private theorem tensorFrameMap_left {D₁ D₂ Z T : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T)
    (k : Z ⟶ T)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    (U : T.Etaleᵒᵖ)
    (g : T.gmSheaf.obj.obj U)
    (x : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U)
    (y : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U) :
    tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U ((cartierPairFrameTorsor i₁ h₁).vadd U g x) y =
      (cartierPairFrameTorsor k hZ).vadd U g (tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U x y) := by
  unfold tensorFrameMap
  apply ULift.ext
  apply Subtype.ext
  change Scheme.Modules.tensorPullbackFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ
    ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom
    (Scheme.Modules.smulHom _ ((Additive.toMul g.down : Γ(U.unop.left, ⊤)ˣ) :
      Γ(U.unop.left, ⊤)) ≫ x.down.1) y.down.1 ≫ _ = _
  rw [Scheme.Modules.tensorPullbackFrames_scalar_left]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem tensorFrameMap_right {D₁ D₂ Z T : Scheme.{u}} (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T)
    (k : Z ⟶ T)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    (U : T.Etaleᵒᵖ)
    (g : T.gmSheaf.obj.obj U)
    (x : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U)
    (y : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U) :
    tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U x ((cartierPairFrameTorsor i₂ h₂).vadd U g y) =
      (cartierPairFrameTorsor k hZ).vadd U g (tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U x y) := by
  unfold tensorFrameMap
  apply ULift.ext
  apply Subtype.ext
  change Scheme.Modules.tensorPullbackFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ
    ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).obj U.unop).hom x.down.1
    (Scheme.Modules.smulHom _ ((Additive.toMul g.down : Γ(U.unop.left, ⊤)ˣ) :
      Γ(U.unop.left, ⊤)) ≫ y.down.1) ≫ _ = _
  rw [Scheme.Modules.tensorPullbackFrames_scalar_right]
  exact Category.assoc _ _ _

private def pairFrameMk {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible)
    (U : T.Etaleᵒᵖ)
    (x : (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj i.ker.toModulesᵛ) (hx : IsIso x) :
    (cartierPairFrameTorsor i hI).sheaf.obj.obj U :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i.ker.toModulesᵛ
  Scheme.Modules.etaleIsoTorsorMk (X := T) i.ker.toModulesᵛ (U := U) x hx

attribute [irreducible] pairFrameMk

private theorem pairFrameMk_val {D T : Scheme.{u}} (i : D ⟶ T)
    (hI : i.ker.IsInvertible) (U : T.Etaleᵒᵖ)
    (x : (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj i.ker.toModulesᵛ) (hx : IsIso x) :
    cartierPairFrameVal i hI (pairFrameMk i hI U x hx) = x := by
  unfold pairFrameMk
  rfl

private theorem pairFrameVal_injective {D T : Scheme.{u}} (i : D ⟶ T)
    (hI : i.ker.IsInvertible) (U : T.Etaleᵒᵖ) :
    Function.Injective (cartierPairFrameVal i hI (U := U)) := by
  have := hI.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i.ker.toModulesᵛ
  exact Scheme.Modules.etaleIsoTorsorVal_injective (X := T) i.ker.toModulesᵛ (U := U)

private theorem tensorFrameMap_val {D₁ D₂ Z T : Scheme.{u}}
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (k : Z ⟶ T)
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    (U : T.Etaleᵒᵖ) (x : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U)
    (y : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U) :
    cartierPairFrameVal k hZ (tensorFrameMap i₁ i₂ k h₁ h₂ hZ e U x y) =
      cartierPairTensorFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ U.unop
        (cartierPairFrameVal i₁ h₁ x) (cartierPairFrameVal i₂ h₂ y) ≫
        (Scheme.Modules.pullback U.unop.hom).map e.inv := by
  unfold tensorFrameMap
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- The cone-coordinate conversion traverses the injective-resolution representation.
private theorem pair_restrict {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : InjectiveResolution T.gmSheaf) (P : Sheaf.Torsor T.gmSheaf)
    (τ : P.sheaf.obj.obj (op (Scheme.Etale.mk V.ι))) :
    HomologicalComplex.homologyMap (cartierPairRestriction h I.cocomplex) 1
      (relativeTorsorEquiv T (Scheme.Etale.mk V.ι) I (Quotient.mk _ ⟨P, τ⟩)) =
    relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I
      (Quotient.mk _ ⟨P, P.sheaf.obj.map (cartierPairOpenInclusion h).op τ⟩) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let : Injective (I.cocomplex.X 0) := I.injective 0
  obtain ⟨s, ⟨e⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
    (resolutionLiftSequence_shortExact T I) P
  rw [relativeTorsorEquiv_presentation T (Scheme.Etale.mk V.ι) I ⟨P, τ⟩ s e,
    relativeTorsorEquiv_presentation T (Scheme.Etale.mk W.ι) I
      ⟨P, P.sheaf.obj.map (cartierPairOpenInclusion h).op τ⟩ s e]
  let z : ResolutionFramedLift T (Scheme.Etale.mk V.ι) I :=
    ⟨s, e.iso.hom.hom.app _ τ⟩
  let z' : ResolutionFramedLift T (Scheme.Etale.mk W.ι) I :=
    ⟨s, e.iso.hom.hom.app _ (P.sheaf.obj.map (cartierPairOpenInclusion h).op τ)⟩
  have hsq : HomologicalComplex.extendMap
      (𝟙 (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex)) ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T (Scheme.Etale.mk W.ι) I.cocomplex =
      relativeSectionRestriction T (Scheme.Etale.mk V.ι) I.cocomplex ≫
        HomologicalComplex.extendMap
          (etaleSectionMap (cartierPairOpenInclusion h) I.cocomplex)
          ComplexShape.embeddingUpNat := by
    rw [HomologicalComplex.extendMap_id]
    exact cartierPairRestriction_square h I.cocomplex
  let α : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex) ⟶ _ := 𝟙 _
  have hd : (I.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) 0 =
      (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z'.1 -
        (show (I.cocomplex.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))) from
          α.f 1 ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)) := by
    change _ = _ - (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s
    rw [map_zero, sub_self]
  have hr : (I.cocomplex.X 0).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op 0 =
      (show (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)) from z'.2.1) -
        (show (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)) from
          (etaleSectionMap (cartierPairOpenInclusion h) I.cocomplex).f 0 z.2.1) := by
    rw [map_zero, eq_comm, sub_eq_zero]
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (e.iso.hom.hom.naturality (cartierPairOpenInclusion h).op) τ)
  have hh := relativeFrameClass_map_eq T (Scheme.Etale.mk V.ι) I
    (Scheme.Etale.mk W.ι) I _ _ hsq z z' 0 hd hr
  simp only [HomologicalComplex.extendMap_id] at hh
  unfold cartierPairRestriction relativeSections
  exact hh


section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- Explicit frame and pseudofunctor comparisons require additional elaboration.
/-- The canonical frame quotient is a contracted product, with its actual open section,
and its Ext-normalized relative class is additive.
Source: Stacks 03AJ and blueprint divisor-class clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof (DAG steps 3--5): tensor local frames and transport by the framed dual-ideal
isomorphism. The map is invariant under (g,-g), is equivariant in both variables,
and locally is the multiplication quotient of Gm times Gm by Gm. Its local inverse
c maps to [(c,1)], proving the sheaf-quotient universal property. The canonical
sections are frames on their complements and their tensor is the product section.
In one injective resolution represent each pair by (t,b). The actual relative
cycle is (iCycles(t),-b). Tensoring lifting torsors adds t and adds the restricted
b coordinates. Passing to homology and negating to the Ext normalization gives
exactly the displayed addition, with the specified cone restriction maps. -/
theorem cartierPairTensor_frames {D₁ D₂ Z T : Scheme.{u}}
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (k : Z ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion k]
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hk : k.ker = i₁.ker * i₂.ker) (hZ : k.ker.IsInvertible)
    (e : k.ker.toModulesᵛ ≅ i₁.ker.toModulesᵛ ⊗ i₂.ker.toModulesᵛ)
    (he : supportedDivisorSection k ≫ e.hom =
      (λ_ (Scheme.Modules.unit T)).inv ≫
        (supportedDivisorSection i₁ ⊗ₘ supportedDivisorSection i₂)) :
    ∃ (τ₁ : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj
        (op (Scheme.Etale.mk i₁.openComplement.ι)))
      (τ₂ : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj
        (op (Scheme.Etale.mk i₂.openComplement.ι)))
      (τZ : (cartierPairFrameTorsor k hZ).sheaf.obj.obj
        (op (Scheme.Etale.mk (i₁.openComplement ⊓ i₂.openComplement).ι)))
      (m : ∀ U : T.Etaleᵒᵖ, (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U →
        (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U →
        (cartierPairFrameTorsor k hZ).sheaf.obj.obj U),
      cartierPairFrameVal i₁ h₁ τ₁ = supportedDivisorSectionPullback i₁ i₁.openComplement ∧
      cartierPairFrameVal i₂ h₂ τ₂ = supportedDivisorSectionPullback i₂ i₂.openComplement ∧
      cartierPairFrameVal k hZ τZ =
        supportedDivisorSectionPullback k (i₁.openComplement ⊓ i₂.openComplement) ∧
      (∀ U x y, cartierPairFrameVal k hZ (m U x y) =
        cartierPairTensorFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ U.unop
          (cartierPairFrameVal i₁ h₁ x) (cartierPairFrameVal i₂ h₂ y) ≫
          (Scheme.Modules.pullback U.unop.hom).map e.inv) ∧
      (∀ (U V : T.Etaleᵒᵖ) (f : U ⟶ V) x y,
        (cartierPairFrameTorsor k hZ).sheaf.obj.map f (m U x y) =
          m V ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map f x)
            ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map f y)) ∧
      (∀ U g x y, m U ((cartierPairFrameTorsor i₁ h₁).vadd U g x)
          ((cartierPairFrameTorsor i₂ h₂).vadd U (-g) y) = m U x y) ∧
      (∀ U g x y, m U ((cartierPairFrameTorsor i₁ h₁).vadd U g x) y =
        (cartierPairFrameTorsor k hZ).vadd U g (m U x y)) ∧
      (∀ (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
        (a : ∀ U : T.Etaleᵒᵖ, (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj U →
          (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj U → F.obj.obj U),
        (∀ (U V : T.Etaleᵒᵖ) (f : U ⟶ V) x y, F.obj.map f (a U x y) =
          a V ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map f x)
            ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map f y)) →
        (∀ U g x y, a U ((cartierPairFrameTorsor i₁ h₁).vadd U g x)
          ((cartierPairFrameTorsor i₂ h₂).vadd U (-g) y) = a U x y) →
        ∃! l : (cartierPairFrameTorsor k hZ).sheaf ⟶ F,
          ∀ U x y, l.hom.app U (m U x y) = a U x y) ∧
      m (op (Scheme.Etale.mk (i₁.openComplement ⊓ i₂.openComplement).ι))
          ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map
            (cartierPairOpenInclusion inf_le_left).op τ₁)
          ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map
            (cartierPairOpenInclusion inf_le_right).op τ₂) = τZ ∧
      (∀ I : InjectiveResolution T.gmSheaf,
        -relativeTorsorEquiv T
            (Scheme.Etale.mk (i₁.openComplement ⊓ i₂.openComplement).ι) I
            (Quotient.mk _ ⟨cartierPairFrameTorsor k hZ, τZ⟩) =
          HomologicalComplex.homologyMap (cartierPairRestriction inf_le_left I.cocomplex) 1
            (-relativeTorsorEquiv T (Scheme.Etale.mk i₁.openComplement.ι) I
              (Quotient.mk _ ⟨cartierPairFrameTorsor i₁ h₁, τ₁⟩)) +
          HomologicalComplex.homologyMap (cartierPairRestriction inf_le_right I.cocomplex) 1
            (-relativeTorsorEquiv T (Scheme.Etale.mk i₂.openComplement.ι) I
              (Quotient.mk _ ⟨cartierPairFrameTorsor i₂ h₂, τ₂⟩))) := by
  have := h₁.isInvertible_dual_toModules
  have := h₂.isInvertible_dual_toModules
  have := hZ.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₁.ker.toModulesᵛ
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible i₂.ker.toModulesᵛ
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible k.ker.toModulesᵛ
  let W := i₁.openComplement ⊓ i₂.openComplement
  have hW : (W : Set T) = (Set.range k.base)ᶜ := by
    have hh := (cartierPairTensor_geometry i₁ i₂ k h₁ h₂ hk).2.2.1
    change ((i₁.openComplement ⊓ i₂.openComplement : T.Opens) : Set T) = _
    rw [← hh]
    rfl
  let τ₁ : (cartierPairFrameTorsor i₁ h₁).sheaf.obj.obj
      (op (Scheme.Etale.mk i₁.openComplement.ι)) :=
    pairFrameMk i₁ h₁ (op (Scheme.Etale.mk i₁.openComplement.ι))
    (supportedDivisorSectionPullback i₁ i₁.openComplement)
    (cartierDivisorSectionPullback_isIso i₁ i₁.openComplement rfl)
  let τ₂ : (cartierPairFrameTorsor i₂ h₂).sheaf.obj.obj
      (op (Scheme.Etale.mk i₂.openComplement.ι)) :=
    pairFrameMk i₂ h₂ (op (Scheme.Etale.mk i₂.openComplement.ι))
    (supportedDivisorSectionPullback i₂ i₂.openComplement)
    (cartierDivisorSectionPullback_isIso i₂ i₂.openComplement rfl)
  let τZ : (cartierPairFrameTorsor k hZ).sheaf.obj.obj
      (op (Scheme.Etale.mk W.ι)) :=
    pairFrameMk k hZ (op (Scheme.Etale.mk W.ι))
    (supportedDivisorSectionPullback k W) (cartierDivisorSectionPullback_isIso k W hW)
  let m := tensorFrameMap i₁ i₂ k h₁ h₂ hZ e
  have hn (U V : T.Etaleᵒᵖ) (f : U ⟶ V) x y :
      (cartierPairFrameTorsor k hZ).sheaf.obj.map f (m U x y) =
      m V ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map f x)
        ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map f y) :=
    tensorFrameMap_natural i₁ i₂ k h₁ h₂ hZ e f x y
  have h₁m U g x y : m U ((cartierPairFrameTorsor i₁ h₁).vadd U g x) y =
      (cartierPairFrameTorsor k hZ).vadd U g (m U x y) :=
    tensorFrameMap_left i₁ i₂ k h₁ h₂ hZ e U g x y
  have h₂m U g x y : m U x ((cartierPairFrameTorsor i₂ h₂).vadd U g y) =
      (cartierPairFrameTorsor k hZ).vadd U g (m U x y) :=
    tensorFrameMap_right i₁ i₂ k h₁ h₂ hZ e U g x y
  have hs : m (op (Scheme.Etale.mk W.ι))
      ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_left).op τ₁)
      ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_right).op τ₂) = τZ := by
    apply pairFrameVal_injective k hZ (op (Scheme.Etale.mk W.ι))
    change cartierPairFrameVal k hZ (tensorFrameMap i₁ i₂ k h₁ h₂ hZ e _ _ _) = _
    rw [tensorFrameMap_val]
    dsimp only [τZ]
    rw [pairFrameMk_val]
    have hr₁ : cartierPairFrameVal i₁ h₁
        ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map
          (cartierPairOpenInclusion inf_le_left).op τ₁) =
        (Scheme.Modules.pullback W.ι).map (supportedDivisorSection i₁) := by
      dsimp only [τ₁, τ₂]
      unfold pairFrameMk cartierPairFrameVal cartierPairFrameTorsor
      change (modulesPseudofunctor.presheafHom (Scheme.Modules.unitObj T)
        i₁.ker.toModulesᵛ).map ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).map
          (cartierPairOpenInclusion inf_le_left)).op
            (supportedDivisorSectionPullback i₁ i₁.openComplement) = _
      rw [pullbackSection_eq]
      exact Scheme.Modules.pullbackMap_presheaf_map _ _ _ _
    have hr₂ : cartierPairFrameVal i₂ h₂
        ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map
          (cartierPairOpenInclusion inf_le_right).op τ₂) =
        (Scheme.Modules.pullback W.ι).map (supportedDivisorSection i₂) := by
      dsimp only [τ₁, τ₂]
      unfold pairFrameMk cartierPairFrameVal cartierPairFrameTorsor
      change (modulesPseudofunctor.presheafHom (Scheme.Modules.unitObj T)
        i₂.ker.toModulesᵛ).map ((Scheme.toProEt T ⋙ Scheme.ProEt.forget T).map
          (cartierPairOpenInclusion inf_le_right)).op
            (supportedDivisorSectionPullback i₂ i₂.openComplement) = _
      rw [pullbackSection_eq]
      exact Scheme.Modules.pullbackMap_presheaf_map _ _ _ _
    change cartierPairTensorFrames i₁.ker.toModulesᵛ i₂.ker.toModulesᵛ
      (Scheme.Etale.mk W.ι)
      (cartierPairFrameVal i₁ h₁ ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_left).op τ₁))
      (cartierPairFrameVal i₂ h₂ ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_right).op τ₂)) ≫
      (Scheme.Modules.pullback W.ι).map e.inv = supportedDivisorSectionPullback k W
    unfold cartierPairTensorFrames
    rw [hr₁, hr₂]
    change Scheme.Modules.tensorPullbackFrames _ _ W.ι
      ((Scheme.Modules.pullback W.ι).map (supportedDivisorSection i₁))
      ((Scheme.Modules.pullback W.ι).map (supportedDivisorSection i₂)) ≫ _ = _
    rw [Scheme.Modules.tensorPullbackFrames_map, ← Functor.map_comp, ← he, Category.assoc,
      e.hom_inv_id, Category.comp_id, pullbackSection_eq]
  refine ⟨τ₁, τ₂, τZ, m, pairFrameMk_val i₁ h₁ _ _ _, pairFrameMk_val i₂ h₂ _ _ _,
    pairFrameMk_val k hZ _ _ _, tensorFrameMap_val i₁ i₂ k h₁ h₂ hZ e, hn, ?_, h₁m, ?_, hs, ?_⟩
  · intro U g x y
    rw [h₁m, h₂m, ← Sheaf.Torsor.add_vadd, add_neg_cancel, Sheaf.Torsor.zero_vadd]
  · intro F a ha hi
    exact Sheaf.Torsor.binaryTorsorQuotient_universal _ _ _ m
      (fun f x y ↦ hn _ _ f x y) h₁m h₂m F a (fun f x y ↦ ha _ _ f x y) hi
  · intro I
    have h := relativeTorsorEquiv_add_of_equivariant T (Scheme.Etale.mk W.ι) I
      (cartierPairFrameTorsor i₁ h₁) (cartierPairFrameTorsor i₂ h₂)
      (cartierPairFrameTorsor k hZ) m (fun f x y ↦ hn _ _ f x y) h₁m h₂m
      ((cartierPairFrameTorsor i₁ h₁).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_left).op τ₁)
      ((cartierPairFrameTorsor i₂ h₂).sheaf.obj.map
        (cartierPairOpenInclusion inf_le_right).op τ₂)
    rw [hs, ← pair_restrict inf_le_left I, ← pair_restrict inf_le_right I] at h
    rw [h, neg_add, map_neg, map_neg]

end

/-- Yoneda class of a Mathlib-normalized short extension. The recorded positive-roof
comparison has the opposite sign on short exact sequences; retain that normalization.
Source: Stacks 06XV and the recorded Yoneda-derived comparison.
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairYonedaClass {T : Scheme.{u}}
    (Q : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : YonedaDerivedExtComparison (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (β : Ext Q T.gmSheaf 1) : YonedaExtension.Classes T.gmSheaf Q 1 :=
  (@AddEquiv.toEquiv _ _ (c.classGroup T.gmSheaf Q 0).toAdd inferInstance
    (c.comparison T.gmSheaf Q 0)).symm (-β)

private lemma supported_one_restrict {D T : Scheme.{u}} (i : D ⟶ T)
    (U : T.Etaleᵒᵖ) :
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
        ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (supportedIntegralOne T)) =
      (supportedIntegralUnit i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) := by
  let v := ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
  have hq := ConcreteCategory.congr_hom ((supportedIntegralUnit i).hom.naturality v)
    (supportedIntegralOne T)
  have h1 := ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v)
    (ULift.up 1)
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hq h1
  exact hq.symm.trans (congrArg ((supportedIntegralUnit i).hom.app U) h1.symm)

set_option backward.isDefEq.respectTransparency false in
private lemma relativeExtension_eq_of_represents {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)) G 1)
    (hβ : RelativeExtensionRepresents i P β) : β = relativeExtension i P :=
  (Classical.choose_spec (relativeExtension_existsUnique i P)).2 β hβ

private theorem relativeExtensionRepresents_mk {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (ha : ∀ (U : T.Etaleᵒᵖ) g t,
      @id (E.obj.obj U) (f.app U (P.1.vadd U g t)) = f.app U t + a.hom.app U g)
    (hb : ∀ (U : T.Etaleᵒᵖ) t,
      b.hom.app U (f.app U t) = (supportedIntegralUnit i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩))
    (hτ : @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app _ P.2) = 0) :
    RelativeExtensionRepresents i P hE.extClass := by
  exact ⟨E, a, b, hab, hE, f, ha, hb, hτ, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private lemma pole_boundary_eq_relative {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (τ : (cartierPairFrameTorsor i hI).sheaf.obj.obj
      (op (Scheme.Etale.mk i.openComplement.ι)))
    (hτ : cartierPairFrameVal i hI τ = supportedDivisorSectionPullback i i.openComplement)
    (β : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      T.gmSheaf 1) (hβ : CartierPoleBoundarySpec i hI β) :
    β = relativeExtension i ⟨cartierPairFrameTorsor i hI, τ⟩ := by
  obtain ⟨τ', E, a, b, hab, hE, f, hτ', hfa, hfb, hfτ, hext⟩ :=
    (by unfold CartierPoleBoundarySpec at hβ; exact hβ i.openComplement rfl)
  have hframe : τ' = τ := by
    have := hI.isInvertible_dual_toModules
    have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual i.ker.toModules)
    apply Scheme.Modules.etaleIsoTorsorVal_injective (Scheme.Modules.dual i.ker.toModules)
    exact hτ'.trans hτ.symm
  apply relativeExtension_eq_of_represents
  rw [hext]
  apply relativeExtensionRepresents_mk i ⟨cartierPairFrameTorsor i hI, τ⟩
    E a b hab hE f.hom
  · intro U g t
    exact (hfa U g t).trans (add_comm _ _)
  · intro U t
    exact (hfb U t).trans (supported_one_restrict i U)
  · rw [← hframe]
    exact hfτ

private theorem relative_extension_add_of_classes {D₁ D₂ Z T : Scheme.{u}}
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (k : Z ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion k]
    (h₁ : k.openComplement ≤ i₁.openComplement)
    (h₂ : k.openComplement ≤ i₂.openComplement)
    (P₁ : Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk i₁.openComplement.ι))
    (P₂ : Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk i₂.openComplement.ι))
    (PZ : Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk k.openComplement.ι))
    (hα : ∀ I : InjectiveResolution T.gmSheaf,
      -relativeTorsorEquiv T (Scheme.Etale.mk k.openComplement.ι) I (Quotient.mk _ PZ) =
        HomologicalComplex.homologyMap (cartierPairRestriction h₁ I.cocomplex) 1
          (-relativeTorsorEquiv T (Scheme.Etale.mk i₁.openComplement.ι) I
            (Quotient.mk _ P₁)) +
        HomologicalComplex.homologyMap (cartierPairRestriction h₂ I.cocomplex) 1
          (-relativeTorsorEquiv T (Scheme.Etale.mk i₂.openComplement.ι) I
            (Quotient.mk _ P₂))) :
    relativeExtension k PZ =
      (Ext.mk₀ (relativeExtensionSupportMap i₁ k h₁)).comp
          (relativeExtension i₁ P₁) (zero_add 1) +
        (Ext.mk₀ (relativeExtensionSupportMap i₂ k h₂)).comp
          (relativeExtension i₂ P₂) (zero_add 1) := by
  let I := injectiveResolution T.gmSheaf
  apply (relativeExtensionComparison k T.gmSheaf I 1).injective
  rw [map_add,
    (relative_extension_enlarge i₁ k h₁ T.gmSheaf I P₁).1,
    (relative_extension_enlarge i₂ k h₂ T.gmSheaf I P₂).1]
  rw [relative_extension_cohomology_normalization,
    ← (relative_extension_enlarge i₁ k h₁ T.gmSheaf I P₁).2,
    ← (relative_extension_enlarge i₂ k h₂ T.gmSheaf I P₂).2,
    relative_extension_cohomology_normalization,
    relative_extension_cohomology_normalization]
  exact hα I

section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal cartierPairTensorFrames

/-- Supported constant restriction and tensor addition in the relative extension
realization, with the identical equality on actual Yoneda classes and Baer addition.
Source: Stacks 03AJ, 010L, 06XV; blueprint divisor-class clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof (DAG steps 6--8): the open-closed exact sequence on constant integers has
quotient i_*Z and its open source represents sections, including for empty and
disconnected opens. The inclusion of the two open sources induces the canonical
maps q on their cokernels, preserving supported one. Pull back each extension
along q. Its lifting torsor over supported one is the original frame torsor, with
the section restricted to W and sent to zero. Form the Baer sum by diagonal
pullback and addition pushout. The two equivariant torsor maps descend to a map
from the contracted product into this Baer extension; the specified section goes
to zero. Uniqueness in lem-sp-relative-torsor-extension identifies this extension
with the product-divisor extension. The natural additive Yoneda-derived comparison
identifies this very equation with Yoneda pullback and Baer addition. Its
positive-projection convention sends a short extension to minus its Mathlib
extClass, hence the explicit minus signs inside the inverse comparison below. -/
theorem cartierPairTensor_extensions {D₁ D₂ Z T : Scheme.{u}}
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (k : Z ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion k]
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hk : k.ker = i₁.ker * i₂.ker) (hZ : k.ker.IsInvertible) :
    ∃ (q₁ : (lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z) ⟶
          (lowerStar AddCommGrpCat.{u + 1} i₁).obj (supportedIntegralConstant D₁))
      (q₂ : (lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z) ⟶
          (lowerStar AddCommGrpCat.{u + 1} i₂).obj (supportedIntegralConstant D₂)),
      supportedIntegralUnit k ≫ q₁ = supportedIntegralUnit i₁ ∧
      supportedIntegralUnit k ≫ q₂ = supportedIntegralUnit i₂ ∧
      (∀ q : (lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z) ⟶
          (lowerStar AddCommGrpCat.{u + 1} i₁).obj (supportedIntegralConstant D₁),
        supportedIntegralUnit k ≫ q = supportedIntegralUnit i₁ → q = q₁) ∧
      (∀ q : (lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z) ⟶
          (lowerStar AddCommGrpCat.{u + 1} i₂).obj (supportedIntegralConstant D₂),
        supportedIntegralUnit k ≫ q = supportedIntegralUnit i₂ → q = q₂) ∧
      (∀ (β₁ : Ext ((lowerStar AddCommGrpCat.{u + 1} i₁).obj
          (supportedIntegralConstant D₁)) T.gmSheaf 1)
        (β₂ : Ext ((lowerStar AddCommGrpCat.{u + 1} i₂).obj
          (supportedIntegralConstant D₂)) T.gmSheaf 1)
        (βZ : Ext ((lowerStar AddCommGrpCat.{u + 1} k).obj
          (supportedIntegralConstant Z)) T.gmSheaf 1),
        CartierPoleBoundarySpec i₁ h₁ β₁ → CartierPoleBoundarySpec i₂ h₂ β₂ →
        CartierPoleBoundarySpec k hZ βZ →
        βZ = (Ext.mk₀ q₁).comp β₁ (zero_add 1) +
          (Ext.mk₀ q₂).comp β₂ (zero_add 1) ∧
        ∀ c : YonedaDerivedExtComparison
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
          cartierPairYonedaClass
              ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) c βZ =
            (c.classGroup T.gmSheaf
              ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) 0).add
              (cartierPairYonedaClass
                ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) c
                ((Ext.mk₀ q₁).comp β₁ (zero_add 1)))
              (cartierPairYonedaClass
                ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) c
                ((Ext.mk₀ q₂).comp β₂ (zero_add 1)))) := by
  obtain ⟨_, _, hW, _, μ, e, _, _, he⟩ := cartierPairTensor_geometry i₁ i₂ k h₁ h₂ hk
  have hle₁ : k.openComplement ≤ i₁.openComplement := hW.trans_le inf_le_left
  have hle₂ : k.openComplement ≤ i₂.openComplement := hW.trans_le inf_le_right
  let q₁ := relativeExtensionSupportMap i₁ k hle₁
  let q₂ := relativeExtensionSupportMap i₂ k hle₂
  have hq₁ : supportedIntegralUnit k ≫ q₁ = supportedIntegralUnit i₁ ∧
      ∀ q, supportedIntegralUnit k ≫ q = supportedIntegralUnit i₁ → q = q₁ := by
    simpa only [q₁, q₂, relativeExtensionSupportMap] using
      Classical.choose_spec (relativeExtensionSupportMap_existsUnique i₁ k hle₁)
  have hq₂ : supportedIntegralUnit k ≫ q₂ = supportedIntegralUnit i₂ ∧
      ∀ q, supportedIntegralUnit k ≫ q = supportedIntegralUnit i₂ → q = q₂ := by
    simpa only [q₁, q₂, relativeExtensionSupportMap] using
      Classical.choose_spec (relativeExtensionSupportMap_existsUnique i₂ k hle₂)
  refine ⟨q₁, q₂, hq₁.1, hq₂.1, ?_, ?_, ?_⟩
  · intro q hq
    exact hq₁.2 q hq
  · intro q hq
    exact hq₂.2 q hq
  · intro β₁ β₂ βZ hβ₁ hβ₂ hβZ
    have hadd : βZ = (Ext.mk₀ q₁).comp β₁ (zero_add 1) +
        (Ext.mk₀ q₂).comp β₂ (zero_add 1) := by
      obtain ⟨τ₁, τ₂, τZ, m, hτ₁, hτ₂, hτZ, hm, hn, hi, hv, hu, hs, hα⟩ :=
        cartierPairTensor_frames i₁ i₂ k h₁ h₂ hk hZ e he
      have hb₁ := pole_boundary_eq_relative i₁ h₁ τ₁ hτ₁ β₁ hβ₁
      have hb₂ := pole_boundary_eq_relative i₂ h₂ τ₂ hτ₂ β₂ hβ₂
      have finish (W : T.Opens) (hEq : W = k.openComplement)
          (τ : (cartierPairFrameTorsor k hZ).sheaf.obj.obj (op (Scheme.Etale.mk W.ι)))
          (hτ : cartierPairFrameVal k hZ τ = supportedDivisorSectionPullback k W)
          (hα : ∀ I : InjectiveResolution T.gmSheaf,
            -relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I
                (Quotient.mk _ ⟨cartierPairFrameTorsor k hZ, τ⟩) =
              HomologicalComplex.homologyMap
                  (cartierPairRestriction (hEq.symm ▸ hle₁) I.cocomplex) 1
                (-relativeTorsorEquiv T (Scheme.Etale.mk i₁.openComplement.ι) I
                  (Quotient.mk _ ⟨cartierPairFrameTorsor i₁ h₁, τ₁⟩)) +
              HomologicalComplex.homologyMap
                  (cartierPairRestriction (hEq.symm ▸ hle₂) I.cocomplex) 1
                (-relativeTorsorEquiv T (Scheme.Etale.mk i₂.openComplement.ι) I
                  (Quotient.mk _ ⟨cartierPairFrameTorsor i₂ h₂, τ₂⟩))) :
          βZ = (Ext.mk₀ q₁).comp β₁ (zero_add 1) +
            (Ext.mk₀ q₂).comp β₂ (zero_add 1) := by
        subst W
        have hbZ := pole_boundary_eq_relative k hZ τ hτ βZ hβZ
        rw [hbZ, hb₁, hb₂]
        exact relative_extension_add_of_classes i₁ i₂ k hle₁ hle₂
          ⟨cartierPairFrameTorsor i₁ h₁, τ₁⟩ ⟨cartierPairFrameTorsor i₂ h₂, τ₂⟩
          ⟨cartierPairFrameTorsor k hZ, τ⟩ hα
      exact finish _ hW.symm τZ hτZ hα
    refine ⟨hadd, ?_⟩
    intro c
    let := c.classGroup T.gmSheaf
      ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) 0
    rw [hadd]
    unfold cartierPairYonedaClass
    simp only [neg_add]
    exact (c.comparison T.gmSheaf
      ((lowerStar AddCommGrpCat.{u + 1} k).obj (supportedIntegralConstant Z)) 0).symm.map_add _ _

end

/-- Enlargement of support commutes with every coefficient map and the connecting
homomorphisms of every short exact coefficient sequence, in all degrees.
Source: Stacks 0117 and 0G78, signed-cone restriction.
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof (DAG steps 5 and 9): the relative cone rows are short exact because evaluation
preserves the supplied degreewise splittings. Identity on global sections and
restriction on the open term define a morphism of these rows. Naturality of the
homology connecting homomorphism gives the displayed delta square. Coefficient
complex maps commute with both coordinates of the same square by presheaf
naturality. Functoriality of the cone and homology then proves their commutation
with restriction. No degree restriction is imposed. -/
theorem cartierPairTensor_naturality {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V) :
    (∀ (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
      (f : I ⟶ J) (n : ℤ),
      HomologicalComplex.homologyMap (cartierPairRestriction h I) n ≫
          HomologicalComplex.homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) n =
        HomologicalComplex.homologyMap (relativeSectionMap T (Scheme.Etale.mk V.ι) f) n ≫
          HomologicalComplex.homologyMap (cartierPairRestriction h J) n) ∧
    (∀ (S : ShortComplex
        (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
      (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
      (n : ℤ),
      relativeConnecting T (Scheme.Etale.mk V.ι) S hs n ≫
          HomologicalComplex.homologyMap (cartierPairRestriction h S.X₁) (n + 1) =
        HomologicalComplex.homologyMap (cartierPairRestriction h S.X₃) n ≫
          relativeConnecting T (Scheme.Etale.mk W.ι) S hs n) := by
  constructor
  · intro I J f n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
      (cartierPairRestriction_map h f)
  · intro S hs n
    let m : relativeShortComplex T (Scheme.Etale.mk V.ι) S ⟶
        relativeShortComplex T (Scheme.Etale.mk W.ι) S := {
      τ₁ := cartierPairRestriction h S.X₁
      τ₂ := cartierPairRestriction h S.X₂
      τ₃ := cartierPairRestriction h S.X₃
      comm₁₂ := by
        change cartierPairRestriction h S.X₁ ≫ relativeSectionMap T _ S.f =
          relativeSectionMap T _ S.f ≫ cartierPairRestriction h S.X₂
        exact cartierPairRestriction_map h S.f
      comm₂₃ := by
        change cartierPairRestriction h S.X₂ ≫ relativeSectionMap T _ S.g =
          relativeSectionMap T _ S.g ≫ cartierPairRestriction h S.X₃
        exact cartierPairRestriction_map h S.g }
    dsimp only [relativeConnecting]
    exact HomologicalComplex.HomologySequence.δ_naturality m
      (relativeShortComplex_shortExact T (Scheme.Etale.mk V.ι) S hs)
      (relativeShortComplex_shortExact T (Scheme.Etale.mk W.ι) S hs) n (n + 1) rfl

end AlgebraicGeometry.Etale
