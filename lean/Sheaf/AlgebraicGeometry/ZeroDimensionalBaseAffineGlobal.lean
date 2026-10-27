/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Sheaf.Topology.SpectralSpaceCohomologyDimension
import WeilConjectures.Mathlib.Topology.Spectral.Basic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.CategoryTheory.SpectralSequence.Vanishing
import Sheaf.CategoryTheory.SheafTensor

/-! # Affine-to-global cohomology over a zero-dimensional affine base

Source: Stacks Project, Tags 0A3G and 0732, and the fibre-chain dimension argument.
(blueprint: lem-sfb-zero-dimensional-base-affine-global).

Derived evaluation at an open object computes the ordinary module-derived sections of
its open slice. The ringed open comparison identifies that slice with the small
pro-etale site of the open subscheme, with the actual restricted ring and module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open CategoryTheory.Limits TopologicalSpace Opposite in
/-- Exactness of sections on a basis implies exactness of a short complex of abelian sheaves. -/
private theorem exact_of_basis_sections
    (X : Type u) [TopologicalSpace X]
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}))
    (h : ∀ U : Opens X, U ∈ B →
      (S.map (sheafToPresheaf _ _ ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op U))).Exact) :
    S.Exact := by
  let k := kernel.lift S.g S.f S.zero
  apply S.exact_iff_epi_kernel_lift.mpr
  suffices Sheaf.IsLocallySurjective k from Sheaf.epi_of_isLocallySurjective k
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) k.hom
  constructor
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  let t := (kernel S.g).obj.map (homOfLE hVU).op s
  let z := (kernel.ι S.g).hom.app (op V) t
  have hz : S.g.hom.app (op V) z = 0 := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (kernel.condition S.g)) (op V)) t
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (h V hV) z hz
  refine ⟨V, homOfLE hVU, ⟨y, ?_⟩, hxV⟩
  have hmono : Function.Injective ((kernel.ι S.g).hom.app (op V)) :=
    (AddCommGrpCat.mono_iff_injective _).mp
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V)).map_mono (kernel.ι S.g))
  apply hmono
  change (kernel.ι S.g).hom.app (op V) (k.hom.app (op V) y) = z
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, kernel.lift_ι]
  exact hy

private theorem open_proetale_data (X : Scheme.{u}) :
    ∃ (j : X.Opens ⥤ X.ProEt),
      j.IsContinuous (_root_.Opens.grothendieckTopology X)
        (Scheme.ProEt.topology X) ∧
      PreservesFiniteLimits j ∧
      (∀ U : X.Opens, Nonempty (j.obj U ≅ Scheme.ProEt.mk U.ι)) := by
  obtain ⟨i, hi, _, hl, _, hc, _⟩ := zariski_to_etale_core X
  let := hc
  let := hl
  let j := i ⋙ Scheme.toProEt X
  have hj : j.IsContinuous (_root_.Opens.grothendieckTopology X)
      (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp i (Scheme.toProEt X) _ X.smallEtaleTopology _
  refine ⟨j, hj, inferInstance, fun U ↦ ?_⟩
  have ho : (Scheme.ProEt.forget X).obj (j.obj U) =
      (Scheme.ProEt.forget X).obj (Scheme.ProEt.mk U.ι) :=
    congrArg (fun F ↦ F.obj U) hi
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful
    (Scheme.ProEt.forget X)).preimageIso (eqToIso ho)⟩

private theorem comparison_bound
    (X : Scheme.{u}) (j : X.Opens ⥤ X.ProEt)
    [j.IsContinuous (_root_.Opens.grothendieckTopology X)
      (Scheme.ProEt.topology X)]
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (n : ℕ)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op (j.obj U))).rightDerived n).obj F)) :
    let P := j.sheafPushforwardContinuous Ab.{u + 1}
      (_root_.Opens.grothendieckTopology X) (Scheme.ProEt.topology X)
    let _ : P.Additive := Functor.additive_of_preserves_binary_products P
    IsZero ((P.rightDerived n).obj F) := by
  dsimp
  let P := j.sheafPushforwardContinuous Ab.{u + 1}
    (_root_.Opens.grothendieckTopology X) (Scheme.ProEt.topology X)
  let : P.Additive := Functor.additive_of_preserves_binary_products P
  let I := injectiveResolution F
  let K := (P.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hz : IsZero (K.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    apply exact_of_basis_sections X {U | IsAffineOpen U} X.isBasis_affineOpens (K.sc n)
    intro U hU
    change (((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) (j.obj U)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).ExactAt n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (h U hU).of_iso (I.isoRightDerivedObj _ n).symm
  exact hz.of_iso (I.isoRightDerivedObj P n)

private theorem homeomorph_opens_dense
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) :
    h.opensCongr.equivalence.functor.IsDenseSubsite
      (_root_.Opens.grothendieckTopology Y)
      (_root_.Opens.grothendieckTopology Z) := by
  let E := h.opensCongr.equivalence
  refine { functorPushforward_mem_iff := ?_ }
  intro U S
  constructor
  · intro H y hy
    have hy' : h y ∈ E.functor.obj U := by
      change h.symm (h y) ∈ U
      simpa using hy
    obtain ⟨V, f, ⟨W, g, k, hg, _⟩, hv⟩ := H (h y) hy'
    refine ⟨W, g, hg, ?_⟩
    have hw := k.le hv
    change h.symm (h y) ∈ W at hw
    simpa using hw
  · intro H z hz
    change h.symm z ∈ U at hz
    obtain ⟨V, f, hf, hv⟩ := H (h.symm z) hz
    exact ⟨E.functor.obj V, E.functor.map f,
      ⟨V, f, 𝟙 _, hf, (Category.id_comp _).symm⟩, hv⟩

private instance zariski_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (_root_.Opens.grothendieckTopology X) Ab.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u + 1} _ _

private theorem zariski_cohomology_bound
    (X : Scheme.{u}) [SpectralSpace X] (e : ℕ)
    (hd : topologicalKrullDim X ≤ (e : WithBot ℕ∞))
    (F : Sheaf (_root_.Opens.grothendieckTopology X) Ab.{u + 1})
    (q : ℕ) (hq : e < q) :
    IsZero (((sheafToPresheaf (_root_.Opens.grothendieckTopology X) Ab.{u + 1} ⋙
      (evaluation X.Opensᵒᵖ Ab.{u + 1}).obj (op ⊤)).rightDerived q).obj F) := by
  let Y := ULift.{u + 1} X
  let h : Y ≃ₜ X := Homeomorph.ulift
  have : SpectralSpace Y := h.symm.spectralSpace
  let E := h.symm.opensCongr.equivalence
  have : E.inverse.IsDenseSubsite (_root_.Opens.grothendieckTopology Y)
      (_root_.Opens.grothendieckTopology X) := homeomorph_opens_dense h
  let T := E.sheafCongr (_root_.Opens.grothendieckTopology X)
    (_root_.Opens.grothendieckTopology Y) Ab.{u + 1}
  let : T.functor.Additive := Functor.additive_of_preserves_binary_products T.functor
  let G := sheafToPresheaf (_root_.Opens.grothendieckTopology Y) Ab.{u + 1} ⋙
    (evaluation (TopologicalSpace.Opens Y)ᵒᵖ Ab.{u + 1}).obj (op ⊤)
  have htop : E.inverse.obj ⊤ = ⊤ := h.opensCongr.map_top
  let s : T.functor ⋙ G ≅
      sheafToPresheaf (_root_.Opens.grothendieckTopology X) Ab.{u + 1} ⋙
        (evaluation X.Opensᵒᵖ Ab.{u + 1}).obj (op ⊤) :=
    NatIso.ofComponents (fun A ↦ A.obj.mapIso (eqToIso htop).symm.op) (by
      intro A B f
      exact (f.hom.naturality _).symm)
  let c := Functor.compRightDerivedObjIso T.functor G
    (fun I _ ↦ Functor.rightAcyclic_of_injective _) q F
  let : HasExt.{u + 1}
      (Sheaf (_root_.Opens.grothendieckTopology Y) Ab.{u + 1}) :=
    hasExt_of_enoughInjectives _
  have hh : Subsingleton (Sheaf.H' (T.functor.obj F) q ⊤) :=
    TopCat.Sheaf.subsingleton_H'_top_of_spectralSpace_of_dimension_le Y e
      ((IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph).trans_le hd) _ q hq
  obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    (_root_.Opens.grothendieckTopology Y) ⊤ q
  have hzH : IsZero (Sheaf.H' (T.functor.obj F) q ⊤) := by
    let := hh
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hz : IsZero ((G.rightDerived q).obj (T.functor.obj F)) :=
    hzH.of_iso (d.app (T.functor.obj F)).symm
  exact hz.of_iso ((Functor.rightDerivedObjIsoOfIso s q F).symm ≪≫ c)

private noncomputable def evaluation_iso
    (X : Scheme.{u}) {W W' : X.ProEt} (t : W ≅ W') :
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op W)) ≅
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op W')) :=
  NatIso.ofComponents (fun F ↦ F.obj.mapIso t.symm.op) (by
    intro F G f
    exact (f.hom.naturality _).symm)

private theorem internal_evaluation_comparison
    (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (W : X.ProEt) (q : ℕ) :
    IsZero (((Mod.forget R ⋙ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op W)).rightDerived q).obj M) ↔
      IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op W)).rightDerived q).obj M.X) := by
  let J := Scheme.ProEt.topology X
  let O : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let : EnoughInjectives (SheafOfModules.{u + 1} O) :=
    EnoughInjectives.of_equivalence E.inverse
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let F := sheafToPresheaf J Ab.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op W)
  have hT (I : SheafOfModules.{u + 1} O) [Injective I] :
      F.rightAcyclic ((SheafOfModules.toSheaf.{u + 1} O).obj I) := by
    let D := ULiftHom.{u + 1} X.ProEt
    let e : X.ProEt ≌ D := ULiftHom.equiv
    let K := e.inverse.inducedTopology J
    have : e.inverse.IsDenseSubsite K J := inferInstance
    let S := (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj O
    let ψ : O ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
      { hom := 𝟙 O.obj }
    have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) O.obj =
        ψ.hom ≫ e.functor.op.whiskerLeft (𝟙 S.obj) := by
      apply NatTrans.ext
      funext U
      change O.obj.map (𝟙 U) = 𝟙 _
      exact O.obj.map_id U
    have H₂ : (𝟙 S.obj) ≫ e.inverse.op.whiskerLeft ψ.hom ≫
        Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
      apply NatTrans.ext
      funext U
      change (𝟙 _) ≫ (𝟙 _) ≫ S.obj.map (𝟙 U) = 𝟙 _
      simp only [Category.id_comp]
      exact S.obj.map_id U
    let : e.symm.functor.IsContinuous K J :=
      inferInstanceAs (e.inverse.IsContinuous K J)
    let : e.symm.inverse.IsContinuous J K :=
      inferInstanceAs (e.functor.IsContinuous J K)
    let Q := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} e.symm (𝟙 S) ψ H₁ H₂
    let T := e.sheafCongr J K Ab.{u + 1}
    let : T.functor.Additive := Functor.additive_of_preserves_binary_products T.functor
    let G := sheafToPresheaf K Ab.{u + 1} ⋙
      (evaluation Dᵒᵖ Ab.{u + 1}).obj (op (e.functor.obj W))
    let c : T.functor ⋙ G ≅ F := Iso.refl _
    intro n
    let : IsGrothendieckAbelian.{u + 1} (Sheaf K Ab.{u + 1}) :=
      Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u + 1} K Ab.{u + 1}
    let : HasExt.{u + 1} (Sheaf K Ab.{u + 1}) := hasExt_of_enoughInjectives _
    have : Subsingleton
        (Sheaf.H' ((SheafOfModules.toSheaf.{u + 1} S).obj (Q.functor.obj I)) (n + 1)
          (e.functor.obj W)) :=
      injective_module_abelian_acyclic (e.functor.obj W) (Q.functor.obj I)
        (n + 1) (Nat.succ_pos n)
    obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      K (e.functor.obj W) (n + 1)
    have hzH : IsZero
        (Sheaf.H' ((SheafOfModules.toSheaf.{u + 1} S).obj (Q.functor.obj I)) (n + 1)
          (e.functor.obj W)) := AddCommGrpCat.isZero_of_subsingleton _
    have hz : IsZero ((G.rightDerived (n + 1)).obj
        (T.functor.obj ((SheafOfModules.toSheaf.{u + 1} O).obj I))) :=
      hzH.of_iso (d.app ((SheafOfModules.toSheaf.{u + 1} S).obj (Q.functor.obj I))).symm
    exact hz.of_iso ((Functor.rightDerivedObjIsoOfIso c (n + 1) _).symm ≪≫
      Functor.compRightDerivedObjIso T.functor G
        (fun I _ ↦ Functor.rightAcyclic_of_injective _) (n + 1) _)
  let c := Functor.compRightDerivedObjIso E.functor (SheafOfModules.toSheaf.{u + 1} O ⋙ F)
    (fun I _ ↦ Functor.rightAcyclic_of_injective _) q M
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} O) :=
    (moduleSheaves_colimits_forgetful O).2.2.1
  let d := Functor.compRightDerivedObjIso (SheafOfModules.toSheaf.{u + 1} O) F hT q
    (E.functor.obj M)
  have h : E.functor ⋙ (SheafOfModules.toSheaf.{u + 1} O ⋙ F) ≅ Mod.forget R ⋙ F := Iso.refl _
  exact ((Functor.rightDerivedObjIsoOfIso h q M).symm ≪≫ c ≪≫ d).isZero_iff

private theorem total_dimension_bound
    {B X : Scheme.{u}} [IsAffine B]
    (hB : ∀ p : PrimeSpectrum Γ(B, ⊤), p.asIdeal.IsMaximal)
    (g : X ⟶ B) [LocallyOfFiniteType g] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ B),
      topologicalKrullDim (pullback g b : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (e : WithBot ℕ∞) := by
  have : T1Space (PrimeSpectrum Γ(B, ⊤)) :=
    ⟨fun p ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr (hB p)⟩
  have : T1Space (Spec Γ(B, ⊤)) := by
    change T1Space (PrimeSpectrum Γ(B, ⊤))
    infer_instance
  have : T1Space B := B.isoSpec.hom.homeomorph.symm.t1Space
  have hf (b : B) : topologicalKrullDim (g.fiber b) ≤ (e : WithBot ℕ∞) := by
    have : LocallyOfFiniteType (g.fiberToSpecResidueField b) :=
      show LocallyOfFiniteType (pullback.snd g (B.fromSpecResidueField b)) by infer_instance
    let K := AlgebraicClosure (B.residueField b)
    let t := Spec.map (CommRingCat.ofHom (algebraMap (B.residueField b) K))
    calc
      topologicalKrullDim (g.fiber b) =
          topologicalKrullDim
            (pullback (g.fiberToSpecResidueField b) t : Scheme.{u}) :=
        (topologicalKrullDim_pullback_eq_of_field (g.fiberToSpecResidueField b) t).symm
      _ = topologicalKrullDim
          (pullback g (t ≫ B.fromSpecResidueField b) : Scheme.{u}) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (pullbackLeftPullbackSndIso g (B.fromSpecResidueField b) t).hom.homeomorph.isHomeomorph
      _ ≤ (e : WithBot ℕ∞) := he K (t ≫ B.fromSpecResidueField b)
  let := specializationOrder X
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun x ↦ ?_
  rw [← topologicalKrullDim_closure_singleton]
  have hs : closure ({x} : Set X) ⊆ g ⁻¹' {g x} := by
    intro y hy
    exact ((show x ⤳ y from specializes_iff_mem_closure.mpr hy).map g.continuous).eq.symm
  calc
    topologicalKrullDim (closure ({x} : Set X)) ≤ topologicalKrullDim (g ⁻¹' {g x}) :=
      (Topology.IsEmbedding.inclusion hs).isInducing.topologicalKrullDim_le
    _ = topologicalKrullDim (g.fiber (g x)) :=
      (IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo (g x)).isHomeomorph).symm
    _ ≤ (e : WithBot ℕ∞) := hf (g x)

/-- An affine-open cohomology bound gives the global bound obtained by adding the
geometric fibre dimension over a zero-dimensional affine base.

Source: Stacks Project, Tags 0A3G and 0732; Schemes Tag 01K1 and Algebra Tag 00P3.
(blueprint: lem-sfb-zero-dimensional-base-affine-global).

Proof:
1. Separated finite type over an affine makes X qcqs, hence spectral. Maximality
of the primes makes B a T1 space. Field-extension invariance of dimension gives
the ordinary fibre bound. The closure of every singleton of X lies in one fibre;
the specialization-order formula for dimension therefore gives dim X ≤ e.
2. The internal/sectionwise module equivalence preserves underlying sections.
Raise the hom universe of the site using ULiftHom and transport the ring and
modules along the site equivalence. On this equivalent small site the existing
injective-module acyclicity and derived-evaluation comparisons apply. Exactness
of forgetting modules and transport of resolutions give the comparison with
abelian derived evaluation in every degree, at every object.
3. Compose the continuous finite-limit-preserving inclusions from Zariski opens
to etale objects and then pro-etale objects. Its abelian sheaf pullback is left
exact by exact filtered Kan extension and sheafification, so pushforward P
preserves injectives.
4. Apply P to an abelian injective resolution. In degrees above a its sections
complex is exact on every affine open by the local hypothesis and step 2.
Exactness on this basis implies sheaf exactness: the kernel-lift is locally
surjective after refinement to affine neighbourhoods. Hence R^q P(M.X)=0 for q>a.
5. Transport Zariski sheaves along the homeomorphism from ULift X to X. Stacks
0A3G applied there, where space and coefficient universes agree, gives vanishing
of right-derived global sections above e for every Zariski abelian sheaf.
6. The proved source-library Grothendieck spectral-sequence rectangle bound
combines steps 4 and 5 to give global abelian vanishing above e+a. Identify
evaluation at the top open with the identity pro-etale object, then use step 2.
No coefficient restriction or Noetherian hypothesis is used. The argument
includes empty schemes and e=a=0. -/
theorem proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base
    {B X : Scheme.{u}} [IsAffine B]
    (hB : ∀ p : PrimeSpectrum Γ(B, ⊤), p.asIdeal.IsMaximal)
    (g : X ⟶ B) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e a : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ B),
      topologicalKrullDim (pullback g b : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hlocal : ∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ, a < q →
      IsZero (((Mod.forget R ⋙ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
          (op (Scheme.ProEt.mk U.ι))).rightDerived q).obj M))
    (r : ℕ) (hr : e + a < r) :
    IsZero (((Mod.forget R ⋙ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 X)))).rightDerived r).obj M) := by
  classical
  have hd := total_dimension_bound hB g e he
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  let : SpectralSpace X := {}
  obtain ⟨j, hc, hl, hj⟩ := open_proetale_data X
  let := hc
  let := hl
  let : RepresentablyFlat j := flat_of_preservesFiniteLimits j
  let J := _root_.Opens.grothendieckTopology X
  let P := j.sheafPushforwardContinuous Ab.{u + 1} J (Scheme.ProEt.topology X)
  let L := j.sheafPullback Ab.{u + 1} J (Scheme.ProEt.topology X)
  let : IsGrothendieckAbelian.{u + 1} (Sheaf J Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u + 1} J Ab.{u + 1}
  let Γ := Sheaf.sectionsFunctorAt J (⊤ : X.Opens)
  have hL : PreservesFiniteLimits L := by
    let : AB5OfSize.{u, u} Ab.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have := preservesFiniteLimits_op_lan_of_flat (H := Ab.{u + 1}) j
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  let := hL
  let : P.Additive := Functor.additive_of_preserves_binary_products P
  have hFG : P.IsAcyclicComposablePair Γ :=
    (j.sheafAdjunctionContinuous Ab.{u + 1} J
      (Scheme.ProEt.topology X)).isAcyclicComposablePair Γ
  have hR : ∀ q : ℕ, a < q → IsZero ((P.rightDerived q).obj M.X) := by
    intro q hq
    apply comparison_bound X j M.X q
    intro U hU
    have hz := (internal_evaluation_comparison X R M (Scheme.ProEt.mk U.ι) q).mp
      (hlocal U hU q hq)
    exact hz.of_iso (Functor.rightDerivedObjIsoOfIso
      (evaluation_iso X (hj U).some) q M.X)
  have hZ : ∀ p q : ℕ, e < p →
      IsZero ((Γ.rightDerived p).obj ((P.rightDerived q).obj M.X)) := by
    intro p q hp
    exact zariski_cohomology_bound X e hd _ p hp
  have hz := P.isZero_rightDerived_comp_of_lt_add Γ hFG M.X hR hZ r hr
  let t : j.obj ⊤ ≅ Scheme.ProEt.mk (𝟙 X) := (hj ⊤).some ≪≫
    (Functor.FullyFaithful.ofFullyFaithful (Scheme.ProEt.forget X)).preimageIso
      (Over.isoMk X.topIso (by
        change (⊤ : X.Opens).ι ≫ 𝟙 X = (⊤ : X.Opens).ι
        exact Category.comp_id _))
  let c : P ⋙ Γ ≅ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 X))) :=
    evaluation_iso X t
  apply (internal_evaluation_comparison X R M (Scheme.ProEt.mk (𝟙 X)) r).mpr
  exact hz.of_iso (Functor.rightDerivedObjIsoOfIso c r M.X).symm

end AlgebraicGeometry
