/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import all Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionData
import Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionExact
import Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import all Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionClass

/-!
# The degree-one Artin--Schreier kernel in a smooth proper curve family

Source: Stacks Project, Tag 0GKV, case (b), the exact sequence and its kernel.
(blueprint: lem-weil-pbc-prime-curve-artin-schreier-kernel)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
open Scheme.Modules in
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

private theorem zariskiSheafifyOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      HasSheafify ((_root_.Opens.grothendieckTopology T).over U) AddCommGrpCat.{u} :=
  fun _ ↦ inferInstance

private theorem zariskiWeakSheafifyOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      HasWeakSheafify ((_root_.Opens.grothendieckTopology T).over U) AddCommGrpCat.{u} :=
  fun U ↦ (zariskiSheafifyOver T U).isRightAdjoint

private theorem zariskiLocallyBijectiveOver (T : Type u) [TopologicalSpace T] :
    ∀ U : TopologicalSpace.Opens T,
      ((_root_.Opens.grothendieckTopology T).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun _ ↦ inferInstance

attribute [local instance 2000] zariskiSheafifyOver zariskiWeakSheafifyOver
  zariskiLocallyBijectiveOver

private theorem additive_artinSchreier (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    ∃ (wp : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
      (i : X.constantZMod p ⟶ X.etaleAdditiveSheaf) (h : i ≫ wp = 0),
      (ShortComplex.mk i wp h).ShortExact ∧
      ∀ (U : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(U.unop.left, ⊤)),
        wp.hom.app U x = ULift.up (x.down ^ p - x.down) := by
  obtain ⟨w, i, h, hw, hi⟩ := Scheme.construct_section_maps X p hp
    X.etaleAdditiveSheaf (fun _ ↦ AddEquiv.ulift) (by intro U V g x; rfl)
  refine ⟨w, i, h, ?_, ?_⟩
  · apply Scheme.artinSchreier_section_data_shortExact X p hp X.etaleAdditiveSheaf
      (fun _ ↦ AddEquiv.ulift) w i h
    · intro U V g x
      rfl
    · exact hw
    · exact hi
  · intro U x
    apply ULift.ext
    exact hw U x

private theorem rightDerived_kernel_of_epi
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (C : ShortComplex A) (hC : C.ShortExact) [Epi (v.map C.g)] :
    Nonempty ((v.rightDerived 1).obj C.X₁ ≅ kernel ((v.rightDerived 1).map C.g)) := by
  obtain ⟨D, hD, _, _⟩ := v.exists_universal_rightDerived_deltaFunctor
  have hzero : Epi ((D.F 0).map C.g) := by
    rw [hD]
    let e := v.rightDerivedZeroIsoSelf
    have he := e.hom.naturality C.g
    have hEq : (v.rightDerived 0).map C.g =
        e.hom.app _ ≫ v.map C.g ≫ e.inv.app _ := by
      apply (cancel_mono (e.hom.app C.X₃)).mp
      simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using he
    rw [hEq]
    infer_instance
  obtain ⟨hδ, _⟩ := D.exact_right C hC 0
  have hd : D.delta C hC 0 = 0 := by
    apply (cancel_epi ((D.F 0).map C.g)).mp
    simpa only [comp_zero] using hδ
  obtain ⟨hz, hex⟩ := D.exact_left C hC 0
  have hm : Mono ((D.F 1).map C.f) := hex.mono_g hd
  obtain ⟨hz', hex'⟩ := D.exact_middle C hC 1
  have hk := hex'.fIsKernel
  rw [← congrFun hD 1]
  exact ⟨hk.conePointUniqueUpToIso (limit.isLimit _)⟩

private theorem epi_lowerStar_artinSchreier {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0)
    [IsIso (Scheme.etaleAdditiveSheafToLowerStar f)]
    (w : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hw : ∀ (U : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(U.unop.left, ⊤)),
      w.hom.app U x = ULift.up (x.down ^ p - x.down)) :
    Epi ((lowerStar AddCommGrpCat.{u + 1} f).map w) := by
  obtain ⟨v, i, h, hs, hv⟩ := additive_artinSchreier S p hp
  have : Epi v := hs.epi_g
  let t := Scheme.etaleAdditiveSheafToLowerStar f
  have ht : t ≫ (lowerStar AddCommGrpCat.{u + 1} f).map w = v ≫ t := by
    ext U x
    change w.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U.unop))
      (ULift.up ((pullback.fst U.unop.hom f).appTop x.down)) =
      ULift.up ((pullback.fst U.unop.hom f).appTop (v.hom.app U x).down)
    rw [hw, hv]
    simp only [map_sub, map_pow]
    rfl
  have he : (lowerStar AddCommGrpCat.{u + 1} f).map w = inv t ≫ v ≫ t := by
    rw [← ht, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

-- Evaluate the square before substituting the concrete sheaf and cohomology maps.
private theorem pointwise_commuting_square {A B : AddCommGrpCat.{u + 1}}
    (s : End A) (r : A ⟶ B) (t : End B) (h : s ≫ r = r ≫ t) (x : A) :
    r.hom (s.hom x) = t.hom (r.hom x) := by
  exact ConcreteCategory.congr_hom h x

-- Keep scalar calculations in the endomorphism category until the final evaluation.
-- This avoids unfolding the tensor-pullback module when composing restriction maps.
private noncomputable def liftedScalarMap {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (U : S.Etale) (a : Γ(U.left, ⊤)) :
    End ((Scheme.Modules.liftedCoherentEtaleSheaf E).obj.obj (op U)) :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.map
    (((Scheme.Modules.tensorPullback U.hom).obj E).smul a)

private theorem liftedScalarMap_apply {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (U : S.Etale) (a : Γ(U.left, ⊤))
    (x : ULift.{u + 1} Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)) :
    (liftedScalarMap E U a).hom x = ULift.up (a • x.down) := rfl

private theorem liftedScalarMap_naturality {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] {U V : S.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤)) :
    liftedScalarMap E U a ≫ (Scheme.Modules.liftedCoherentEtaleSheaf E).obj.map g.op =
      (Scheme.Modules.liftedCoherentEtaleSheaf E).obj.map g.op ≫
        liftedScalarMap E V (g.left.appTop a) := by
  exact (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _).symm.trans
    ((congrArg (AddCommGrpCat.uliftFunctor.{u + 1, u}.map)
      (Scheme.Modules.etaleTensorSectionsRestriction_smul E g a)).trans
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _))

-- Package the sheaf and its natural scalar maps before doing the class argument.
private structure ScalarSheaf (S : Scheme.{u}) where
  sheaf : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  smulMap : ∀ U : S.Etale, Γ(U.left, ⊤) → End (sheaf.obj.obj (op U))
  naturality : ∀ {U V : S.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤)),
    smulMap U a ≫ sheaf.obj.map g.op =
      sheaf.obj.map g.op ≫ smulMap V (g.left.appTop a)

private noncomputable def coherentScalarSheaf {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] : ScalarSheaf S where
  sheaf := Scheme.Modules.liftedCoherentEtaleSheaf E
  smulMap := liftedScalarMap E
  naturality := liftedScalarMap_naturality E

attribute [local irreducible] liftedScalarMap

private theorem local_frobenius_formula {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hφ : ∀ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)),
      φ.hom.app T x = ULift.up (x.down ^ p))
    (U : S.Etale) (T : (pullback U.hom f).Etale)
    (x : (curveLocalStructure f U).obj.obj (op T)) :
    curveLocalFunction f U T
        (((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ).hom.app
          (op T) x) = ULift.up ((curveLocalFunction f U T x).down ^ p) := by
  have hn := (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    (pullback.snd U.hom f) inferInstance).hom.naturality φ
  have he := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.hom.app (op T)) hn) x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, localizationRestriction_map_hom_app] at he
  change curveLocalFunction f U T
    (((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ).hom.app
      (op T) x) = φ.hom.app
    (op ((MorphismProperty.Over.map ⊤
      (show Etale (pullback.snd U.hom f) from inferInstance)).obj T))
      (curveLocalFunction f U T x) at he
  exact he.trans (hφ _ _)

private theorem local_frobenius_scalar {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hφ : ∀ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)),
      φ.hom.app T x = ULift.up (x.down ^ p))
    (U : S.Etale) (a : Γ(U.left, ⊤))
    (μ ν : curveLocalStructure f U ⟶ curveLocalStructure f U)
    (hμ : IsCurveLocalScalar f U a μ) (hν : IsCurveLocalScalar f U (a ^ p) ν) :
    μ ≫ (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ =
      (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ ≫ ν := by
  let e := (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    (pullback.snd U.hom f) inferInstance).app X.etaleAdditiveSheaf
  apply (cancel_mono e.hom).mp
  ext T x
  change curveLocalFunction f U T.unop
      (((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ).hom.app T
        (μ.hom.app T x)) =
    curveLocalFunction f U T.unop
      (ν.hom.app T
        (((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ).hom.app T x))
  rw [local_frobenius_formula f p φ hφ, hμ, hν,
    local_frobenius_formula f p φ hφ]
  simp only [map_pow, mul_pow, id_eq]

private noncomputable abbrev firstAbelianImage {X S : Scheme.{u}} (f : X ⟶ S) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 1

private def CurveScalarLinearity {X S : Scheme.{u}} (f : X ⟶ S)
    (D : ScalarSheaf S)
    (e : (firstAbelianImage f).obj X.etaleAdditiveSheaf ≅
      D.sheaf) : Prop :=
  ∀ (U : S.Etale) (a : Γ(U.left, ⊤)),
      ∃ μ : curveLocalStructure f U ⟶ curveLocalStructure f U,
        IsCurveLocalScalar f U a μ ∧
        ∀ (z z' : (abelianHigherDirectImageRawPresheaf f 1 X.etaleAdditiveSheaf).obj (op U)),
          rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
            curveLocalCohomologyMap f U μ
              (rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
          e.hom.hom.app (op U) (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z') =
            (D.smulMap U a).hom (e.hom.hom.app (op U)
              (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z))

private theorem smooth_curve_scalar_data {X S : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1) :
    IsIso (Scheme.etaleAdditiveSheafToLowerStar f) ∧
      ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
        (e : (firstAbelianImage f).obj X.etaleAdditiveSheaf ≅
          (coherentScalarSheaf E).sheaf),
          CurveScalarLinearity f (coherentScalarSheaf E) e := by
  obtain ⟨h₀, E, hE, hqE, e, hlin⟩ := smooth_curve_etale_structure_direct_images f hdim
  refine ⟨h₀, E, hE, hqE, e, ?_⟩
  intro U a
  obtain ⟨μ, hμ, hm⟩ := hlin U a
  refine ⟨μ, hμ, ?_⟩
  intro z z' hz
  exact (hm z z' hz).trans
    (liftedScalarMap_apply E U a (e.hom.hom.app (op U)
      (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z))).symm

private theorem conjugate_equation {A B M : Type*}
    (c : A → B) (post : A → A) (P : B → B) (i : M → B) (j : B → M)
    (s t : M → M) (z z' : A)
    (hij : ∀ b, i (j b) = b) (hn : ∀ a, P (c a) = c (post a))
    (ha : j (c z') = s (j (c z))) (hb : j (c (post z')) = t (j (c (post z)))) :
    j (P (i (s (j (c z))))) = t (j (P (i (j (c z))))) := by
  rw [← ha, hij, hn, hb, hij, hn]

-- Evaluate conjugation while both sheaves remain abstract.
private theorem sheaf_conjugate_equation
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {B G : Sheaf J AddCommGrpCat.{u + 1}} (e : B ≅ G) (P : B ⟶ B)
    {U : Cᵒᵖ} {A : Type*} (c : A → B.obj.obj U) (post : A → A)
    (s t : End (G.obj.obj U)) (z z' : A)
    (hn : ∀ a, P.hom.app U (c a) = c (post a))
    (ha : e.hom.hom.app U (c z') = s.hom (e.hom.hom.app U (c z)))
    (hb : e.hom.hom.app U (c (post z')) = t.hom (e.hom.hom.app U (c (post z)))) :
    (e.inv ≫ P ≫ e.hom).hom.app U (s.hom (e.hom.hom.app U (c z))) =
      t.hom ((e.inv ≫ P ≫ e.hom).hom.app U (e.hom.hom.app U (c z))) := by
  have hinv (x : B.obj.obj U) : e.inv.hom.app U (e.hom.hom.app U x) = x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app U) e.hom_inv_id) x
  exact conjugate_equation c post (P.hom.app U) (e.inv.hom.app U) (e.hom.hom.app U)
    s.hom t.hom z z' hinv hn ha hb

private theorem map_commuting_pair
    {A B : Type*} [Category A] [Category B] (K : A ⥤ B) {O : A}
    (μ ρ ν : O ⟶ O) (h : μ ≫ ρ = ρ ≫ ν) :
    K.map μ ≫ K.map ρ = K.map ρ ≫ K.map ν :=
  (K.map_comp μ ρ).symm.trans ((congrArg K.map h).trans (K.map_comp ρ ν))

private theorem scalar_via_surjection {A T B M : Type*}
    (r : A → T) (hr : Function.Surjective r) (c : A → B) (k : T → B)
    (hk : ∀ z, k (r z) = c z) (j : B → M) (s : M → M) (m : T → T)
    (h : ∀ z z', r z' = m (r z) → j (c z') = s (j (c z))) :
    ∀ x, j (k (m x)) = s (j (k x)) := by
  intro x
  obtain ⟨z, rfl⟩ := hr x
  obtain ⟨z', hz'⟩ := hr (m (r z))
  rw [← hz', hk, hk]
  exact h z z' hz'

private theorem sheaf_semilinear_via_cohomology
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {B G : Sheaf J AddCommGrpCat.{u + 1}} (e : B ≅ G) (P : B ⟶ B)
    {U : Cᵒᵖ} {A T : Type*} (r : A → T) (hr : Function.Surjective r)
    (c : A → B.obj.obj U) (k : T → B.obj.obj U)
    (hk : ∀ z, k (r z) = c z) (q m n : T → T)
    (hproduct : ∀ x, q (m x) = n (q x))
    (s t : End (G.obj.obj U))
    (hn : ∀ x, P.hom.app U (k x) = k (q x))
    (ha : ∀ z z', r z' = m (r z) →
      e.hom.hom.app U (c z') = s.hom (e.hom.hom.app U (c z)))
    (hb : ∀ z z', r z' = n (r z) →
      e.hom.hom.app U (c z') = t.hom (e.hom.hom.app U (c z))) (z : A) :
    (e.inv ≫ P ≫ e.hom).hom.app U (s.hom (e.hom.hom.app U (c z))) =
      t.hom ((e.inv ≫ P ≫ e.hom).hom.app U (e.hom.hom.app U (c z))) := by
  have ha' := scalar_via_surjection r hr c k hk (e.hom.hom.app U) s.hom m ha
  have hb' := scalar_via_surjection r hr c k hk (e.hom.hom.app U) t.hom n hb
  have hbt : e.hom.hom.app U (k (q (m (r z)))) =
      t.hom (e.hom.hom.app U (k (q (r z)))) := by
    rw [hproduct]
    exact hb' (q (r z))
  simpa only [hk] using
    sheaf_conjugate_equation e P k q s t (r z) (m (r z)) hn (ha' (r z)) hbt

private theorem firstClassMap_isLocallySurjective {X S : Scheme.{u}} (f : X ⟶ S)
    (O : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective S.smallEtaleTopology (normalizationKappa f 1 O) := by
  let c := normalizationKappa f 1 O
  have hfac : toSheafify S.smallEtaleTopology
      (abelianHigherDirectImageRawPresheaf f 1 O) ≫
      (normalizationLift f 1 O).hom = c := by
    have he := ((sheafificationAdjunction S.smallEtaleTopology
      AddCommGrpCat.{u + 1}).homEquiv _ _).apply_symm_apply c
    rw [Adjunction.homEquiv_unit] at he
    exact he
  have : IsIso (normalizationLift f 1 O) := normalizationLift_isIso f 1 O
  have : IsIso (normalizationLift f 1 O).hom :=
    Functor.map_isIso (sheafToPresheaf _ _) (normalizationLift f 1 O)
  change Presheaf.IsLocallySurjective S.smallEtaleTopology c
  rw [← hfac]
  infer_instance

universe v w t
private theorem extend_local_equation
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{u + 1})
    (A : Cᵒᵖ → Type t)
    (res : ∀ {U V : C}, (V ⟶ U) → A (op U) → A (op V))
    (sm : ∀ U, A U → G.obj.obj U → G.obj.obj U)
    (q : ∀ U, A U → A U)
    (hsm : ∀ {U V : C} (g : V ⟶ U) a x,
      G.obj.map g.op (sm (op U) a x) = sm (op V) (res g a) (G.obj.map g.op x))
    (hq : ∀ {U V : C} (g : V ⟶ U) a, res g (q (op U) a) = q (op V) (res g a))
    (P : G ⟶ G) (R : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (c : R ⟶ G.obj)
    (hc : Presheaf.IsLocallySurjective J c)
    (hsep : Presheaf.IsSheaf J (G.obj ⋙ forget AddCommGrpCat.{u + 1}))
    (h : ∀ U a z, P.hom.app U (sm U a (c.app U z)) =
      sm U (q U a) (P.hom.app U (c.app U z))) :
    ∀ U a x, P.hom.app U (sm U a x) = sm U (q U a) (P.hom.app U x) := by
  intro U a x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 hsep).isSeparated _
    (Presheaf.imageSieve_mem J c x)).ext
  rintro V g ⟨z, hz⟩
  change G.obj.map g.op (P.hom.app U (sm U a x)) =
    G.obj.map g.op (sm U (q U a) (P.hom.app U x))
  have hn (y : G.obj.obj U) :
      G.obj.map g.op (P.hom.app U y) = P.hom.app (op V) (G.obj.map g.op y) :=
    (ConcreteCategory.congr_hom (P.hom.naturality g.op) y).symm
  rw [hn, hsm, hsm, hn, hq, ← hz]
  exact h (op V) (res g a) z

private theorem semilinear_from_local_classes
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
    (B G : Sheaf J AddCommGrpCat.{u + 1}) (e : B ≅ G) (P : B ⟶ B)
    (R : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (c : R ⟶ B.obj)
    (hc : Presheaf.IsLocallySurjective J c)
    (A : Cᵒᵖ → Type t)
    (res : ∀ {U V : C}, (V ⟶ U) → A (op U) → A (op V))
    (sm : ∀ U, A U → End (G.obj.obj U)) (q : ∀ U, A U → A U)
    (hsm : ∀ {U V : C} (g : V ⟶ U) a x,
      G.obj.map g.op ((sm (op U) a).hom x) = (sm (op V) (res g a)).hom (G.obj.map g.op x))
    (hq : ∀ {U V : C} (g : V ⟶ U) a, res g (q (op U) a) = q (op V) (res g a))
    (h : ∀ U a z,
      (e.inv ≫ P ≫ e.hom).hom.app U ((sm U a).hom (e.hom.hom.app U (c.app U z))) =
        (sm U (q U a)).hom ((e.inv ≫ P ≫ e.hom).hom.app U
          (e.hom.hom.app U (c.app U z)))) :
    ∀ U a, sm U a ≫ (e.inv ≫ P ≫ e.hom).hom.app U =
      (e.inv ≫ P ≫ e.hom).hom.app U ≫ sm U (q U a) := by
  let c' := c ≫ e.hom.hom
  have hc' : Presheaf.IsLocallySurjective J c' := by
    have : IsIso e.hom.hom := Functor.map_isIso (sheafToPresheaf _ _) e.hom
    exact @Presheaf.isLocallySurjective_comp _ _ J _ _ _ _ _ _ _ _ _ _ _ hc
      (Presheaf.isLocallySurjective_of_iso J e.hom.hom)
  have hG : Presheaf.IsSheaf J (G.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj G).property
  have hm := extend_local_equation J G A res (fun U a x ↦ (sm U a).hom x) q hsm hq
    (e.inv ≫ P ≫ e.hom) R c' hc' hG h
  intro U a
  ext x
  exact hm U a x

private theorem scalar_values_congr {B M : Type*}
    (j : B → M) (s : M → M) {x y x' y' : B}
    (hx : x = x') (hy : y = y') (h : j y' = s (j x')) : j y = s (j x) := by
  cases hx
  cases hy
  exact h

private theorem first_iota_coefficient {X S : Scheme.{u}} (f : X ⟶ S)
    (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf) (U : S.Etale) :
    curveLocalCohomologyMap f U
        ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ) ≫
      normalizationIota f 1 X.etaleAdditiveSheaf U =
    normalizationIota f 1 X.etaleAdditiveSheaf U ≫
      ((firstAbelianImage f).map φ).hom.app (op U) := by
  exact normalizationIota_coefficient_of_class f 1 φ
    (rawRestrictedResolution_class f 1 X.etaleAdditiveSheaf)
    (rawRestrictedResolution_class f 1 X.etaleAdditiveSheaf)
    (raw_coefficient f 1 φ) U

private theorem first_scalar_lifts {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hφ : ∀ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)),
      φ.hom.app T x = ULift.up (x.down ^ p))
    (D : ScalarSheaf S)
    (e : (firstAbelianImage f).obj X.etaleAdditiveSheaf ≅ D.sheaf)
    (hlin : CurveScalarLinearity f D e) (U : S.Etale) (a : Γ(U.left, ⊤)) :
    ∃ m n : End (rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf U),
      m ≫ curveLocalCohomologyMap f U
          ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ) =
        curveLocalCohomologyMap f U
          ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ) ≫ n ∧
      (∀ z z', rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
          m.hom (rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
        e.hom.hom.app (op U) ((normalizationKappa f 1 X.etaleAdditiveSheaf).app (op U) z') =
          (D.smulMap U a).hom (e.hom.hom.app (op U)
            ((normalizationKappa f 1 X.etaleAdditiveSheaf).app (op U) z))) ∧
      (∀ z z', rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
          n.hom (rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
        e.hom.hom.app (op U) ((normalizationKappa f 1 X.etaleAdditiveSheaf).app (op U) z') =
          (D.smulMap U (a ^ p)).hom (e.hom.hom.app (op U)
            ((normalizationKappa f 1 X.etaleAdditiveSheaf).app (op U) z))) := by
  obtain ⟨μ, hμ, hμlin⟩ := hlin U a
  obtain ⟨ν, hν, hνlin⟩ := hlin U (a ^ p)
  let L := upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)
  let K := CochainComplex.singleFunctor
      (Sheaf (pullback U.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    DerivedCategory.Q ⋙ cohomology AddCommGrpCat.{u + 1} (pullback U.hom f) 1
  refine ⟨curveLocalCohomologyMap f U μ, curveLocalCohomologyMap f U ν, ?_, ?_, ?_⟩
  · exact map_commuting_pair K μ (L.map φ) ν
      (local_frobenius_scalar f p φ hφ U a μ ν hμ hν)
  · intro z z' hz
    exact scalar_values_congr (e.hom.hom.app (op U)) (D.smulMap U a).hom
      (normalizationKappa_apply f 1 X.etaleAdditiveSheaf U z)
      (normalizationKappa_apply f 1 X.etaleAdditiveSheaf U z') (hμlin z z' hz)
  · intro z z' hz
    exact scalar_values_congr (e.hom.hom.app (op U)) (D.smulMap U (a ^ p)).hom
      (normalizationKappa_apply f 1 X.etaleAdditiveSheaf U z)
      (normalizationKappa_apply f 1 X.etaleAdditiveSheaf U z') (hνlin z z' hz)

-- The concrete comparisons are constructed once; section calculations use their laws.
private structure SemilinearityProblem (S : Scheme.{u}) (p : ℕ) where
  scalar : ScalarSheaf S
  image : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  comparison : image ≅ scalar.sheaf
  frobenius : image ⟶ image
  raw : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}
  classes : raw ⟶ image.obj
  localSurj : Presheaf.IsLocallySurjective S.smallEtaleTopology classes
  coho : S.Etale → AddCommGrpCat.{u + 1}
  evaluate : ∀ U, raw.obj (op U) ⟶ coho U
  evaluate_iso : ∀ U, IsIso (evaluate U)
  iota : ∀ U, coho U ⟶ image.obj.obj (op U)
  class_fac : ∀ U, evaluate U ≫ iota U = classes.app (op U)
  cohoFrobenius : ∀ U, End (coho U)
  coefficient : ∀ U, cohoFrobenius U ≫ iota U =
    iota U ≫ frobenius.hom.app (op U)
  scalar_lifts : ∀ (U : S.Etale) (a : Γ(U.left, ⊤)), ∃ m n : End (coho U),
    m ≫ cohoFrobenius U = cohoFrobenius U ≫ n ∧
    (∀ z z', evaluate U z' = m.hom (evaluate U z) →
      comparison.hom.hom.app (op U) (classes.app (op U) z') =
        (scalar.smulMap U a).hom
          (comparison.hom.hom.app (op U) (classes.app (op U) z))) ∧
    (∀ z z', evaluate U z' = n.hom (evaluate U z) →
      comparison.hom.hom.app (op U) (classes.app (op U) z') =
        (scalar.smulMap U (a ^ p)).hom
          (comparison.hom.hom.app (op U) (classes.app (op U) z)))

private noncomputable def curveSemilinearityProblem {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hφ : ∀ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)),
      φ.hom.app T x = ULift.up (x.down ^ p))
    (D : ScalarSheaf S)
    (e : (firstAbelianImage f).obj X.etaleAdditiveSheaf ≅ D.sheaf)
    (hlin : CurveScalarLinearity f D e) : SemilinearityProblem S p where
  scalar := D
  image := (firstAbelianImage f).obj X.etaleAdditiveSheaf
  comparison := e
  frobenius := (firstAbelianImage f).map φ
  raw := abelianHigherDirectImageRawPresheaf f 1 X.etaleAdditiveSheaf
  classes := normalizationKappa f 1 X.etaleAdditiveSheaf
  localSurj := firstClassMap_isLocallySurjective f X.etaleAdditiveSheaf
  coho := rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf
  evaluate := rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf
  evaluate_iso := isIso_rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf
  iota := normalizationIota f 1 X.etaleAdditiveSheaf
  class_fac := rawRestrictedResolution_class f 1 X.etaleAdditiveSheaf
  cohoFrobenius U := curveLocalCohomologyMap f U
    ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).map φ)
  coefficient := first_iota_coefficient f φ
  scalar_lifts := first_scalar_lifts f p φ hφ D e hlin

private theorem SemilinearityProblem.on_classes {S : Scheme.{u}} {p : ℕ}
    (v : SemilinearityProblem S p) (U : S.Etaleᵒᵖ) (a : Γ(U.unop.left, ⊤))
    (z : v.raw.obj U) :
    (v.comparison.inv ≫ v.frobenius ≫ v.comparison.hom).hom.app U
        ((v.scalar.smulMap U.unop a).hom
          (v.comparison.hom.hom.app U (v.classes.app U z))) =
      (v.scalar.smulMap U.unop (a ^ p)).hom
        ((v.comparison.inv ≫ v.frobenius ≫ v.comparison.hom).hom.app U
          (v.comparison.hom.hom.app U (v.classes.app U z))) := by
  obtain ⟨m, n, hcomm, hm, hn⟩ := v.scalar_lifts U.unop a
  have : IsIso (v.evaluate U.unop) := v.evaluate_iso U.unop
  exact sheaf_semilinear_via_cohomology v.comparison v.frobenius
    (v.evaluate U.unop) (ConcreteCategory.bijective_of_isIso _).surjective
    (v.classes.app U) (v.iota U.unop)
    (comparison_class_value _ _ _ (v.classes.app U) (v.class_fac U.unop) (fun _ ↦ rfl))
    (v.cohoFrobenius U.unop).hom m.hom n.hom
    (fun x ↦ pointwise_commuting_square _ _ _ hcomm x)
    (v.scalar.smulMap U.unop a) (v.scalar.smulMap U.unop (a ^ p))
    (fun x ↦ (pointwise_commuting_square _ _ _ (v.coefficient U.unop) x).symm) hm hn z

private theorem SemilinearityProblem.semilinear {S : Scheme.{u}} {p : ℕ}
    (v : SemilinearityProblem S p) :
    ∀ (U : S.Etale) (a : Γ(U.left, ⊤)),
      v.scalar.smulMap U a ≫
          (v.comparison.inv ≫ v.frobenius ≫ v.comparison.hom).hom.app (op U) =
        (v.comparison.inv ≫ v.frobenius ≫ v.comparison.hom).hom.app (op U) ≫
          v.scalar.smulMap U (a ^ p) := by
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have h := semilinear_from_local_classes S.smallEtaleTopology
    v.image v.scalar.sheaf v.comparison v.frobenius v.raw v.classes v.localSurj
    (fun U ↦ Γ(U.unop.left, ⊤)) (fun g a ↦ g.left.appTop a)
    (fun U a ↦ v.scalar.smulMap U.unop a) (fun _ a ↦ a ^ p)
    (fun g a x ↦ pointwise_commuting_square _ _ _ (v.scalar.naturality g a) x)
    (fun g a ↦ g.left.appTop.hom.map_pow a p) v.on_classes
  intro U a
  exact h (op U) a

private theorem first_frobenius_semilinear {X S : Scheme.{u}} (f : X ⟶ S)
    (p : ℕ) (φ : X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf)
    (hφ : ∀ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)),
      φ.hom.app T x = ULift.up (x.down ^ p))
    (D : ScalarSheaf S)
    (e : (firstAbelianImage f).obj X.etaleAdditiveSheaf ≅ D.sheaf)
    (hlin : CurveScalarLinearity f D e) :
    let F := e.inv ≫ (firstAbelianImage f).map φ ≫ e.hom
    ∀ (U : S.Etale) (a : Γ(U.left, ⊤)),
      D.smulMap U a ≫ F.hom.app (op U) =
        F.hom.app (op U) ≫ D.smulMap U (a ^ p) := by
  exact (curveSemilinearityProblem f p φ hφ D e hlin).semilinear

/-- Exact coefficient forgetting commutes with the actual first derived direct image. -/
private theorem nonempty_firstModuleAbelianIso
    (R : Type (u + 1)) [CommRing R] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Nonempty ((moduleAbelianForget R S).obj (higherDirectImage R f 1 M) ≅
      (firstAbelianImage f).obj ((moduleAbelianForget R X).obj M)) := by
  refine ⟨?_⟩
  let U := moduleAbelianForget R S
  let V := moduleAbelianForget R X
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj M
  let a := (moduleAbelianDerivedLowerStarIso R f).app K ≪≫
    (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
      ((V.mapDerivedCategoryPlusSingleFunctor 0).app M)
  exact (U.mapDerivedCategoryPlusHomologyFunctorIso 1).app
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) f).obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 1).mapIso a

/-- The first direct image with prime coefficients is the fixed-point kernel of a
Frobenius-semilinear endomorphism of a finite locally free structure module.
Source: Stacks Project, Tag 0GKV, case (b), second and third paragraphs.
(blueprint: lem-weil-pbc-prime-curve-artin-schreier-kernel)

Proof: Pullback of global functions makes p zero on X. Apply the proved
Artin--Schreier section-map constructor directly to X.etaleAdditiveSheaf with
its canonical ULift.down coordinates. Its restriction identity is definitional.
The scheme Artin--Schreier exactness theorem gives the short exact sequence of
constant Z/p, the additive structure sheaf, and the same sheaf with difference map.
The right-derived delta functor of abelian direct image supplies the exact segment
from the cokernel of f_*wp to R1 f_* Z/p to the kernel of R1 f_*wp. The smooth-curve
structure direct-image theorem identifies f_*O with O_S and R1 f_*O with the lifted
associated sheaf of a finite locally free quasi-coherent module E. On f_*O, wp is
p-th power minus identity. Artin--Schreier exactness on S makes this map epic;
its naturality with structural pullback transports epimorphy to f_*wp.
The zero-degree derived comparison is natural in wp, so this also says that
R0 f_*wp is epic. The connecting morphism is then zero by epi cancellation;
exactness at R1 f_* Z/p makes its map into R1 f_*O monic. Exactness at R1 f_*O
identifies this monomorphism with the kernel. Hence the exact segment identifies
R1 f_* Z/p with the
kernel on R1 f_*O. Put F = R1 f_*wp + identity and transport through the specified
structure comparison. To verify F(ae) = a^p F(e), first take a raw local cohomology
class over an etale object. Sectionwise p-th power intertwines multiplication by
a with multiplication by a^p. Functoriality of cohomology and the scalar formula of
the structure direct-image theorem give the same equation on raw classes. The
higher-image presheaf theorem says sections are locally represented by such classes,
so sheaf separation proves the equation for every section. Finally the exact
module/abelian direct-image comparison identifies the left term with the forgotten
prime-module higher direct image. The construction uses the full characteristic-p
closed subscheme, including nilpotents. Every comparison and exactness argument
also applies to an empty base. -/
theorem exists_prime_curve_artinSchreier_kernel
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
      (F : Scheme.Modules.liftedCoherentEtaleSheaf E ⟶
        Scheme.Modules.liftedCoherentEtaleSheaf E),
      (∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)),
        F.hom.app U (ULift.up (a.down • e.down)) =
          ULift.up (a.down ^ p •
            (@id Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)
              (F.hom.app U e).down))) ∧
      Nonempty ((moduleAbelianForget (ULift.{u + 1} (ZMod p)) S).obj
        (higherDirectImage (ULift.{u + 1} (ZMod p)) f 1
          ((constantSheaf X.smallEtaleTopology _).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) ≅
        kernel (F - 𝟙 _)) := by
  classical
  obtain ⟨h₀, E, hE, hqE, e, hlin⟩ := smooth_curve_scalar_data f hdim
  have hpX : (p : Γ(X, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg f.appTop hp
  obtain ⟨w, i, hi, hs, hw⟩ := additive_artinSchreier X p hpX
  let φ := w + 𝟙 _
  have hφ (T : X.Etaleᵒᵖ) (x : ULift.{u + 1} Γ(T.unop.left, ⊤)) :
      φ.hom.app T x = ULift.up (x.down ^ p) := by
    change ULift.up ((@id Γ(T.unop.left, ⊤) (w.hom.app T x).down) + x.down) =
      ULift.up (x.down ^ p)
    rw [hw]
    apply ULift.ext
    exact sub_add_cancel _ _
  let H := firstAbelianImage f
  let e : H.obj X.etaleAdditiveSheaf ≅
      Scheme.Modules.liftedCoherentEtaleSheaf E := e
  let F := e.inv ≫ H.map φ ≫ e.hom
  have hsemi := first_frobenius_semilinear f p φ hφ (coherentScalarSheaf E) e hlin
  refine ⟨E, hE, hqE, F, ?_, ?_⟩
  · intro U a x
    have hh := pointwise_commuting_square _ _ _ (hsemi U.unop a.down) x
    change F.hom.app U ((liftedScalarMap E U.unop a.down).hom x) =
      (liftedScalarMap E U.unop (a.down ^ p)).hom (F.hom.app U x) at hh
    exact (congrArg (fun z ↦ F.hom.app U z)
      (liftedScalarMap_apply E U.unop a.down x)).symm.trans
      (hh.trans (liftedScalarMap_apply E U.unop (a.down ^ p) (F.hom.app U x)))
  · let v := lowerStar AddCommGrpCat.{u + 1} f
    have : Epi (v.map w) := epi_lowerStar_artinSchreier f p hp w hw
    obtain ⟨k⟩ := rightDerived_kernel_of_epi v (ShortComplex.mk i w hi) hs
    let d := v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 1
    let k₁ : H.obj (X.constantZMod p) ≅ kernel (H.map w) :=
      d.app (X.constantZMod p) ≪≫ k ≪≫
        kernel.mapIso ((v.rightDerived 1).map w) (H.map w)
          (d.app X.etaleAdditiveSheaf).symm
          (d.app X.etaleAdditiveSheaf).symm (d.inv.naturality w)
    have hF : F - 𝟙 _ = e.inv ≫ H.map w ≫ e.hom := by
      change e.inv ≫ H.map (w + 𝟙 X.etaleAdditiveSheaf) ≫ e.hom - 𝟙 _ = _
      rw [H.map_add, H.map_id]
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.id_comp,
        Iso.inv_hom_id, add_sub_cancel_right]
    let k₂ : kernel (H.map w) ≅ kernel (F - 𝟙 _) :=
      kernel.mapIso (H.map w) (F - 𝟙 _) e e (by
        rw [hF]
        simp only [Iso.hom_inv_id_assoc])
    let R := ULift.{u + 1} (ZMod p)
    let M := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      (ModuleCat.of R R)
    have : X.smallEtaleTopology.PreservesSheafification
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
      GrothendieckTopology.instPreservesSheafification _ _
    let c : (moduleAbelianForget R X).obj M ≅ X.constantZMod p :=
      (constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app (ModuleCat.of R R)
    obtain ⟨m⟩ := nonempty_firstModuleAbelianIso R f M
    exact ⟨m ≪≫ H.mapIso c ≪≫ k₁ ≪≫ k₂⟩

end AlgebraicGeometry.Etale
