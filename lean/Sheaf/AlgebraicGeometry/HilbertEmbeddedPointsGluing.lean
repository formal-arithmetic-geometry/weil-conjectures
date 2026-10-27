/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.Topology.GlueSheavesOfModules
import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import all WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineCapture
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.ModuleSubobjectEqOnCover
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian

/-! # Gluing the affine embedded-point submodules

Source: Stacks Project, Divisors, Tag 02OL, proof of Lemma 31.5.8
(blueprint: lem-sc-hilbert-embedded-points-gluing).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

local instance sliceSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasSheafify ((_root_.Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  inferInstance

local instance sliceLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((_root_.Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem surjective_slice_top_of_epi (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) {M N : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Function.Surjective ((φ.val.app (op (Over.mk (𝟙 U)))).hom) := by
  let T := (overEquiv U).functor
  let : IsAffine U.toScheme := hU
  have : (T.obj M).IsQuasicoherent := isQuasicoherent_overEquiv X U M
  have : (T.obj N).IsQuasicoherent := isQuasicoherent_overEquiv X U N
  have hs := surjective_affine_of_epi (T.map φ) (isAffineOpen_top U.toScheme)
  let a : U.overEquivalence.inverse.obj ⊤ ≅ Over.mk (𝟙 U) :=
    Over.isoMk (eqToIso U.ι_image_top)
  intro y
  obtain ⟨x, hx⟩ := hs (N.val.map a.hom.op y)
  refine ⟨M.val.map a.inv.op x, ?_⟩
  rw [PresheafOfModules.naturality_apply]
  change N.val.map a.inv.op ((T.map φ).app ⊤ x) = y
  rw [hx]
  have hn : N.val.presheaf.map a.hom.op ≫ N.val.presheaf.map a.inv.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, a.inv_hom_id, op_id]
    exact N.val.presheaf.map_id _
  exact congrArg (fun k ↦ k y) hn

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The subsheaf generated on an affine chart by a finite section submodule.
Construct it as the image of the finite free map defined by a finite spanning set.
The image, rather than the spanning set, is the mathematical object used downstream.
Source: Stacks Project, Schemes, Tag 01I6; Divisors, Tag 02OL.
(blueprint: lem-sc-hilbert-embedded-points-gluing). -/
noncomputable def affineSectionSubmodule (X : Scheme.{u}) (F : X.Modules)
    (U : X.Opens) (N : Submodule Γ(X, U) Γ(F, U))
    (hN : Module.Finite Γ(X, U) N) :
    Σ Q : SheafOfModules.{u} (X.ringCatSheaf.over U), Q ⟶ F.over U := by
  classical
  let S := (Module.Finite.iff_fg.mp hN).choose
  let A := X.ringCatSheaf.over U
  let G := F.over U
  let σ (i : S) : G.sections := G.val.sectionsMk
    (fun V ↦ F.val.map V.unop.hom.op i.1)
    (by
      intro V W f
      change F.val.map f.unop.left.op (F.val.map V.unop.hom.op i.1) =
        F.val.map W.unop.hom.op i.1
      exact congrArg (fun k ↦ k i.1) (F.presheaf.map_comp
        V.unop.hom.op f.unop.left.op) |>.symm)
  let φ : SheafOfModules.free (R := A) S ⟶ G := G.freeHomEquiv.symm σ
  exact ⟨Abelian.image φ, Abelian.image.ι φ⟩

set_option maxHeartbeats 500000 in
-- Finite free sections and slice-image transport require extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem affine_local_realization (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (N : Submodule Γ(X, U) Γ(F, U)) (hN : Module.Finite Γ(X, U) N) :
    let Q := affineSectionSubmodule X F U N hN
    Mono Q.2 ∧ Q.1.IsQuasicoherent ∧
      LinearMap.range (Q.2.val.app (op (Over.mk (𝟙 U)))).hom = N := by
  classical
  let S := (Module.Finite.iff_fg.mp hN).choose
  have hS : Submodule.span Γ(X, U) (S : Set Γ(F, U)) = N :=
    (Module.Finite.iff_fg.mp hN).choose_spec
  let A := X.ringCatSheaf.over U
  let G := F.over U
  let σ (i : S) : G.sections := G.val.sectionsMk
    (fun V ↦ F.val.map V.unop.hom.op i.1)
    (by
      intro V W f
      change F.val.map f.unop.left.op (F.val.map V.unop.hom.op i.1) =
        F.val.map W.unop.hom.op i.1
      exact congrArg (fun k ↦ k i.1) (F.presheaf.map_comp
        V.unop.hom.op f.unop.left.op) |>.symm)
  let φ : SheafOfModules.free (R := A) S ⟶ G := G.freeHomEquiv.symm σ
  let V := op (Over.mk (𝟙 U))
  have hb (i : S) (r : Γ(X, U)) :
      φ.val.app V ((SheafOfModules.ιFree (R := A) (I := S) i).val.app V r) = r • i.1 := by
    have h : G.freeHomEquiv φ i = σ i := by
      dsimp only [φ]
      rw [Equiv.apply_symm_apply]
    have h1 := congrArg (fun s : G.sections ↦ s.val V) h
    change (SheafOfModules.ιFree (R := A) (I := S) i ≫ φ).val.app V
      (1 : A.obj.obj V) = _ at h1
    have hlin := (SheafOfModules.ιFree (R := A) (I := S) i ≫ φ).val.app V |>.hom.map_smul
      (r : A.obj.obj V) (1 : A.obj.obj V)
    change _ = r • _ at hlin
    simp only [smul_eq_mul, mul_one] at hlin
    change (SheafOfModules.ιFree (R := A) (I := S) i ≫ φ).val.app V r = _
    rw [hlin, h1]
    have hid : F.val.map (𝟙 U).op i.1 = i.1 := by simp
    have he : (σ i).val V = i.1 := hid
    rw [he]
  have hr : LinearMap.range (φ.val.app V).hom = N := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      let e := SheafOfModules.freeSectionsLinearEquiv (R := A) S V
      have hx : x = ∑ i : S, (SheafOfModules.ιFree (R := A) (I := S) i).val.app V (e x i) :=
        (e.symm_apply_apply x).symm
      rw [hx, map_sum]
      exact N.sum_mem fun i _ ↦ by rw [hb]; exact N.smul_mem _ (hS ▸
        Submodule.subset_span i.2)
    · rw [← hS]
      apply Submodule.span_le.mpr
      intro i hi
      exact ⟨(SheafOfModules.ιFree (R := A) (I := S) (⟨i, hi⟩ : S)).val.app V (1 : A.obj.obj V),
        (hb ⟨i, hi⟩ 1).trans (one_smul _ _ )⟩
  have : G.IsQuasicoherent := SheafOfModules.isQuasicoherent_over F U
  have hQ : (Abelian.image φ).IsQuasicoherent := quasiCoherent_slice_image U φ
  have : (Abelian.image φ).IsQuasicoherent := hQ
  have hs : Function.Surjective ((Abelian.factorThruImage φ).val.app V).hom :=
    surjective_slice_top_of_epi X U hU (Abelian.factorThruImage φ)
  change Mono (Abelian.image.ι φ) ∧ (Abelian.image φ).IsQuasicoherent ∧
    LinearMap.range ((Abelian.image.ι φ).val.app V).hom = N
  refine ⟨inferInstance, hQ, ?_⟩
  apply Eq.trans _ hr
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hs x
    exact ⟨z, (congrArg (fun k ↦ k.val.app V z) (Abelian.image.fac φ)).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(Abelian.factorThruImage φ).val.app V x,
      congrArg (fun k ↦ k.val.app V x) (Abelian.image.fac φ)⟩

attribute [local irreducible] affineSectionSubmodule

set_option backward.defeqAttrib.useBackward true

private theorem subobject_eq_of_cokernel_composites
    {C : Type*} [Category C] [Abelian C] {A B M : C}
    (f : A ⟶ M) (g : B ⟶ M) [Mono f] [Mono g]
    (hf : f ≫ cokernel.π g = 0) (hg : g ≫ cokernel.π f = 0) :
    Subobject.mk f = Subobject.mk g := by
  apply le_antisymm
  · exact Subobject.mk_le_mk_of_comm (Abelian.monoLift g f hf)
      (Abelian.monoLift_comp g f hf)
  · exact Subobject.mk_le_mk_of_comm (Abelian.monoLift f g hg)
      (Abelian.monoLift_comp f g hg)

set_option backward.isDefEq.respectTransparency false in
private theorem slice_comp_cokernel_eq_zero_on_basis
    (X : Scheme.{u}) (U : X.Opens)
    {A B M : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (f : A ⟶ M) (g : B ⟶ M) (P : X.Opens → Prop)
    (hbase : ∀ (W : X.Opens), W ≤ U → ∀ x ∈ W,
      ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧ P V)
    (hrange : ∀ (W : X.Opens) (hW : W ≤ U), P W →
      Set.range (f.val.app (op (Over.mk (homOfLE hW)))) ⊆
        Set.range (g.val.app (op (Over.mk (homOfLE hW))))) :
    f ≫ cokernel.π g = 0 := by
  let q := cokernel.π g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply (forget₂ _ AddCommGrpCat).map_injective
  let I := {V : X.Opens // V ≤ W.unop.left ∧ P V}
  let V (i : I) : Over U := Over.mk (homOfLE (i.2.1.trans W.unop.hom.le))
  let v (i : I) : V i ⟶ W.unop := Over.homMk (homOfLE i.2.1)
  have hv : Sieve.ofArrows V v ∈ ((_root_.Opens.grothendieckTopology X).over U) W.unop := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    intro x hx
    obtain ⟨Z, hZW, hxZ, hP⟩ := hbase W.unop.left W.unop.hom.le x hx
    refine ⟨Z, homOfLE hZW, ?_, hxZ⟩
    exact Sieve.ofArrows_mk (fun i : I ↦ (V i).left) (fun i : I ↦ (v i).left)
      (⟨Z, hZW, hP⟩ : I)
  apply (cokernel g).isSheaf.hom_ext_ofArrows v hv
  intro i
  ext x
  have hz0 : ((SheafOfModules.Hom.val
      (0 : A ⟶ cokernel g)).app W) x = 0 := rfl
  change (cokernel g).val.map (v i).op ((f ≫ cokernel.π g).val.app W x) =
    (cokernel g).val.map (v i).op (((SheafOfModules.Hom.val
      (0 : A ⟶ cokernel g)).app W) x)
  rw [hz0, map_zero]
  have hi := hrange i.1 (i.2.1.trans W.unop.hom.le) i.2.2
  obtain ⟨y, hy⟩ := hi ⟨A.val.map (v i).op x, rfl⟩
  have hz := congrArg (fun k ↦ k.val.app (op (V i)) y) (cokernel.condition g)
  change (cokernel g).val.map (v i).op (q.val.app W (f.val.app W x)) = 0
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply, ← hy]
  exact hz

set_option backward.isDefEq.respectTransparency false in
private theorem overlap_inclusion_app
    (X : Scheme.{u}) (F : X.Modules) (U V : X.Opens) (h : U ≤ V)
    {G : SheafOfModules.{u} (X.ringCatSheaf.over V)} (ι : G ⟶ F.over V)
    (W : X.Opens) (hW : W ≤ U) :
    ((SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).map ι ≫
      (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).hom.app F).val.app
        (op (Over.mk (homOfLE hW))) =
      ι.val.app (op (Over.mk (homOfLE (hW.trans h)))) := rfl

set_option maxHeartbeats 800000 in
-- Comparing nested slice restrictions requires additional elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
private theorem glue_local_submodules
    (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ⨆ i, U i = ⊤)
    (Fi : ∀ i, SheafOfModules.{u} (X.ringCatSheaf.over (U i)))
    (ι : ∀ i, Fi i ⟶ F.over (U i)) (hmono : ∀ i, Mono (ι i))
    (hcompat : ∀ (i j : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (∃ (f : Γ(X, U i)) (g : Γ(X, U j)),
        W = X.basicOpen f ∧ W = X.basicOpen g) →
      Set.range ((ι i).val.app (op (Over.mk (homOfLE hi)))) =
        Set.range ((ι j).val.app (op (Over.mk (homOfLE hj))))) :
    ∃ (H : X.Modules) (f : H ⟶ F), Mono f ∧
      ∃ (e : ∀ i, H.over (U i) ≅ Fi i), ∀ i, f.over (U i) = (e i).hom ≫ ι i := by
  let R := X.ringCatSheaf
  let T (i j : I) := SheafOfModules.overMap R
    (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
  let a (i j : I) : (T i j).obj (Fi i) ⟶ F.over (U i ⊓ U j) :=
    (T i j).map (ι i) ≫ (SheafOfModules.overFunctorMap R
      (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).hom.app F
  let S (i j : I) := SheafOfModules.overMap R
    (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))
  let b (i j : I) : (S i j).obj (Fi j) ⟶ F.over (U i ⊓ U j) :=
    (S i j).map (ι j) ≫ (SheafOfModules.overFunctorMap R
      (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).hom.app F
  have (i j : I) : Mono (a i j) := by
    dsimp [a, T]
    have := hmono i
    infer_instance
  have (i j : I) : Mono (b i j) := by
    dsimp [b, S]
    have := hmono j
    infer_instance
  have hab (i j : I) : Subobject.mk (a i j) = Subobject.mk (b i j) := by
    let P (W : X.Opens) := ∃ (f : Γ(X, U i)) (g : Γ(X, U j)),
      W = X.basicOpen f ∧ W = X.basicOpen g
    have hb (W : X.Opens) (hW : W ≤ U i ⊓ U j) (x : X) (hx : x ∈ W) :
        ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧ P V := by
      obtain ⟨f, hfW, hxf⟩ := (hU i).exists_basicOpen_le ⟨x, hx⟩ ((hW hx).1)
      obtain ⟨r, g, hrg, hxr⟩ := exists_basicOpen_le_affine_inter
        ((hU i).basicOpen f) (hU j) x ⟨hxf, (hW hx).2⟩
      obtain ⟨c, hc⟩ := (hU i).basicOpen_basicOpen_is_basicOpen f r
      exact ⟨X.basicOpen r, (X.basicOpen_le r).trans hfW, hxr, c, g, hc.symm, hrg⟩
    have hr (W : X.Opens) (hW : W ≤ U i ⊓ U j) (hP : P W) :
        Set.range ((a i j).val.app (op (Over.mk (homOfLE hW)))) =
          Set.range ((b i j).val.app (op (Over.mk (homOfLE hW)))) := by
      dsimp only [a, b, T, S]
      rw [overlap_inclusion_app, overlap_inclusion_app]
      exact hcompat i j W (hW.trans inf_le_left) (hW.trans inf_le_right) hP
    exact subobject_eq_of_cokernel_composites (a i j) (b i j)
      (slice_comp_cokernel_eq_zero_on_basis X (U i ⊓ U j)
        (a i j) (b i j) P hb (fun W hW hP ↦ (hr W hW hP).le))
      (slice_comp_cokernel_eq_zero_on_basis X (U i ⊓ U j)
        (b i j) (a i j) P hb (fun W hW hP ↦ (hr W hW hP).ge))
  let t (i j : I) : (T i j).obj (Fi i) ≅ (S i j).obj (Fi j) :=
    Subobject.isoOfMkEqMk (a i j) (b i j) (hab i j)
  have ht (i j : I) : (t i j).hom ≫ b i j = a i j :=
    Subobject.ofMkLEMk_comp (hab i j).le
  have htapp (i j : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      (t i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
        (ι j).val.app (op (Over.mk (homOfLE hj))) =
          (ι i).val.app (op (Over.mk (homOfLE hi))) := by
    have h' := congrArg (fun k ↦ k.val.app
      (op (Over.mk (homOfLE (le_inf hi hj))))) (ht i j)
    change (t i j).hom.val.app _ ≫ (b i j).val.app _ = (a i j).val.app _ at h'
    dsimp only [a, b, T, S] at h'
    rw [overlap_inclusion_app, overlap_inclusion_app] at h'
    exact h'
  have hcoc (i j k : I) (W : X.Opens)
      (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
      (t i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
        (t i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (t j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk)))) := by
    have := hmono k
    have : Mono ((ι k).val.app (op (Over.mk (homOfLE hk)))) := by
      exact inferInstanceAs (Mono ((SheafOfModules.evaluation _ _).map (ι k)))
    apply (cancel_mono ((ι k).val.app (op (Over.mk (homOfLE hk))))).mp
    rw [Category.assoc, htapp j k W hj hk, htapp i k W hi hk, htapp i j W hi hj]
  obtain ⟨H, e, he⟩ := (glue_sheaves_of_modules X.toRingedSpace I U hcover).2.2 Fi t hcoc
  obtain ⟨f, hf, _⟩ := (glue_sheaves_of_modules X.toRingedSpace I U hcover).1 H F
    (fun i ↦ (e i).hom ≫ ι i) (by
      intro i j W hi hj
      change (e i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
          (ι i).val.app (op (Over.mk (homOfLE hi))) =
        (e j).hom.val.app (op (Over.mk (homOfLE hj))) ≫
          (ι j).val.app (op (Over.mk (homOfLE hj)))
      rw [← htapp i j W hi hj, ← Category.assoc, he])
  have hfmono : Mono f := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro W s s' h
    let Q : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨H.val.presheaf, H.isSheaf⟩
    apply Q.eq_of_locally_eq' (fun i ↦ W.unop ⊓ U i) W.unop
      (fun i ↦ homOfLE inf_le_left)
      (by simp only [← inf_iSup_eq, hcover, inf_top_eq, le_refl])
    intro i
    have : Mono (f.over (U i)) := by rw [hf]; have := hmono i; infer_instance
    have hinj : Function.Injective
        ((f.over (U i)).val.app (op (Over.mk (homOfLE
          (inf_le_right : W.unop ⊓ U i ≤ U i))))).hom := by
      exact (ModuleCat.mono_iff_injective _).mp
        (inferInstanceAs (Mono ((SheafOfModules.evaluation _ _).map (f.over (U i)))))
    apply hinj
    change f.val.app (op (W.unop ⊓ U i))
        (H.val.map (homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op s) =
      f.val.app (op (W.unop ⊓ U i))
        (H.val.map (homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op s')
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg (fun z ↦ F.val.map (homOfLE
      (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op z) h
  exact ⟨H, f, hfmono, e, hf⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coherent_submodule_gluing
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (I : Type u) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (N : ∀ i, Submodule (Γ(X, U i)) (Γ(F, U i)))
    (Fi : ∀ i, SheafOfModules.{u} (X.ringCatSheaf.over (U i)))
    (ι : ∀ i, Fi i ⟶ F.over (U i))
    (hmono : ∀ i, Mono (ι i)) (hqc : ∀ i, (Fi i).IsQuasicoherent)
    (hsections : ∀ i,
      LinearMap.range ((ι i).val.app (op (Over.mk (𝟙 (U i))))).hom = N i)
    (hcompat : ∀ (i j : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (∃ (f : Γ(X, U i)) (g : Γ(X, U j)),
        W = X.basicOpen f ∧ W = X.basicOpen g) →
      Set.range ((ι i).val.app (op (Over.mk (homOfLE hi)))) =
        Set.range ((ι j).val.app (op (Over.mk (homOfLE hj))))) :
    ∃! K : Subobject F,
      RingedSpace.IsCoherent X.toRingedSpace (K : X.Modules) ∧
      (∀ (i : I) (W : X.Opens) (hi : W ≤ U i),
        Set.range (K.arrow.app W) =
          Set.range ((ι i).val.app (op (Over.mk (homOfLE hi))))) ∧
      (∀ i, Nonempty (Γ((cokernel K.arrow : X.Modules), U i) ≃ₗ[Γ(X, U i)]
        (Γ(F, U i) ⧸ N i))) := by
  have hcover' : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨H, f, hmono', e, he⟩ := glue_local_submodules X F I U hU hcover' Fi ι hmono hcompat
  have hH (i : I) : (H.over (U i)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U i))).prop_of_iso
      (e i).symm (hqc i)
  have : H.IsQuasicoherent := SheafOfModules.IsQuasicoherent.of_coversTop H U
    ((_root_.Opens.coversTop_iff _ U).mpr hcover')
  let K := Subobject.mk f
  let a : (K : X.Modules) ≅ H := Subobject.underlyingIso f
  have hKqc : (K : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso a.symm inferInstance
  have hKcoh : RingedSpace.IsCoherent X.toRingedSpace (K : X.Modules) :=
    (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F
    (K : X.Modules) K.arrow hF inferInstance hKqc |>.1
  have hrange (i : I) (W : X.Opens) (hi : W ≤ U i) :
      Set.range (K.arrow.app W) =
        Set.range ((ι i).val.app (op (Over.mk (homOfLE hi)))) := by
    have hf : K.arrow = a.hom ≫ f := (Subobject.underlyingIso_hom_comp_eq_mk f).symm
    have hfi (x) := congrArg (fun k ↦ k.val.app
      (op (Over.mk (homOfLE hi))) x) (he i)
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(e i).hom.val.app _ (a.hom.app W x), ?_⟩
      exact (hfi _).symm.trans (congrArg (fun k ↦ k.app W x) hf.symm)
    · rintro ⟨x, rfl⟩
      have hiso : IsIso ((e i).hom.val.app (op (Over.mk (homOfLE hi)))) :=
        inferInstanceAs (IsIso ((SheafOfModules.evaluation _ _).map (e i).hom))
      obtain ⟨z, rfl⟩ :=
        (ConcreteCategory.bijective_of_isIso ((e i).hom.val.app
          (op (Over.mk (homOfLE hi))))).2 x
      obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (a.hom.app W)).2 z
      exact ⟨w, (congrArg (fun k ↦ k.app W w) hf).trans (hfi _)⟩
  refine ⟨K, ⟨hKcoh, hrange, ?_⟩, ?_⟩
  · have : F.IsQuasicoherent :=
      ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
    intro i
    have hn : LinearMap.range (K.arrow.val.app (op (U i))).hom = N i := by
      ext s
      exact Set.ext_iff.mp (hrange i (U i) le_rfl) s |>.trans
        (by
          have hid : homOfLE (le_rfl : U i ≤ U i) = 𝟙 (U i) := Subsingleton.elim _ _
          change s ∈ LinearMap.range ((ι i).val.app
            (op (Over.mk (homOfLE le_rfl)))).hom ↔ s ∈ N i
          rw [hid, hsections])
    obtain ⟨q, _⟩ := (quasiCoherent_cokernel_image K.arrow).2.2.2.2.2.2.2.2 ⟨U i, hU i⟩
      |>.2.2.2
    exact ⟨q.symm.trans (Submodule.quotEquivOfEq _ _ hn)⟩
  · intro L hL
    have h := module_subobject_eq_on_cover U hcover L.arrow K.arrow
      (fun i W hi ↦ (hL.2.1 i W hi).trans (hrange i W hi).symm)
    simpa only [Subobject.mk_arrow] using h

set_option backward.isDefEq.respectTransparency false in
/-- Compatible finite submodules on an affine cover glue to a unique coherent subobject.
The affine realizations are constructed as images of finite free maps; their ranges on
principal opens are the localized submodules, and compatibility is required on opens
principal in both charts. The cokernel has the prescribed affine section quotients.
Source: Stacks Project, Divisors, Tag 02OL, proof of Lemma 31.5.8.
(blueprint: lem-sc-hilbert-embedded-points-gluing).

Proof: Realize each finite section submodule by its finite free presentation and take
the sheaf image. Affine exactness identifies its section image with the given submodule.
The images are quasi-coherent. Equal ranges on overlaps identify the local subobjects;
cancellation of their inclusions proves the cocycle condition. Glue sheaves and maps,
then use local quasi-coherence and the coherent-submodule criterion. The affine
cokernel formula gives the quotient sections. Local range equality proves uniqueness. -/
theorem existsUnique_coherent_submodule_of_affine_cover
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (I : Type u) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (N : ∀ i, Submodule Γ(X, U i) Γ(F, U i))
    (hN : ∀ i, Module.Finite Γ(X, U i) (N i))
    (hcompat : ∀ (i j : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (∃ (f : Γ(X, U i)) (g : Γ(X, U j)),
        W = X.basicOpen f ∧ W = X.basicOpen g) →
      Set.range ((affineSectionSubmodule X F (U i) (N i) (hN i)).2.val.app
        (op (Over.mk (homOfLE hi)))) =
      Set.range ((affineSectionSubmodule X F (U j) (N j) (hN j)).2.val.app
        (op (Over.mk (homOfLE hj))))) :
    ∃! K : Subobject F,
      RingedSpace.IsCoherent X.toRingedSpace (K : X.Modules) ∧
      (∀ (i : I) (W : X.Opens) (hi : W ≤ U i),
        Set.range (K.arrow.app W) =
          Set.range ((affineSectionSubmodule X F (U i) (N i) (hN i)).2.val.app
            (op (Over.mk (homOfLE hi))))) ∧
      (∀ i, LinearMap.range (K.arrow.val.app (op (U i))).hom = N i) ∧
      (∀ i, Nonempty (Γ((cokernel K.arrow : X.Modules), U i) ≃ₗ[Γ(X, U i)]
        (Γ(F, U i) ⧸ N i))) := by
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  let Q (i : I) := affineSectionSubmodule X F (U i) (N i) (hN i)
  have hQ (i : I) := affine_local_realization X F (U i) (hU i) (N i) (hN i)
  obtain ⟨K, hK, huniq⟩ := coherent_submodule_gluing X F hF I U hU hcover N
    (fun i ↦ (Q i).1) (fun i ↦ (Q i).2) (fun i ↦ (hQ i).1)
    (fun i ↦ (hQ i).2.1) (fun i ↦ (hQ i).2.2) hcompat
  refine ⟨K, ⟨hK.1, hK.2.1, ?_, hK.2.2⟩, ?_⟩
  · intro i
    ext s
    exact Set.ext_iff.mp (hK.2.1 i (U i) le_rfl) s |>.trans (by
      have hid : homOfLE (le_rfl : U i ≤ U i) = 𝟙 (U i) := Subsingleton.elim _ _
      change s ∈ LinearMap.range ((Q i).2.val.app
        (op (Over.mk (homOfLE le_rfl)))).hom ↔ s ∈ N i
      rw [hid, (hQ i).2.2])
  · intro L hL
    exact huniq L ⟨hL.1, hL.2.1, hL.2.2.2⟩

end AlgebraicGeometry.Scheme.Modules
