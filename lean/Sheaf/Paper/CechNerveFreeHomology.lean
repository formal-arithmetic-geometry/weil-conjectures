/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Free-module homology of a Čech nerve

Source: Stacks Project, Hypercoverings, Lemma 01GC (lemma-compare-cosk0),
with the same contraction over a commutative ring instead of ℤ
(blueprint: lem-weil-pbc-cech-nerve-free-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem locally_surjective_hom_ext
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (hf : Presheaf.IsLocallySurjective J f)
    {T : Cᵒᵖ ⥤ Type u} (hT : Presheaf.IsSheaf J T)
    (g h : Q ⟶ T) (heq : f ≫ g = f ≫ h) : g = h := by
  have := hf
  ext X x
  apply (((isSheaf_iff_isSheaf_of_type J T).1 hT).isSeparated _
    (Presheaf.imageSieve_mem J f x)).ext
  rintro Y i ⟨y, hy⟩
  dsimp
  rw [← NatTrans.naturality_apply g i.op x,
    ← NatTrans.naturality_apply h i.op x, ← hy]
  exact ConcreteCategory.congr_hom (congr_app heq (Opposite.op Y)) y

private theorem free_sheaf_map_epi
    {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} R)] {P Q : Cᵒᵖ ⥤ Type u}
    (f : P ⟶ Q) (hf : Presheaf.IsLocallySurjective J f) :
    Epi (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
      presheafToSheaf J (ModuleCat R)).map f) := by
  let adj := ((ModuleCat.adj R).whiskerRight Cᵒᵖ).comp
    (sheafificationAdjunction J (ModuleCat R))
  refine ⟨?_⟩
  intro T g h heq
  apply (adj.homEquiv Q T).injective
  refine locally_surjective_hom_ext f hf ?_ _ _ ?_
  · exact (Presheaf.isSheaf_iff_isSheaf_forget J T.obj (forget (ModuleCat R))).1 T.property
  · simpa only [adj.homEquiv_naturality_left] using
      congrArg (adj.homEquiv P T) heq

set_option backward.isDefEq.respectTransparency false in
private theorem extraDegeneracy_exact
    {R : Type u} [CommRing R]
    {X : SimplicialObject.Augmented (ModuleCat.{u} R)}
    (ed : X.ExtraDegeneracy)
    (hz : ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0 ≫
      X.hom.app (Opposite.op (SimplexCategory.mk 0)) = 0) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0)
      (X.hom.app (Opposite.op (SimplexCategory.mk 0))) hz).Exact := by
  have hc : ed.s 0 ≫
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0 =
      𝟙 _ - X.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫ ed.s' := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, ed.s₀_comp_δ₁, sub_eq_add_neg]
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  change ↑(X.left.obj (Opposite.op (SimplexCategory.mk 0))) at x
  change X.hom.app (Opposite.op (SimplexCategory.mk 0)) x = 0 at hx
  refine ⟨ed.s 0 x, ?_⟩
  have h := ConcreteCategory.congr_hom hc x
  change ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0
    (ed.s 0 x) = x - ed.s' (X.hom.app (Opposite.op (SimplexCategory.mk 0)) x) at h
  simpa only [hx, map_zero, sub_zero] using h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMonoIso
    {D : Type*} [Category D] [HasFiniteLimits D]
    (f : Arrow D) {Z : D} (g : f.right ⟶ Z) [Mono g] :
    f.cechNerve ≅ (Arrow.mk (f.hom ≫ g)).cechNerve := by
  let h := f.hom ≫ g
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · refine
      { hom := WidePullback.lift
          (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom) ≫ g)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f.hom) j)
          (by intro j; simp)
        inv := WidePullback.lift
          (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) 0 ≫ f.hom)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) j)
          (by intro j; apply (cancel_mono g).1; simp [h, Category.assoc])
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply WidePullback.hom_ext
      · intro j; simp [h, Category.assoc]
      · simp [h, Category.assoc]
    · apply WidePullback.hom_ext <;> simp [Category.assoc, h]
  · intro n m α
    apply WidePullback.hom_ext <;> simp [Arrow.cechNerve, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMapIso
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D] [HasFiniteLimits E]
    (F : D ⥤ E) [PreservesFiniteLimits F] (f : Arrow D) :
    f.cechNerve ⋙ F ≅ (Arrow.mk (F.map f.hom)).cechNerve := by
  let L (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan f.right (fun _ : Fin (n.unop.len + 1) ↦ f.left)
      (fun _ ↦ f.hom)
  let R (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan (F.obj f.right)
      (fun _ : Fin (n.unop.len + 1) ↦ F.obj f.left) (fun _ ↦ F.map f.hom)
  let eD (n : SimplexCategoryᵒᵖ) : L n ⋙ F ≅ R n :=
    NatIso.ofComponents (fun j ↦ match j with
      | none => Iso.refl _
      | some _ => Iso.refl _)
      (by intro j k α; cases α with
          | id j =>
              change F.map ((L n).map (𝟙 j)) ≫ _ = _ ≫ (R n).map (𝟙 j)
              rw [(L n).map_id, (R n).map_id, F.map_id]
              simp
          | term j => simp [L, R])
  let e (n : SimplexCategoryᵒᵖ) : F.obj (limit (L n)) ≅ limit (R n) :=
    preservesLimitIso F (L n) ≪≫ HasLimit.isoOfNatIso (eD n)
  have hπ (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
      (e n).hom ≫ WidePullback.π (fun _ ↦ F.map f.hom) j =
        F.map (WidePullback.π (fun _ ↦ f.hom) j) := by
    change (e n).hom ≫ limit.π (R n) (some j) = F.map (limit.π (L n) (some j))
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  have hb (n : SimplexCategoryᵒᵖ) :
      (e n).hom ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f.hom) =
        F.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom)) := by
    change (e n).hom ≫ limit.π (R n) none = F.map (limit.π (L n) none)
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  refine NatIso.ofComponents e ?_
  intro n m α
  apply WidePullback.hom_ext
  · intro j
    dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hπ]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hπ]
  · dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hb]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hb]


set_option backward.isDefEq.respectTransparency false in
private theorem type_augmentation_exact
    {R : Type u} [CommRing R] (f : Arrow (Type u)) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (f.cechNerve ⋙ (ModuleCat.free R))).d 1 0)
      ((ModuleCat.free R).map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))
      (by
        dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
        rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
        simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve,
          ← (ModuleCat.free R).map_comp])).Exact := by
  classical
  let I : Type u := Set.range f.hom
  let p : f.left ⟶ I := ↾fun a ↦ ⟨f.hom a, ⟨a, rfl⟩⟩
  let j : I ⟶ f.right := ↾fun b ↦ b.1
  have hj : Mono j := (mono_iff_injective _).2 Subtype.val_injective
  have hp : Function.Surjective p := by
    rintro ⟨b, a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  let S : SplitEpi p := { section_ := ↾s, id := by ext b; exact congrArg Subtype.val (hs b) }
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk p) S).map
    (ModuleCat.free R)
  have hz (g : Arrow (Type u)) (H : Type u ⥤ ModuleCat.{u} (R)) :
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj (g.cechNerve ⋙ H)).d 1 0 ≫
        H.map (WidePullback.base (fun _ : Fin 1 ↦ g.hom)) = 0 := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← H.map_comp]
  have hex := extraDegeneracy_exact ed (by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, SimplicialObject.const])
  have hex' : (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        ((Arrow.mk p).cechNerve ⋙ (ModuleCat.free R))).d 1 0)
      ((ModuleCat.free R).map (WidePullback.base (fun _ : Fin 1 ↦ p)))
      (hz (Arrow.mk p) (ModuleCat.free R))).Exact := by
    simpa only [SimplicialObject.Augmented.whiskering,
      SimplicialObject.Augmented.whiskeringObj, SimplicialObject.Augmented.drop,
      SimplicialObject.Augmented.point, Comma.fst, Comma.snd,
      SimplicialObject.whiskering, Functor.whiskeringRight_obj_obj,
      Arrow.augmentedCechNerve, Arrow.mk, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.constComp_hom_app, Category.comp_id] using hex
  let e := nerveMonoIso (Arrow.mk p) j
  change (Arrow.mk p).cechNerve ≅ f.cechNerve at e
  have hb : e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
      WidePullback.base (fun _ : Fin 1 ↦ f.hom) =
      WidePullback.base (fun _ : Fin 1 ↦ p) ≫ j := by
    change e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
      WidePullback.base (fun _ : Fin 1 ↦ p ≫ j) = _
    simp [e, nerveMonoIso]
  let eFree := (SimplicialObject.whiskering _ _).obj (ModuleCat.free R) |>.mapIso e
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  let φ : ShortComplex.mk _ _ (hz (Arrow.mk p) (ModuleCat.free R)) ⟶
      ShortComplex.mk _ _ (hz f (ModuleCat.free R)) :=
    { τ₁ := eP.hom.f 1
      τ₂ := eP.hom.f 0
      τ₃ := (ModuleCat.free R).map j
      comm₁₂ := eP.hom.comm 1 0
      comm₂₃ := by
        dsimp [eP, eFree, SimplicialObject.whiskering,
          Functor.whiskeringRight, Functor.whiskerRight]
        simp only [← (ModuleCat.free R).map_comp]
        change (ModuleCat.free R).map (e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
          WidePullback.base (fun _ : Fin 1 ↦ f.hom)) = _
        exact congrArg (ModuleCat.free R).map hb }
  have : Mono ((ModuleCat.free R).map j) := by
    apply (ModuleCat.mono_iff_injective _).2
    exact Finsupp.mapDomain_injective Subtype.val_injective
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex'

set_option backward.isDefEq.respectTransparency false in
private theorem presheaf_augmentation_exact
    {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] (f : Arrow (Cᵒᵖ ⥤ Type u)) :
    let F := (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)).d 1 0)
      (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))
      (by
        dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
        rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
        simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← F.map_comp])).Exact := by
  let F := (Functor.whiskeringRight Cᵒᵖ (Type u) (ModuleCat R)).obj (ModuleCat.free R)
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  have hz (g : Arrow (Cᵒᵖ ⥤ Type u)) (H : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} R)) :
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj (g.cechNerve ⋙ H)).d 1 0 ≫
        H.map (WidePullback.base (fun _ : Fin 1 ↦ g.hom)) = 0 := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← H.map_comp]
  have hzType (g : Arrow (Type u)) (H : Type u ⥤ ModuleCat.{u} R) :
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj (g.cechNerve ⋙ H)).d 1 0 ≫
        H.map (WidePullback.base (fun _ : Fin 1 ↦ g.hom)) = 0 := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← H.map_comp]
  let S := ShortComplex.mk (P.d 1 0)
    (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))) (hz f F)
  let E := fun X ↦ (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X
  have hjoint : JointlyFaithful E := ⟨by
    intro P Q α β h
    apply NatTrans.ext
    funext X
    exact h X⟩
  apply hjoint.jointlyReflectsIsomorphisms.exact_iff S |>.2
  intro X
  let V := (evaluation Cᵒᵖ (Type u)).obj X
  let q := Arrow.mk (f.hom.app X)
  let eN := nerveMapIso V f
  let eFree := (SimplicialObject.whiskering _ _).obj (ModuleCat.free R) |>.mapIso eN
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  have hbase : eN.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
      WidePullback.base (fun _ : Fin 1 ↦ V.map f.hom) =
      V.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)) := by
    dsimp [eN, q, nerveMapIso]
    simp [Category.assoc, HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π]
  let φ : S.map (E X) ⟶
      ShortComplex.mk _ _ (hzType q (ModuleCat.free R)) :=
    { τ₁ := eP.hom.f 1
      τ₂ := eP.hom.f 0
      τ₃ := 𝟙 _
      comm₁₂ := by
        have hd : (E X).map (P.d 1 0) =
            ((AlgebraicTopology.alternatingFaceMapComplex _).obj
              ((f.cechNerve ⋙ V) ⋙ (ModuleCat.free R))).d 1 0 := by
          simp only [P, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
            AlgebraicTopology.AlternatingFaceMapComplex.objD,
            Functor.map_sum, Functor.map_zsmul]
          rfl
        change eP.hom.f 1 ≫ _ = (E X).map (P.d 1 0) ≫ eP.hom.f 0
        rw [hd]
        exact eP.hom.comm 1 0
      comm₂₃ := by
        dsimp [S, F, E, eP, eFree, SimplicialObject.whiskering,
          Functor.whiskeringRight, Functor.whiskerRight]
        simp only [Category.comp_id, ← (ModuleCat.free R).map_comp]
        exact congrArg (ModuleCat.free R).map hbase }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (type_augmentation_exact q)

private theorem presheafCechSheaf_augmentation_exact
    {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} R)] (f : Arrow (Cᵒᵖ ⥤ Type u))
    (hf : Presheaf.IsLocallySurjective J f.hom) :
  let F := (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
    presheafToSheaf J (ModuleCat R)
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let ε := F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))
  ∃ hz : A.d 1 0 ≫ ε = 0,
    (ShortComplex.mk (A.d 1 0) ε hz).Exact ∧ Epi ε := by
  dsimp only
  let F := (Functor.whiskeringRight Cᵒᵖ (Type u) (ModuleCat R)).obj (ModuleCat.free R)
  let G := presheafToSheaf J (ModuleCat.{u} R)
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  have hz0 (g : Arrow (Cᵒᵖ ⥤ Type u)) (H : (Cᵒᵖ ⥤ Type u) ⥤ Sheaf J (ModuleCat.{u} R)) :
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj (g.cechNerve ⋙ H)).d 1 0 ≫
        H.map (WidePullback.base (fun _ : Fin 1 ↦ g.hom)) = 0 := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← H.map_comp]
  let hz := hz0 f (F ⋙ G)
  refine ⟨hz, ?_, ?_⟩
  · have hex := (presheaf_augmentation_exact f).map G
    have hd : G.map (P.d 1 0) =
        ((AlgebraicTopology.alternatingFaceMapComplex _).obj
          (f.cechNerve ⋙ (F ⋙ G))).d 1 0 := by
      simp only [P, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        Functor.map_sum, Functor.map_zsmul]
      rfl
    change (ShortComplex.mk (G.map (P.d 1 0))
      (G.map (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))) _).Exact at hex
    simpa only [hd, P, F, G, AlgebraicTopology.alternatingFaceMapComplex_obj_X,
      Functor.comp_obj, Functor.comp_map] using hex
  · have := hf
    let π := WidePullback.π (fun _ : Fin 1 ↦ f.hom) 0
    have hπ : Presheaf.IsLocallySurjective J π := by
      apply Presheaf.isLocallySurjective_of_surjective
      intro X x
      let s : f.left ⟶ f.cechNerve.obj (Opposite.op (SimplexCategory.mk 0)) :=
        WidePullback.lift f.hom (fun _ : Fin 1 ↦ 𝟙 f.left) (by simp)
      refine ⟨s.app X x, ?_⟩
      have h : s ≫ π = 𝟙 f.left := by simp [s, π]
      exact ConcreteCategory.congr_hom (congr_app h X) x
    have hb : π ≫ f.hom = WidePullback.base (fun _ : Fin 1 ↦ f.hom) := by
      simp [π]
    have hbase : Presheaf.IsLocallySurjective J
        (WidePullback.base (fun _ : Fin 1 ↦ f.hom)) := by
      rw [← hb]
      infer_instance
    exact free_sheaf_map_epi _ hbase


private theorem type_nerve_positive_exact
    {R : Type u} [CommRing R] (f : Arrow (Type u)) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (f.cechNerve ⋙ (ModuleCat.free R))).ExactAt (n + 1) := by
  classical
  let I : Type u := Set.range f.hom
  let p : f.left ⟶ I := ↾fun a ↦ ⟨f.hom a, ⟨a, rfl⟩⟩
  let j : I ⟶ f.right := ↾fun b ↦ b.1
  have hj : Mono j := (mono_iff_injective _).2 Subtype.val_injective
  have hp : Function.Surjective p := by
    rintro ⟨b, a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  let S : SplitEpi p := { section_ := ↾s, id := by ext b; exact congrArg Subtype.val (hs b) }
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk p) S).map
    (ModuleCat.free R)
  let he := ed.homotopyEquiv
  have hsingle : ((ChainComplex.single₀ (ModuleCat R)).obj
      ((ModuleCat.free R).obj I)).ExactAt (n + 1) := by
    apply HomologicalComplex.ExactAt.of_isZero
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hx : ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      ((Arrow.mk p).cechNerve ⋙ (ModuleCat.free R))).ExactAt (n + 1) := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    exact (he.toHomologyIso (n + 1)).isZero_iff.2
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hsingle)
  let e := nerveMonoIso (Arrow.mk p) j
  have hfac : p ≫ j = f.hom := by ext a; rfl
  have hf : Arrow.mk (p ≫ j) = f := by cases f; simp_all
  change (Arrow.mk p).cechNerve ≅ (Arrow.mk (p ≫ j)).cechNerve at e
  rw [hf] at e
  exact hx.of_iso
    ((AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      ((SimplicialObject.whiskering _ _).obj (ModuleCat.free R) |>.mapIso e))

private theorem presheaf_nerve_positive_exact
    {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] (f : Arrow (Cᵒᵖ ⥤ Type u)) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R))).ExactAt
        (n + 1) := by
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R))
  let E := fun X ↦ (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj X
  have hjoint : JointlyFaithful E := ⟨by
    intro P Q α β h
    apply NatTrans.ext
    funext X
    exact h X⟩
  apply hjoint.jointlyReflectsIsomorphisms.exact_iff _ |>.2
  intro X
  let V := (evaluation Cᵒᵖ (Type u)).obj X
  let q := Arrow.mk (f.hom.app X)
  let eN := nerveMapIso V f
  let eFree := (SimplicialObject.whiskering _ _).obj (ModuleCat.free R) |>.mapIso eN
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  have h := type_nerve_positive_exact (R := R) q n
  have h' := h.of_iso eP.symm
  change (((AlgebraicTopology.alternatingFaceMapComplex _) ⋙
    (E X).mapHomologicalComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R))).ExactAt
      (n + 1)
  rw [AlgebraicTopology.map_alternatingFaceMapComplex]
  exact h'

private theorem presheafCechSheaf_positive_exact
    {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u} R)] (f : Arrow (Cᵒᵖ ⥤ Type u)) :
  let F := (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
    presheafToSheaf J (ModuleCat R)
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  ∀ n : ℕ, A.ExactAt (n + 1) := by
  dsimp only
  intro n
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R))
  let F := presheafToSheaf J (ModuleCat.{u} R)
  have hpre : P.ExactAt (n + 1) := presheaf_nerve_positive_exact f n
  have hmap := hpre.map F
  change (((AlgebraicTopology.alternatingFaceMapComplex _) ⋙
    F.mapHomologicalComplex _).obj
    (f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R))).ExactAt
      (n + 1) at hmap
  rw [AlgebraicTopology.map_alternatingFaceMapComplex] at hmap
  exact hmap


set_option backward.isDefEq.respectTransparency false in
/-- The sheafified free-module Čech nerve of a presheaf map surjective after
sheafification has zero positive homology; its canonical augmentation induces an
isomorphism on degree-zero homology to the free-module sheaf on the target.

Source: Stacks Project, Hypercoverings, Lemma 01GC (lemma-compare-cosk0),
lines 590--660, with free R-modules in place of free abelian groups.
(blueprint: lem-weil-pbc-cech-nerve-free-homology).

Proof:
1. Mathlib's local-surjectivity criterion for sheafification gives local surjectivity
   of the original presheaf map.
2. Objectwise, factor a set map through its image. The wide-pullback universal
   property identifies its nerve with the nerve of the surjection onto that image.
   Choose a section of this surjection. Its extra degeneracy, mapped by the free
   R-module functor, contracts the augmented nerve. The image inclusion induces a
   monomorphism of free R-modules, so exactness at the augmentation is retained.
   The same contraction gives exactness in all positive degrees.
3. Evaluation preserves finite limits and homology, and the evaluation functors
   jointly detect exactness. Their finite-limit comparison identifies evaluated
   presheaf nerves with the nerves of evaluated set maps. Hence the presheaf
   complex is exact in positive degrees and at its augmentation.
4. Additive exact sheafification preserves this exactness and commutes with the
   alternating-face complex. The sheafified free-module functor is left adjoint
   to the underlying-set presheaf functor. Maps into a sheaf agree if they agree
   after a locally surjective presheaf map, so the augmentation is epic.
5. The degree-zero quasi-isomorphism criterion for short complexes turns the
   exact, epic augmentation into the claimed isomorphism on H₀. Its map is
   Mathlib's canonical alternating-face augmentation, by the degree-zero formula.
-/
theorem freeModule_cechNerve_homology
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Type (u)) [CommRing R]
    (f : Arrow (Cᵒᵖ ⥤ Type (u)))
    (hsurj : Sheaf.IsLocallySurjective
      ((presheafToSheaf J.toGrothendieck (Type (u))).map f.hom)) :
    (∀ i : ℕ, 0 < i → IsZero
      (((AlgebraicTopology.alternatingFaceMapComplex
        (Sheaf J.toGrothendieck (ModuleCat.{u} R))).obj
          (f.cechNerve ⋙
            (Functor.whiskeringRight Cᵒᵖ (Type (u)) (ModuleCat.{u} R)).obj
              (ModuleCat.free R) ⋙
            presheafToSheaf J.toGrothendieck (ModuleCat.{u} R))).homology i)) ∧
    IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        ((SimplicialObject.Augmented.whiskeringObj _ _
          ((Functor.whiskeringRight Cᵒᵖ (Type (u)) (ModuleCat.{u} R)).obj
            (ModuleCat.free R) ⋙
            presheafToSheaf J.toGrothendieck (ModuleCat.{u} R))).obj
          f.augmentedCechNerve)) 0) := by
  let F := (Functor.whiskeringRight Cᵒᵖ (Type u) (ModuleCat R)).obj
    (ModuleCat.free R) ⋙ presheafToSheaf J.toGrothendieck (ModuleCat R)
  let X := ((SimplicialObject.Augmented.whiskeringObj _ _ F).obj
    f.augmentedCechNerve)
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let ε := AlgebraicTopology.AlternatingFaceMapComplex.ε.app X
  have hlocal :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J.toGrothendieck f.hom).1 hsurj
  obtain ⟨hz, hex, hepi⟩ := presheafCechSheaf_augmentation_exact (R := R) f hlocal
  constructor
  · intro i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (presheafCechSheaf_positive_exact (R := R) J.toGrothendieck f n)
  · change IsIso (HomologicalComplex.homologyMap ε 0)
    apply (quasiIsoAt_iff_isIso_homologyMap ε 0).1
    rw [quasiIsoAt_iff' ε 1 0 0 (by simp) (by simp)]
    apply (ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)).2
    change (ShortComplex.mk (A.d 1 0) (ε.f 0) _).Exact ∧ Epi (ε.f 0)
    have hε : ε.f 0 = F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)) := by
      simp [ε, X, SimplicialObject.Augmented.whiskeringObj,
        Arrow.augmentedCechNerve]
    constructor
    · simpa only [hε] using hex
    · simpa only [hε] using hepi

end CategoryTheory
