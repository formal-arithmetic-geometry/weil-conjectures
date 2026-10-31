/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteIntersectionLimitCompatibility
public import WeilConjectures.AlgebraicGeometry.CoverCech
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # The first finite-cover Čech limit

Source: Stacks Project, Tag 099U (`lemma-affine-vanishing`), first Čech-colimit
calculation, and Tag 099S (`lemma-limit-pullback`)
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit).

The stage families are precisely the coordinate-reindexed presentations over `U`.
Their objects need only be ind-étale over `X`. The maps below are characterized by
restriction on every ordered tuple, including repeated indices. Colimit comparisons
are stated using `colimit.desc`, so their directions and their legs are specified.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The underlying abelian presheaf of the actual module inverse image `ν_X^* F`,
restricted to the affine ind-étale basis. Source: Stacks 099U, first-limit calculation
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
noncomputable def firstLimitClassicalPresheaf (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    X.AffineProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (toProEt X).op ⋙ ((ProEtale.finiteCoefficientComparison X Λ).obj F).val.presheaf

/-- Bundle the simultaneous first-limit stage as an object of the original basis.
Source: Stacks 099U, the family indexed by the product of directed sets
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisStage {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (j : ∀ a, J a) (a : Fin m) : X.AffineProEt :=
  mk (((firstLimitCoordinate D a).obj (op j)).hom ≫ U.hom) (hD a (op (j a)))

/-- The stage covering arrow is its given structure map to `U`.
Source: Stacks 099U, first-limit stage covering
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisArrow {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (j : ∀ a, J a) (a : Fin m) : firstLimitBasisStage U D hD j a ⟶ U :=
  MorphismProperty.Over.homMk ((firstLimitCoordinate D a).obj (op j)).hom rfl trivial

/-- The transition is the coordinate transition of the given inverse system.
Source: Stacks 099U, first-limit directed system
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisTransition {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    {i j : ∀ a, J a} (h : i ⟶ j) (a : Fin m) :
    firstLimitBasisStage U D hD j a ⟶ firstLimitBasisStage U D hD i a :=
  MorphismProperty.Over.homMk ((firstLimitCoordinate D a).map h.op).left
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ U.hom) (Over.w ((firstLimitCoordinate D a).map h.op))))
    trivial

/-- The original member maps to its chosen stage by the supplied presentation cone.
Source: Stacks 099U, first-limit restriction maps
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit). -/
def firstLimitBasisProjection {X : Scheme.{u}} (U : X.AffineProEt) {m : ℕ}
    (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    {J : Fin m → Type u} [∀ a, Preorder (J a)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a)
    (j : ∀ a, J a) (a : Fin m) : V a ⟶ firstLimitBasisStage U D hD j a :=
  MorphismProperty.Over.homMk ((q a).app (op (j a))).left
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ U.hom) (Over.w ((q a).app (op (j a)))))).trans
        (MorphismProperty.Over.w (f a))) trivial

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cech_ext {C : Type*} [Category C] {T : Type*} {U : C}
    {V : T → C} {f : ∀ a, V a ⟶ U} (S : SiteCechComplex V f)
    {p : ℕ} {α : Fin (p + 1) → T} {Z : C} (a b : Z ⟶ S.W p α)
    (h : ∀ r, a ≫ S.pr p α r = b ≫ S.pr p α r) : a = b := by
  obtain ⟨c, _, hc⟩ := S.universal p α Z (fun r ↦ b ≫ S.pr p α r)
    (fun r ↦ by simp only [Category.assoc, S.comm])
  exact (hc a h).trans (hc b (fun _ ↦ rfl)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechMap {C : Type*} [Category C] {T : Type*} {U : C}
    {V W : T → C} {f : ∀ a, V a ⟶ U} {g : ∀ a, W a ⟶ U}
    (S : SiteCechComplex V f) (R : SiteCechComplex W g)
    (a : ∀ t, W t ⟶ V t) (ha : ∀ t, a t ≫ f t = g t)
    (p : ℕ) (α : Fin (p + 1) → T) : R.W p α ⟶ S.W p α :=
  (S.universal p α (R.W p α) (fun r ↦ R.pr p α r ≫ a (α r))
    (fun r ↦ by simp only [Category.assoc, ha, R.comm])).choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cechMap_pr {C : Type*} [Category C] {T : Type*} {U : C}
    {V W : T → C} {f : ∀ a, V a ⟶ U} {g : ∀ a, W a ⟶ U}
    (S : SiteCechComplex V f) (R : SiteCechComplex W g)
    (a : ∀ t, W t ⟶ V t) (ha : ∀ t, a t ≫ f t = g t)
    (p : ℕ) (α : Fin (p + 1) → T) (r : Fin (p + 1)) :
    cechMap S R a ha p α ≫ S.pr p α r = R.pr p α r ≫ a (α r) :=
  (S.universal p α (R.W p α) (fun r ↦ R.pr p α r ≫ a (α r))
    (fun r ↦ by simp only [Category.assoc, ha, R.comm])).choose_spec.1 r

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechComplexMap {C : Type*} [Category C] {T : Type}
    {U : C} {V W : T → C} {f : ∀ a, V a ⟶ U} {g : ∀ a, W a ⟶ U}
    (S : SiteCechComplex V f) (R : SiteCechComplex W g)
    (a : ∀ t, W t ⟶ V t) (ha : ∀ t, a t ≫ f t = g t)
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : S.complex M ⟶ R.complex M := by
  let c (p : ℕ) : S.cochains M p ⟶ R.cochains M p := AddCommGrpCat.ofHom
    { toFun := fun s α ↦ M.map (cechMap S R a ha p α).op (s α)
      map_zero' := by funext α; exact map_zero _
      map_add' := by intros; funext α; exact map_add _ _ _ }
  refine CochainComplex.ofHom c (fun p ↦ ?_)
  simp only [SiteCechComplex.complex, CochainComplex.of_d]
  apply AddCommGrpCat.ext
  intro s
  funext α
  change (∑ r : Fin (p + 2), (-1 : ℤ) ^ r.val •
      M.map (R.indexMap α r.succAbove).op
        (M.map (cechMap S R a ha p (α ∘ r.succAbove)).op
          (s (α ∘ r.succAbove)))) =
    M.map (cechMap S R a ha (p + 1) α).op
      (∑ r : Fin (p + 2), (-1 : ℤ) ^ r.val •
        M.map (S.indexMap α r.succAbove).op (s (α ∘ r.succAbove)))
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have h : R.indexMap α r.succAbove ≫ cechMap S R a ha p (α ∘ r.succAbove) =
      cechMap S R a ha (p + 1) α ≫ S.indexMap α r.succAbove := by
    apply cech_ext S
    intro k
    rw [Category.assoc, cechMap_pr, ← Category.assoc, R.indexMap_pr,
      Category.assoc, S.indexMap_pr, cechMap_pr]
    rfl
  simp only [← AddCommGrpCat.comp_apply, ← M.map_comp, ← op_comp, h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechDiagram {C K : Type*} [Category C] [Category K]
    {T : Type*} {U : C} (A : T → K ⥤ C)
    (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (p : ℕ) (α : Fin (p + 1) → T) : K ⥤ C where
  obj k := (R k).W p α
  map {i j} h := cechMap (R j) (R i) (fun t ↦ (A t).map h) (hg h) p α
  map_id i := by
    apply cech_ext (R i)
    intro r
    rw [cechMap_pr, (A (α r)).map_id]
    simp
  map_comp h k := by
    apply cech_ext (R _)
    intro r
    simp only [Category.assoc, cechMap_pr, (A (α r)).map_comp]
    rw [← Category.assoc (cechMap _ _ _ _ _ _), cechMap_pr, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechCone {C K : Type*} [Category C] [Category K]
    {T : Type*} {U : C} {V : T → C} {f : ∀ t, V t ⟶ U}
    (S : SiteCechComplex V f) (A : T → K ⥤ C)
    (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (q : ∀ t, (Functor.const K).obj (V t) ⟶ A t)
    (hf : ∀ t k, (q t).app k ≫ g k t = f t)
    (p : ℕ) (α : Fin (p + 1) → T) : Cone (cechDiagram A g hg R p α) where
  pt := S.W p α
  π :=
    { app k := cechMap (R k) S (fun t ↦ (q t).app k)
        (fun t ↦ hf t k) p α
      naturality {i j} h := by
        simp only [Functor.const_obj_map]
        apply cech_ext (R j)
        intro r
        dsimp only [cechDiagram]
        simp only [Category.assoc, cechMap_pr]
        rw [← Category.assoc (cechMap _ _ _ _ _ _), cechMap_pr]
        erw [Category.id_comp]
        change S.pr p α r ≫ (q (α r)).app j =
          (S.pr p α r ≫ (q (α r)).app i) ≫ (A (α r)).map h
        rw [Category.assoc, ← (q (α r)).naturality h]
        simp only [Functor.const_obj_map]
        erw [Category.id_comp] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechConeIsLimit {C K : Type*} [Category C] [Category K]
    [Nonempty K] {T : Type*} {U : C} {V : T → C} {f : ∀ t, V t ⟶ U}
    (S : SiteCechComplex V f) (A : T → K ⥤ C)
    (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (q : ∀ t, (Functor.const K).obj (V t) ⟶ A t)
    (hf : ∀ t k, (q t).app k ≫ g k t = f t)
    (hl : ∀ t, IsLimit (Cone.mk (V t) (q t))) (p : ℕ) (α : Fin (p + 1) → T) :
    IsLimit (cechCone S A g hg R q hf p α) := by
  classical
  let cone (s : Cone (cechDiagram A g hg R p α)) (r : Fin (p + 1)) :
      Cone (A (α r)) :=
    { pt := s.pt
      π :=
        { app k := s.π.app k ≫ (R k).pr p α r
          naturality {i j} h := by
            simp only [Functor.const_obj_map]
            rw [← s.w h]
            simp only [Category.assoc]
            dsimp only [cechDiagram]
            simp only [cechMap_pr]
            exact Category.id_comp _ } }
  let a (s : Cone (cechDiagram A g hg R p α)) (r : Fin (p + 1)) : s.pt ⟶ V (α r) :=
    (hl (α r)).lift (cone s r)
  have ha (s) (r) (k) : a s r ≫ (q (α r)).app k =
      s.π.app k ≫ (R k).pr p α r := by
    dsimp only [a]
    exact (hl (α r)).fac (cone s r) k
  have haf (s) (r) : a s r ≫ f (α r) = a s 0 ≫ f (α 0) := by
    let k : K := Classical.choice inferInstance
    rw [← hf (α r) k, ← hf (α 0) k, ← Category.assoc, ← Category.assoc,
      ha s r k, ha s 0 k, Category.assoc, Category.assoc, (R k).comm]
  let b (s) := (S.universal p α s.pt (a s) (haf s)).choose
  have hb (s) (r) : b s ≫ S.pr p α r = a s r :=
    (S.universal p α s.pt (a s) (haf s)).choose_spec.1 r
  refine
    { lift := b
      fac := ?_
      uniq := ?_ }
  · intro s k
    apply cech_ext (R k)
    intro r
    dsimp only [cechCone]
    rw [Category.assoc, cechMap_pr, ← Category.assoc, hb]
    exact ha s r k
  · intro s l h
    apply cech_ext S
    intro r
    rw [hb]
    apply (hl (α r)).hom_ext
    intro k
    change (l ≫ S.pr p α r) ≫ (q (α r)).app k = a s r ≫ (q (α r)).app k
    rw [ha]
    have hh := congrArg (fun z ↦ z ≫ (R k).pr p α r) (h k)
    dsimp only [cechCone] at hh
    simpa only [Category.assoc, cechMap_pr] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem moduleContinuous (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((toProEt X).op ⋙ ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj) := by
  let M := ModuleCat.{u + 1} Λ
  let U := CategoryTheory.forget M
  have : U.PreservesLeftKanExtensions (Scheme.toProEt X).op := by
    intro P
    have : PreservesFilteredColimitsOfSize.{u, u + 1} U :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    have : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        U P (Scheme.toProEt X).op V := by intro V; infer_instance
    infer_instance
  let e := (sheafPullbackForgetIso X.smallEtaleTopology (ProEt.topology X)
    (Scheme.toProEt X) U).app F
  let G := (sheafCompose X.smallEtaleTopology U).obj F
  have := Scheme.proEtaleComparisonSets_continuous X G
  let H := (toProEt X).op ⋙
    ((ProEtale.comparisonUpperStar M X).obj F).obj
  let e' : H ⋙ U ≅ (toProEt X).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj G).obj :=
    Functor.isoWhiskerLeft (toProEt X).op
      ((sheafToPresheaf (ProEt.topology X) (Type (u + 1))).mapIso e)
  have : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  constructor
  intro K _ _
  have : PreservesColimitsOfShape K (H ⋙ U) :=
    preservesColimitsOfShape_of_natIso e'.symm
  have : ReflectsColimitsOfShape K U := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves H U

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem classicalContinuous (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    PreservesFilteredColimitsOfSize.{u, u} (firstLimitClassicalPresheaf X Λ F) := by
  let H := ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F)
  let P := H.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let η : P ⟶ ((ProEtale.finiteCoefficientComparison X Λ).obj F).val.presheaf :=
    toSheafify (ProEt.topology X) P
  have : IsIso η := by
    change IsIso (toSheafify (ProEt.topology X) P)
    exact isIso_toSheafify _
      (((sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj H).property)
  have : PreservesFilteredColimitsOfSize.{u, u} ((toProEt X).op ⋙ H.obj) :=
    moduleContinuous X Λ F
  constructor
  intro K _ _
  have : PreservesColimitsOfShape K ((toProEt X).op ⋙ P) := by
    change PreservesColimitsOfShape K
      (((toProEt X).op ⋙ H.obj) ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    infer_instance
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft (toProEt X).op (asIso η))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechComplexDiagram {C : Type*} [Category C]
    {K : Type u} [SmallCategory K] {T : Type} {U : C}
    (A : T → Kᵒᵖ ⥤ C) (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : K ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ where
  obj k := (R (op k)).complex M
  map h := cechComplexMap (R _) (R _) (fun t ↦ (A t).map h.op) (hg h.op) M
  map_id k := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.ext
    intro s
    funext α
    change M.map (cechMap _ _ _ _ _ _).op (s α) = s α
    have hi : cechMap (R (op k)) (R (op k))
        (fun t ↦ (A t).map (𝟙 k).op) (hg (𝟙 k).op) p α = 𝟙 _ := by
      apply cech_ext (R (op k))
      intro r
      rw [cechMap_pr]
      change _ ≫ (A (α r)).map (𝟙 _) = _
      rw [(A (α r)).map_id, Category.comp_id, Category.id_comp]
    rw [hi]
    simp
  map_comp h k := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.ext
    intro s
    funext α
    change M.map (cechMap _ _ _ _ _ _).op (s α) =
      M.map (cechMap _ _ _ _ _ _).op (M.map (cechMap _ _ _ _ _ _).op (s α))
    have hi : cechMap (R _) (R _) (fun t ↦ (A t).map (h ≫ k).op) (hg _) p α =
        cechMap (R _) (R _) (fun t ↦ (A t).map k.op) (hg _) p α ≫
          cechMap (R _) (R _) (fun t ↦ (A t).map h.op) (hg _) p α := by
      apply cech_ext (R _)
      intro r
      simp only [Category.assoc, cechMap_pr, op_comp, Functor.map_comp]
      rw [← Category.assoc (cechMap _ _ _ _ _ _), cechMap_pr, Category.assoc]
    rw [hi]
    rw [op_comp, M.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechComplexCocone {C : Type*} [Category C]
    {K : Type u} [SmallCategory K] {T : Type} {U : C}
    {V : T → C} {f : ∀ t, V t ⟶ U} (S : SiteCechComplex V f)
    (A : T → Kᵒᵖ ⥤ C) (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (q : ∀ t, (Functor.const Kᵒᵖ).obj (V t) ⟶ A t)
    (hf : ∀ t k, (q t).app k ≫ g k t = f t)
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Cocone (cechComplexDiagram A g hg R M) where
  pt := S.complex M
  ι :=
    { app k := cechComplexMap (R (op k)) S (fun t ↦ (q t).app (op k))
        (fun t ↦ hf t (op k)) M
      naturality {i j} h := by
        apply HomologicalComplex.Hom.ext
        funext p
        apply AddCommGrpCat.ext
        intro s
        funext α
        change M.map (cechMap _ _ _ _ _ _).op
            (M.map (cechMap _ _ _ _ _ _).op (s α)) =
          M.map (cechMap _ _ _ _ _ _).op (s α)
        have hi : cechMap (R (op j)) S (fun t ↦ (q t).app (op j)) (fun t ↦ hf t _) p α ≫
            cechMap (R (op i)) (R (op j)) (fun t ↦ (A t).map h.op) (hg _) p α =
            cechMap (R (op i)) S (fun t ↦ (q t).app (op i)) (fun t ↦ hf t _) p α := by
          apply cech_ext (R (op i))
          intro r
          rw [Category.assoc, cechMap_pr, ← Category.assoc, cechMap_pr, Category.assoc]
          rw [cechMap_pr]
          have hn := (q (α r)).naturality h.op
          dsimp only [Functor.const_obj_map] at hn
          erw [Category.id_comp] at hn
          exact congrArg (fun z ↦ S.pr p α r ≫ z) hn.symm
        simp only [← AddCommGrpCat.comp_apply, ← M.map_comp, ← op_comp, hi] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem finiteProductColimit {K : Type u} [SmallCategory K] [IsFiltered K]
    {T : Type} [Finite T] (B : T → K ⥤ AddCommGrpCat.{u + 1})
    (c : ∀ t, Cocone (B t)) (hc : ∀ t, IsColimit (c t))
    (D : K ⥤ AddCommGrpCat.{u + 1}) (d : Cocone D)
    (e : ∀ k, D.obj k ≅ AddCommGrpCat.of (∀ t, (B t).obj k))
    (ed : d.pt ≅ AddCommGrpCat.of (∀ t, (c t).pt))
    (he : ∀ {i j} (h : i ⟶ j) (s : D.obj i) t,
      (e j).hom (D.map h s) t = (B t).map h ((e i).hom s t))
    (hd : ∀ k (s : D.obj k) t, ed.hom (d.ι.app k s) t = (c t).ι.app k ((e k).hom s t)) :
    Nonempty (IsColimit d) := by
  classical
  let := Fintype.ofFinite T
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  apply Nonempty.intro
  have : ReflectsColimit D (CategoryTheory.forget AddCommGrpCat) :=
    reflectsColimit_of_reflectsIsomorphisms D (CategoryTheory.forget AddCommGrpCat)
  apply isColimitOfReflects (CategoryTheory.forget AddCommGrpCat)
  refine Types.FilteredColimit.isColimitOf' (D ⋙ CategoryTheory.forget _)
    ((CategoryTheory.forget _).mapCocone d) ?_ ?_
  · intro x
    obtain ⟨a, z, hz⟩ : ∃ (a : T → K) (z : ∀ t, (B t).obj (a t)),
        ∀ t, (c t).ι.app (a t) (z t) = ed.hom x t := by
      choose a z hz using fun t ↦ Concrete.isColimit_exists_rep (B t) (hc t) (ed.hom x t)
      exact ⟨a, z, hz⟩
    obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image a)
    let h (t : T) : a t ⟶ k :=
      (hk (Finset.mem_image_of_mem a (Finset.mem_univ t))).some
    let s : D.obj k := (e k).inv (fun t ↦ (B t).map (h t) (z t))
    refine ⟨k, s, ?_⟩
    apply (ConcreteCategory.isIso_iff_bijective ed.hom).mp inferInstance |>.1
    funext t
    change ed.hom x t = ed.hom (d.ι.app k s) t
    rw [hd]
    have hs : (e k).hom s t = (B t).map (h t) (z t) := by simp [s]
    rw [hs, ← hz]
    exact (ConcreteCategory.congr_hom ((c t).w (h t)) (z t)).symm
  · intro i x y hxy
    have ht (t : T) : (c t).ι.app i ((e i).hom x t) =
        (c t).ι.app i ((e i).hom y t) := by
      rw [← hd, ← hd]
      exact congrArg (fun z ↦ ed.hom z t) hxy
    have hz (t : T) : ∃ (k : K) (h : i ⟶ k),
        (B t).map h ((e i).hom x t) = (B t).map h ((e i).hom y t) := by
      obtain ⟨k, f, g, h⟩ := (Concrete.isColimit_rep_eq_iff_exists (B t) (hc t) _ _).mp (ht t)
      obtain ⟨l, h', w⟩ := IsFilteredOrEmpty.cocone_maps f g
      refine ⟨l, f ≫ h', ?_⟩
      calc
        _ = (B t).map h' ((B t).map f ((e i).hom x t)) := by
          rw [(B t).map_comp]; rfl
        _ = (B t).map h' ((B t).map g ((e i).hom y t)) := congrArg ((B t).map h') h
        _ = (B t).map (g ≫ h') ((e i).hom y t) := by
          rw [(B t).map_comp]; rfl
        _ = _ := by rw [w]
    choose k h hh using hz
    obtain ⟨l, f, g, hg⟩ := IsFiltered.wideSpan h
    refine ⟨l, f, ?_⟩
    apply (ConcreteCategory.isIso_iff_bijective (e l).hom).mp inferInstance |>.1
    funext t
    change (e l).hom (D.map f x) t = (e l).hom (D.map f y) t
    rw [he, he, ← hg t, (B t).map_comp]
    exact congrArg ((B t).map (g t)) (hh t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def cechComplexIsColimit {C : Type*} [Category C]
    {K : Type u} [SmallCategory K] [IsFiltered K] {T : Type} [Finite T] {U : C}
    {V : T → C} {f : ∀ t, V t ⟶ U} (S : SiteCechComplex V f)
    (A : T → Kᵒᵖ ⥤ C) (g : ∀ k t, (A t).obj k ⟶ U)
    (hg : ∀ {i j} (h : i ⟶ j) t, (A t).map h ≫ g j t = g i t)
    (R : ∀ k, SiteCechComplex (fun t ↦ (A t).obj k) (g k))
    (q : ∀ t, (Functor.const Kᵒᵖ).obj (V t) ⟶ A t)
    (hf : ∀ t k, (q t).app k ≫ g k t = f t)
    (hl : ∀ t, IsLimit (Cone.mk (V t) (q t)))
    (M : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [PreservesFilteredColimitsOfSize.{u, u} M] :
    IsColimit (cechComplexCocone S A g hg R q hf M) := by
  classical
  have : Nonempty Kᵒᵖ := ⟨op IsFiltered.nonempty.some⟩
  let D := cechComplexDiagram A g hg R M
  let d := cechComplexCocone S A g hg R q hf M
  apply HomologicalComplex.isColimitOfEval D d
  intro p
  let B (α : Fin (p + 1) → T) := (cechDiagram A g hg R p α).rightOp ⋙ M
  let c (α : Fin (p + 1) → T) := M.mapCocone (coconeRightOpOfCone (cechCone S A g hg R q hf p α))
  have hc (α) : IsColimit (c α) :=
    isColimitOfPreserves M
      (isColimitCoconeRightOpOfCone _ (cechConeIsLimit S A g hg R q hf hl p α))
  exact Classical.choice (finiteProductColimit (K := K) B c hc
    (D ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p)
    ((HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapCocone d)
    (fun _ ↦ Iso.refl _) (Iso.refl _) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def extendIsColimit {K : Type u} [SmallCategory K]
    (D : K ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ) (d : Cocone D)
    (hd : IsColimit d) : IsColimit
      ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).mapCocone d) := by
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor AddCommGrpCat.{u + 1}
  apply HomologicalComplex.isColimitOfEval (D ⋙ E) (E.mapCocone d)
  intro z
  by_cases h : ∃ n, e.f n = z
  · let n := h.choose
    have hn := h.choose_spec
    let a : D ⋙ E ⋙ HomologicalComplex.eval _ _ z ≅
        D ⋙ HomologicalComplex.eval _ _ n := NatIso.ofComponents
      (fun k ↦ (D.obj k).extendXIso e hn) (fun f ↦ by
        dsimp only [Functor.comp_map, E, ComplexShape.Embedding.extendFunctor_map,
          HomologicalComplex.eval_map]
        rw [HomologicalComplex.extendMap_f _ e hn]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)
    exact (IsColimit.equivOfNatIsoOfIso a
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) z).mapCocone (E.mapCocone d))
      ((HomologicalComplex.eval _ (ComplexShape.up ℕ) n).mapCocone d)
      (Cocone.ext (d.pt.extendXIso e hn) (fun k ↦ by
        dsimp only [a, E, ComplexShape.Embedding.extendFunctor_map,
          NatIso.ofComponents_inv_app, Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
          Cocone.precompose_obj_ι, NatTrans.comp_app]
        rw [HomologicalComplex.extendMap_f _ e hn]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id]
        rfl))).symm
      (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hd)
  · apply IsColimit.ofIsZero
    · apply (Functor.isZero_iff _).2
      intro k
      exact (D.obj k).isZero_extend_X e z (fun n hn ↦ h ⟨n, hn⟩)
    · exact d.pt.isZero_extend_X e z (fun n hn ↦ h ⟨n, hn⟩)

-- Keep the geometric presentation hypotheses in the public statement, although
-- the continuity argument only needs the supplied limit cones and basis objects.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedVariables false in
/-- The canonical restriction comparisons for the first finite-cover limit are
isomorphisms, both on integer-indexed complexes and in every nonnegative cohomological
degree. `e` only identifies the objects of the diagram with the chosen ordered Čech
complexes. The two coordinate formulas fix its transitions and cocone legs as the
actual restrictions along the unique projection-compatible intersection maps.
Source: Stacks Project, Tags 099U and 099S, first Čech-colimit calculation
(blueprint: lem-weil-pbc-finite-basis-cech-first-limit).

Proof:
1. Reindex each given coordinate presentation along the initial opposite evaluation
   functor from the product of directed sets. Reflect its underlying scheme limit
   into the affine ind-étale category. The universal property of the ordered
   intersections then constructs their limit cones directly for these given systems.
2. Use set-valued classical continuity and the pullback/forgetful comparison to
   obtain continuity for module coefficients. The forgetful functor preserves
   filtered colimits and reflects their universal properties. Forgetting modules
   to abelian groups and removing sheafification of an already-sheaf presheaf gives
   continuity for firstLimitClassicalPresheaf.
3. For each fixed degree, the ordered tuple set is finite. Representatives of its
   finitely many section classes have a common upper stage; finitely many eventual
   equalities hold at a common upper stage as well. This proves the product section
   cocone colimiting, using the concrete filtered-colimit criterion.
4. The intersection universal property constructs transition and projection maps.
   Uniqueness proves their functoriality and compatibility with deleting factors.
   Applying the coefficient presheaf and the alternating finite sum therefore gives
   genuine complex maps, the complex diagram, and its restriction cocone.
5. The degreewise universal property gives the colimit in nonnegative complexes.
   Extension by zero preserves this colimit: in nonnegative integer degrees this
   is the same evaluation colimit, and in negative degrees it is a zero colimit.
6. Filtered abelian-group colimits are exact. The homology functor thus preserves
   the cocone's colimit in every nonnegative degree. A colimiting cocone's canonical
   colimit.desc is an isomorphism, giving both requested comparisons. -/
theorem finite_basis_cech_first_limit (X : Scheme.{u}) [IsAffine X]
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.AffineProEt) {m : ℕ} (hm : 0 < m)
    (V : Fin m → X.AffineProEt) (f : ∀ a, V a ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ topology X U)
    (J : Fin m → Type u) [∀ a, Preorder (J a)] [∀ a, Nonempty (J a)]
    [∀ a, IsDirected (J a) (· ≤ ·)]
    (D : ∀ a, (J a)ᵒᵖ ⥤ Over U.left)
    (q : ∀ a, (Functor.const (J a)ᵒᵖ).obj (Over.mk (f a).left) ⟶ D a)
    (hD : ∀ a i, proAffineEtale (((D a).obj i).hom ≫ U.hom))
    (hstage : ∀ a i, IsAffine ((D a).obj i).left ∧ Etale ((D a).obj i).hom ∧
      LocallyOfFinitePresentation ((D a).obj i).hom ∧ QuasiCompact ((D a).obj i).hom)
    (hlimit : ∀ a, Nonempty (IsLimit ((Over.forget U.left).mapCone
      (Cone.mk (Over.mk (f a).left) (q a)))))
    (htransition : ∀ a (i j : (J a)ᵒᵖ) (h : i ⟶ j), IsAffineHom ((D a).map h).left)
    (hprojection : ∀ a i, IsAffineHom ((q a).app i).left)
    (hstagecover : ∀ j : ∀ a, J a,
      Sieve.ofArrows (fun a ↦ ((D a).obj (op (j a))).left)
        (fun a ↦ ((D a).obj (op (j a))).hom) ∈ etaleTopology U.left)
    (S : SiteCechComplex V f)
    (Sj : ∀ j : ∀ a, J a,
      SiteCechComplex (firstLimitBasisStage U D hD j) (firstLimitBasisArrow U D hD j)) :
    ∃ (C : (∀ a, J a) ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (e : ∀ j, C.obj j ≅ (Sj j).complex (firstLimitClassicalPresheaf X Λ F))
      (ι : C ⟶ (Functor.const (∀ a, J a)).obj
        (S.complex (firstLimitClassicalPresheaf X Λ F))),
      (∀ (i j : ∀ a, J a) (h : i ⟶ j) (p : ℕ)
        (s : (Sj i).cochains (firstLimitClassicalPresheaf X Λ F) p)
        (α : Fin (p + 1) → Fin m) (b : (Sj j).W p α ⟶ (Sj i).W p α),
        (∀ r, b ≫ (Sj i).pr p α r =
          (Sj j).pr p α r ≫ firstLimitBasisTransition U D hD h (α r)) →
        (((e i).inv ≫ C.map h ≫ (e j).hom).f p) s α =
          (firstLimitClassicalPresheaf X Λ F).map b.op (s α)) ∧
      (∀ (j : ∀ a, J a) (p : ℕ)
        (s : (Sj j).cochains (firstLimitClassicalPresheaf X Λ F) p)
        (α : Fin (p + 1) → Fin m) (b : S.W p α ⟶ (Sj j).W p α),
        (∀ r, b ≫ (Sj j).pr p α r =
          S.pr p α r ≫ firstLimitBasisProjection U V f D hD q j (α r)) →
        (((e j).inv ≫ ι.app j).f p) s α =
          (firstLimitClassicalPresheaf X Λ F).map b.op (s α)) ∧
      IsIso (colimit.desc
        (C ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).mapCocone
          (Cocone.mk (S.complex (firstLimitClassicalPresheaf X Λ F)) ι))) ∧
      ∀ q : ℕ, IsIso (colimit.desc
        (C ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q)
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapCocone
          (Cocone.mk (S.complex (firstLimitClassicalPresheaf X Λ F)) ι))) := by
  classical
  let K := ∀ a, J a
  let A (a : Fin m) : Kᵒᵖ ⥤ X.AffineProEt :=
    MorphismProperty.Over.lift (P := proAffineEtale) (Q := ⊤)
      (firstLimitCoordinate D a ⋙ Over.map U.hom)
      (fun j ↦ hD a (op (j.unop a))) (fun _ ↦ trivial)
  let g (j : Kᵒᵖ) (a : Fin m) : (A a).obj j ⟶ U :=
    firstLimitBasisArrow U D hD j.unop a
  have hg {i j : Kᵒᵖ} (h : i ⟶ j) (a : Fin m) :
      (A a).map h ≫ g j a = g i a := by
    apply MorphismProperty.Over.Hom.ext
    exact Over.w ((firstLimitCoordinate D a).map h)
  let R (j : Kᵒᵖ) := Sj j.unop
  let Q (a : Fin m) : (Functor.const Kᵒᵖ).obj (V a) ⟶ A a :=
    { app j := firstLimitBasisProjection U V f D hD q j.unop a
      naturality {i j} h := by
        apply MorphismProperty.Over.Hom.ext
        change ((q a).app (op (j.unop a))).left =
          ((q a).app (op (i.unop a))).left ≫ ((D a).map ((Pi.eval J a).op.map h)).left
        have hn := congrArg Over.Hom.left ((q a).naturality ((Pi.eval J a).op.map h))
        simpa using hn }
  have hf (a : Fin m) (j : Kᵒᵖ) : (Q a).app j ≫ g j a = f a := by
    apply MorphismProperty.Over.Hom.ext
    exact Over.w ((q a).app (op (j.unop a)))
  have hl (a : Fin m) : IsLimit (Cone.mk (V a) (Q a)) := by
    apply isLimitOfReflects (toScheme X)
    have h := ((Functor.Initial.isLimitWhiskerEquiv (Pi.eval J a).op
      ((Over.forget U.left).mapCone (Cone.mk (Over.mk (f a).left) (q a)))).symm
        (Classical.choice (hlimit a)))
    exact h
  let M := firstLimitClassicalPresheaf X Λ F
  have : PreservesFilteredColimitsOfSize.{u, u} M := classicalContinuous X Λ F
  let C := cechComplexDiagram A g hg R M
  let d := cechComplexCocone S A g hg R Q hf M
  have hd : IsColimit d := cechComplexIsColimit S A g hg R Q hf hl M
  refine ⟨C, fun _ ↦ Iso.refl _, d.ι, ?_, ?_, ?_, ?_⟩
  · intro i j h p s α b hb
    have hh : b = cechMap (Sj i) (Sj j)
        (fun a ↦ (A a).map h.op) (hg h.op) p α := by
      apply cech_ext (Sj i)
      intro r
      rw [cechMap_pr]
      exact hb r
    rw [hh]
    rfl
  · intro j p s α b hb
    have hh : b = cechMap (Sj j) S
        (fun a ↦ (Q a).app (op j)) (fun a ↦ hf a (op j)) p α := by
      apply cech_ext (Sj j)
      intro r
      rw [cechMap_pr]
      exact hb r
    rw [hh]
    rfl
  · exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp
      ⟨extendIsColimit C d hd⟩
  · intro n
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_shrink.{u, u, u + 1, u + 1} _
    exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp
      ⟨isColimitOfPreserves (HomologicalComplex.homologyFunctor _ _ n) hd⟩

end AlgebraicGeometry.Scheme.AffineProEt
