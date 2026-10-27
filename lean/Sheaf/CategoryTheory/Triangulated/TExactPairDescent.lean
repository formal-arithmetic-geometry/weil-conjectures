/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Algebra.Colimit.Module

/-! # Exact t-exact descent on common-stage pair categories

Source: Stacks Project, Tags 014V and 00D6; blueprint sketch 42,
Propositions `prop:pseudocone-functor` and `prop:pseudocone-exact`
(blueprint: lem-a1-texact-pair-descent).

The presentations below specify the assumed stage-induced shifts, distinguished triangles
and t-structure halves on the existing common-stage quotient. Only comparisons with shift
by one are used, exactly as in Tag 014V; no coherence between associators and shifts is added.
-/

@[expose] public section

set_option autoImplicit false

universe w u v uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.CommonStage

/-- Image of a triangle with a specified comparison with shift by one.
This is the explicit triangle in the definition of an exact functor, with no choice of
comparisons for other integers. Source: Stacks Project, Tag 014V
(blueprint: lem-a1-texact-pair-descent). -/
def triangleImageOne
    {C : Type uC} [Category.{vC} C] [HasShift C ℤ]
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    (F : C ⥤ D) (c : shiftFunctor C (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ))
    (T : Triangle C) : Triangle D :=
  Triangle.mk (F.map T.mor₁) (F.map T.mor₂) (F.map T.mor₃ ≫ c.hom.app T.obj₁)

-- Category and shift structures are bundled, so their carrier universes occur in a maximum.
set_option linter.checkUnivs false in
/-- A normalized diagram with the exact t-exact transitions assumed in the node.
The exactness fields expand Tag 014V using `triangleImageOne`; the t-exactness fields
preserve the two halves at zero. Source: Stacks Project, Tag 014V, and sketch 42,
finite-stage transitions (blueprint: lem-a1-texact-pair-descent). -/
structure ExactPairDiagram (I : Type w) [PartialOrder I] extends Diagram.{w, u, v} I where
  [shift : ∀ i, HasShift (C i) ℤ]
  [zero : ∀ i, HasZeroObject (C i)]
  [shift_additive : ∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [pretriangulated : ∀ i, Pretriangulated (C i)]
  [triangulated : ∀ i, IsTriangulated (C i)]
  t : ∀ i, TStructure (C i)
  bounded : ∀ i, (t i).bounded = ⊤
  s : ∀ {i j} (h : i ≤ j),
    shiftFunctor (C i) (1 : ℤ) ⋙ U h ≅ U h ⋙ shiftFunctor (C j) (1 : ℤ)
  exact : ∀ {i j} (h : i ≤ j) (T : Triangle (C i)),
    T ∈ distTriang (C i) → triangleImageOne (U h) (s h) T ∈ distTriang (C j)
  le : ∀ {i j} (h : i ≤ j) (X : C i), (t i).le 0 X → (t j).le 0 ((U h).obj X)
  ge : ∀ {i j} (h : i ≤ j) (X : C i), (t i).ge 0 X → (t j).ge 0 ((U h).obj X)

attribute [instance] ExactPairDiagram.shift ExactPairDiagram.zero
  ExactPairDiagram.shift_additive ExactPairDiagram.pretriangulated ExactPairDiagram.triangulated

variable {I : Type w} [PartialOrder I]

/-- The assumed finite-stage presentation of the pair category's triangulated and bounded
 t-structures. The inclusion functors and shift identifications are characterized by their
 literal object and representative formulas, rather than arbitrary supplied maps.
Source: sketch 42, stage inclusions and finite-stage triangles; the node's assumed halves
(blueprint: lem-a1-texact-pair-descent). -/
structure ExactPairPresentation (A : ExactPairDiagram.{w, u, v} I)
    (R : PairStructure A.toDiagram)
    [HasShift R.Obj ℤ] [HasZeroObject R.Obj]
    [∀ n : ℤ, (shiftFunctor R.Obj n).Additive]
    [Pretriangulated R.Obj] [IsTriangulated R.Obj] where
  canonical : R.IsCanonical
  J : ∀ i, A.C i ⥤ R.Obj
  obj : ∀ (i : I) (X : A.C i), (J i).obj X = ⟨i, X⟩
  map : ∀ (i : I) (X Y : A.C i) (f : X ⟶ Y),
    HEq ((J i).map f)
      (R.repr (X := ⟨i, X⟩) (Y := ⟨i, Y⟩)
        ⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩)
  shift_obj : ∀ X : R.Obj, X⟦(1 : ℤ)⟧ = ⟨X.1, X.2⟦(1 : ℤ)⟧⟩
  shift_map : ∀ {X Y : R.Obj} (r : Rep A.toDiagram X Y),
    HEq ((R.repr r)⟦(1 : ℤ)⟧')
      (R.repr (X := ⟨X.1, X.2⟦(1 : ℤ)⟧⟩) (Y := ⟨Y.1, Y.2⟦(1 : ℤ)⟧⟩)
        ⟨r.stage, r.source_le, r.target_le,
          (A.s r.source_le).hom.app X.2 ≫ r.arrow⟦(1 : ℤ)⟧' ≫
            (A.s r.target_le).inv.app Y.2⟩)
  j : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ J i ≅ J i ⋙ shiftFunctor R.Obj (1 : ℤ)
  j_identity : ∀ (i : I) (X : A.C i),
    HEq ((j i).hom.app X) (𝟙 ((J i).obj (X⟦(1 : ℤ)⟧)))
  triangles : ∀ T : Triangle R.Obj, T ∈ distTriang R.Obj ↔
    ∃ (i : I) (T₀ : Triangle (A.C i)), T₀ ∈ distTriang (A.C i) ∧
      Nonempty (T ≅ triangleImageOne (J i) (j i) T₀)
  t : TStructure R.Obj
  bounded : t.bounded = ⊤
  le : ∀ X : R.Obj, t.le 0 X ↔
    ∃ (i : I) (K : A.C i), (A.t i).le 0 K ∧ Nonempty (X ≅ (J i).obj K)
  ge : ∀ X : R.Obj, t.ge 0 X ↔
    ∃ (i : I) (K : A.C i), (A.t i).ge 0 K ∧ Nonempty (X ≅ (J i).obj K)

private theorem transport_self {A : Diagram.{w, u, v} I} {X Y : Pair A}
    (r : Rep A X Y) : transport r (le_refl r.stage) = r.arrow := by
  simp [transport, A.a_right, Functor.congr_hom (A.unit r.stage) r.arrow]

private theorem transport_stage {A : Diagram.{w, u, v} I}
    {i j : I} (h : i ≤ j) {X Y : A.C i} (f : X ⟶ Y) :
    transport (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ :
      Rep A ⟨i, X⟩ ⟨i, Y⟩) h = (A.U h).map f := by
  simp [transport, A.a_left, Functor.congr_hom (A.unit i) f, eqToHom_map]

private theorem repr_comp_stage {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) {X : R.Obj} {i : I} {Y Z : A.C i}
    (r : Rep A X ⟨i, Y⟩) (f : Y ⟶ Z) :
    R.repr r ≫ R.repr (X := ⟨i, Y⟩) (Y := ⟨i, Z⟩)
      ⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ =
    R.repr (X := X) (Y := ⟨i, Z⟩)
      ⟨r.stage, r.source_le, r.target_le, r.arrow ≫ (A.U r.target_le).map f⟩ := by
  simpa only [transport_self, transport_stage] using
    hR.composition r
      (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ :
        Rep A ⟨i, Y⟩ ⟨i, Z⟩) r.stage (le_refl _) r.target_le

private theorem stage_comp_repr {A : Diagram.{w, u, v} I} (R : PairStructure A)
    (hR : R.IsCanonical) {i : I} {X Y : A.C i} {Z : R.Obj}
    (f : X ⟶ Y) (r : Rep A ⟨i, Y⟩ Z) :
    R.repr (X := ⟨i, X⟩) (Y := ⟨i, Y⟩)
      ⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ ≫ R.repr r =
    R.repr (X := ⟨i, X⟩) (Y := Z)
      ⟨r.stage, r.source_le, r.target_le, (A.U r.source_le).map f ≫ r.arrow⟩ := by
  simpa only [transport_self, transport_stage] using
    hR.composition
      (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ :
        Rep A ⟨i, X⟩ ⟨i, Y⟩) r r.stage r.source_le (le_refl _)

private def canonicalIdentity [IsDirectedOrder I] {A : Diagram.{w, u, v} I} (R S : PairStructure A)
    (hR : R.IsCanonical) (hS : S.IsCanonical) : R.Obj ⥤ S.Obj where
  obj X := X
  map f := f
  map_id X := (hR.identity X).trans (hS.identity X).symm
  map_comp {X Y Z} f g := by
    induction f using Quot.inductionOn with
    | h r =>
      induction g using Quot.inductionOn with
      | h s =>
        obtain ⟨n, hr, hs⟩ := exists_ge_ge r.stage s.stage
        exact (hR.composition r s n hr hs).trans (hS.composition r s n hr hs).symm

private theorem canonicalIdentity_additive [IsDirectedOrder I]
    {A : Diagram.{w, u, v} I} (R S : PairStructure A)
    (hR : R.IsCanonical) (hS : S.IsCanonical) :
    (canonicalIdentity R S hR hS).Additive where
  map_add {X Y} f g := by
    induction f using Quot.inductionOn with
    | h r =>
      induction g using Quot.inductionOn with
      | h s =>
        obtain ⟨n, hr, hs⟩ := exists_ge_ge r.stage s.stage
        exact (hR.addition r s n hr hs).trans (hS.addition r s n hr hs).symm

private theorem map_heq
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'
  subst Y'
  cases h
  rfl

private theorem eqToHom_of_heq_id
    {C : Type uC} [Category.{vC} C] {X Y : C} (h : X = Y) (f : X ⟶ Y)
    (hf : HEq f (𝟙 X)) : f = eqToHom h := by
  subst Y
  exact eq_of_heq hf

private theorem heq_add
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} (hf : HEq f f') (hg : HEq g g') :
    HEq (f + g) (f' + g') := by
  subst X'
  subst Y'
  cases hf
  cases hg
  rfl

private theorem stage_additive (A : ExactPairDiagram.{w, u, v} I)
    (R : PairStructure A.toDiagram)
    [HasShift R.Obj ℤ] [HasZeroObject R.Obj]
    [∀ n : ℤ, (shiftFunctor R.Obj n).Additive]
    [Pretriangulated R.Obj] [IsTriangulated R.Obj]
    (P : ExactPairPresentation A R) (i : I) : (P.J i).Additive where
  map_add {X Y} f g := by
    apply eq_of_heq
    have h := P.map i X Y (f + g)
    have hr := P.canonical.addition
      (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ :
        Rep A.toDiagram ⟨i, X⟩ ⟨i, Y⟩)
      (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map g⟩ :
        Rep A.toDiagram ⟨i, X⟩ ⟨i, Y⟩) i (le_refl _) (le_refl _)
    simp only [transport_self, Functor.map_add] at hr h
    exact h.trans (heq_of_eq hr.symm) |>.trans
      (heq_add (P.obj i X) (P.obj i Y) (P.map i X Y f) (P.map i X Y g)).symm

private theorem stage_exact (A : ExactPairDiagram.{w, u, v} I)
    (R : PairStructure A.toDiagram)
    [HasShift R.Obj ℤ] [HasZeroObject R.Obj]
    [∀ n : ℤ, (shiftFunctor R.Obj n).Additive]
    [Pretriangulated R.Obj] [IsTriangulated R.Obj]
    (P : ExactPairPresentation A R) (i : I)
    (T : Triangle (A.C i)) (hT : T ∈ distTriang (A.C i)) :
    triangleImageOne (P.J i) (P.j i) T ∈ distTriang R.Obj := by
  exact (P.triangles _).2 ⟨i, T, hT, ⟨Iso.refl _⟩⟩

private theorem shiftIso_all
    {C : Type uC} [Category.{vC} C] [HasShift C ℤ]
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    (F : C ⥤ D)
    (e : ∀ X, F.obj (X⟦(1 : ℤ)⟧) ≅ (F.obj X)⟦(1 : ℤ)⟧)
    (n : ℤ) : ∀ X, Nonempty (F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧) := by
  have add (a b : ℤ)
      (ha : ∀ X, Nonempty (F.obj (X⟦a⟧) ≅ (F.obj X)⟦a⟧))
      (hb : ∀ X, Nonempty (F.obj (X⟦b⟧) ≅ (F.obj X)⟦b⟧)) :
      ∀ X, Nonempty (F.obj (X⟦a + b⟧) ≅ (F.obj X)⟦a + b⟧) := by
    intro X
    obtain ⟨ea⟩ := ha X
    obtain ⟨eb⟩ := hb (X⟦a⟧)
    exact ⟨F.mapIso ((shiftFunctorAdd C a b).app X) ≪≫ eb ≪≫
      (shiftFunctor D b).mapIso ea ≪≫ ((shiftFunctorAdd D a b).app (F.obj X)).symm⟩
  have negOne : ∀ X, Nonempty (F.obj (X⟦(-1 : ℤ)⟧) ≅ (F.obj X)⟦(-1 : ℤ)⟧) := by
    intro X
    exact ⟨((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by simp)).app
        (F.obj (X⟦(-1 : ℤ)⟧))).symm ≪≫
      (shiftFunctor D (-1 : ℤ)).mapIso (e (X⟦(-1 : ℤ)⟧)).symm ≪≫
      (shiftFunctor D (-1 : ℤ)).mapIso
        (F.mapIso ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by simp)).app X))⟩
  induction n using Int.induction_on with
  | zero =>
    intro X
    exact ⟨F.mapIso ((shiftFunctorZero C ℤ).app X) ≪≫
      ((shiftFunctorZero D ℤ).app (F.obj X)).symm⟩
  | succ n ih => exact add n 1 ih (fun X ↦ ⟨e X⟩)
  | pred n ih => simpa only [sub_eq_add_neg] using add (-n) (-1) ih negOne

private theorem halves_all
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (tC : TStructure C) (tD : TStructure D) (F : C ⥤ D)
    (e : ∀ X, F.obj (X⟦(1 : ℤ)⟧) ≅ (F.obj X)⟦(1 : ℤ)⟧)
    (hLE : ∀ X, tC.le 0 X → tD.le 0 (F.obj X))
    (hGE : ∀ X, tC.ge 0 X → tD.ge 0 (F.obj X))
    (n : ℤ) (X : C) :
    (tC.le n X → tD.le n (F.obj X)) ∧ (tC.ge n X → tD.ge n (F.obj X)) := by
  obtain ⟨en⟩ := shiftIso_all F e n X
  constructor
  · intro hX
    have h := hLE _ (tC.le_shift n n 0 (add_zero n) X hX)
    have h' := (tD.le 0).prop_of_iso en h
    have h'' := tD.le_shift 0 (-n) n (neg_add_cancel n) _ h'
    exact (tD.le n).prop_of_iso
      ((shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).app (F.obj X)) h''
  · intro hX
    have h := hGE _ (tC.ge_shift n n 0 (add_zero n) X hX)
    have h' := (tD.ge 0).prop_of_iso en h
    have h'' := tD.ge_shift 0 (-n) n (neg_add_cancel n) _ h'
    exact (tD.ge n).prop_of_iso
      ((shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).app (F.obj X)) h''

private theorem stage_halves (A : ExactPairDiagram.{w, u, v} I)
    (R : PairStructure A.toDiagram)
    [HasShift R.Obj ℤ] [HasZeroObject R.Obj]
    [∀ n : ℤ, (shiftFunctor R.Obj n).Additive]
    [Pretriangulated R.Obj] [IsTriangulated R.Obj]
    (P : ExactPairPresentation A R) (i : I) (n : ℤ) (X : A.C i) :
    ((A.t i).le n X → P.t.le n ((P.J i).obj X)) ∧
      ((A.t i).ge n X → P.t.ge n ((P.J i).obj X)) := by
  apply halves_all (A.t i) P.t (P.J i) (fun X ↦ (P.j i).app X)
  · intro X hX
    exact (P.le _).2 ⟨i, X, hX, ⟨Iso.refl _⟩⟩
  · intro X hX
    exact (P.ge _).2 ⟨i, X, hX, ⟨Iso.refl _⟩⟩

private def triangleMapOne
    {C : Type uC} [Category.{vC} C] [HasShift C ℤ]
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    (F : C ⥤ D) (c : shiftFunctor C (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ)) :
    Triangle C ⥤ Triangle D where
  obj := triangleImageOne F c
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp [triangleImageOne, Triangle.mk]; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp [triangleImageOne, Triangle.mk]; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [triangleImageOne, Triangle.mk]
        simp only [Category.assoc, ← F.map_comp_assoc]
        have h := c.hom.naturality f.hom₁
        dsimp only [Functor.comp_map] at h
        rw [← h]
        simp only [← F.map_comp_assoc, f.comm₃] }

private theorem triangle_comp_iso
    {C₀ : Type*} [Category C₀] [HasShift C₀ ℤ]
    {D₀ : Type*} [Category D₀] [HasShift D₀ ℤ]
    {C : Type uC} [Category.{vC} C] [HasShift C ℤ]
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    (J : C₀ ⥤ C) (j : shiftFunctor C₀ (1 : ℤ) ⋙ J ≅ J ⋙ shiftFunctor C (1 : ℤ))
    (F : C ⥤ D) (γ : shiftFunctor C (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor D (1 : ℤ))
    (G : C₀ ⥤ D₀) (c : shiftFunctor C₀ (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor D₀ (1 : ℤ))
    (K : D₀ ⥤ D) (k : shiftFunctor D₀ (1 : ℤ) ⋙ K ≅ K ⋙ shiftFunctor D (1 : ℤ))
    (κ : J ⋙ F ≅ G ⋙ K)
    (hs : ∀ X, F.map (j.hom.app X) ≫ γ.hom.app (J.obj X) ≫
      (κ.hom.app X)⟦(1 : ℤ)⟧' =
      κ.hom.app (X⟦(1 : ℤ)⟧) ≫ K.map (c.hom.app X) ≫ k.hom.app (G.obj X))
    (T : Triangle C₀) :
    Nonempty (triangleImageOne F γ (triangleImageOne J j T) ≅
      triangleImageOne K k (triangleImageOne G c T)) := by
  refine ⟨Triangle.isoMk _ _ (κ.app T.obj₁) (κ.app T.obj₂) (κ.app T.obj₃) ?_ ?_ ?_⟩
  · exact κ.hom.naturality T.mor₁
  · exact κ.hom.naturality T.mor₂
  · dsimp [triangleImageOne, Triangle.mk]
    simp only [Functor.map_comp, Category.assoc]
    calc
      _ = F.map (J.map T.mor₃) ≫
          (κ.hom.app (T.obj₁⟦(1 : ℤ)⟧) ≫ K.map (c.hom.app T.obj₁) ≫
            k.hom.app (G.obj T.obj₁)) :=
        congrArg (fun f ↦ F.map (J.map T.mor₃) ≫ f) (hs T.obj₁)
      _ = _ := by
        have h := κ.hom.naturality T.mor₃
        dsimp only [Functor.comp_map] at h
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ K.map (c.hom.app T.obj₁) ≫
            k.hom.app (G.obj T.obj₁)) h

private theorem family_rep_unit {A B : Diagram.{w, u, v} I}
    (Φ : Family A B) (hb : Φ.Coherent) (i : I) {X Y : A.C i} (f : X ⟶ Y) :
    Φ.rep (⟨i, le_refl _, le_refl _, (A.U (le_refl i)).map f⟩ :
      Rep A ⟨i, X⟩ ⟨i, Y⟩) =
    (⟨i, le_refl _, le_refl _, (B.U (le_refl i)).map ((Φ.φ i).map f)⟩ :
      Rep B (Φ.obj ⟨i, X⟩) (Φ.obj ⟨i, Y⟩)) := by
  dsimp [Family.rep]
  congr 1
  simp [hb.unit, Functor.congr_hom (A.unit i) f,
    Functor.congr_hom (B.unit i) ((Φ.φ i).map f), eqToHom_map]

private theorem family_rep_extension {A B : Diagram.{w, u, v} I}
    (Φ : Family A B) (hb : Φ.Coherent) {i j : I} (h : i ≤ j) (X : A.C i) :
    Φ.rep (⟨j, h, le_refl _,
      (eqToIso (congrArg (fun G : A.C j ⥤ A.C j ↦ G.obj ((A.U h).obj X))
        (A.unit j))).inv⟩ : Rep A ⟨i, X⟩ ⟨j, (A.U h).obj X⟩) =
    (⟨j, h, le_refl _, (Φ.b h).hom.app X ≫
      (eqToIso (congrArg (fun G : B.C j ⥤ B.C j ↦
        G.obj ((Φ.φ j).obj ((A.U h).obj X))) (B.unit j))).inv⟩ :
      Rep B (Φ.obj ⟨i, X⟩) (Φ.obj ⟨j, (A.U h).obj X⟩)) := by
  dsimp [Family.rep]
  congr 1
  simp [hb.unit, eqToHom_map]

private theorem conjugate_naturality
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (H : C ⥤ C) (K : D ⥤ D) (c : H ⋙ F ≅ F ⋙ K)
    {X Y : C} (f : X ⟶ Y) {W₁ W₂ Z₁ Z₂ : D}
    (a₁ : W₁ ≅ F.obj (H.obj X)) (a₂ : W₂ ≅ F.obj (H.obj Y))
    (b₁ : Z₁ ≅ K.obj (F.obj X)) (b₂ : Z₂ ≅ K.obj (F.obj Y))
    (q₁ : W₁ ⟶ Z₁) (q₂ : W₂ ⟶ Z₂)
    (h₁ : q₁ ≫ b₁.hom = a₁.hom ≫ c.hom.app X)
    (h₂ : q₂ ≫ b₂.hom = a₂.hom ≫ c.hom.app Y) :
    (a₁.hom ≫ F.map (H.map f) ≫ a₂.inv) ≫ q₂ =
      q₁ ≫ b₁.hom ≫ K.map (F.map f) ≫ b₂.inv := by
  apply (cancel_mono b₂.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂]
  simp only [Iso.inv_hom_id_assoc]
  calc
    _ = a₁.hom ≫ c.hom.app X ≫ K.map (F.map f) := by
      simpa only [Category.assoc, Functor.comp_map] using
        congrArg (fun g ↦ a₁.hom ≫ g) (c.hom.naturality f)
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun g ↦ g ≫ K.map (F.map f)) h₁.symm

section DescentProperties

variable (A B : ExactPairDiagram.{w, u, v} I)
  (RA : PairStructure A.toDiagram) (RB : PairStructure B.toDiagram)
  [HasShift RA.Obj ℤ] [HasZeroObject RA.Obj]
  [∀ n : ℤ, (shiftFunctor RA.Obj n).Additive]
  [Pretriangulated RA.Obj] [IsTriangulated RA.Obj]
  [HasShift RB.Obj ℤ] [HasZeroObject RB.Obj]
  [∀ n : ℤ, (shiftFunctor RB.Obj n).Additive]
  [Pretriangulated RB.Obj] [IsTriangulated RB.Obj]
  (P : ExactPairPresentation A RA) (Q : ExactPairPresentation B RB)
  (Φ : Family A.toDiagram B.toDiagram) (hb : Φ.Coherent)
  (F : RA.Obj ⥤ RB.Obj) (hF : IsDescent RA RB Φ F)

include hb hF in
private theorem descent_stage (i : I) : P.J i ⋙ F = Φ.φ i ⋙ Q.J i := by
  apply Functor.hext
  · intro X
    change F.obj ((P.J i).obj X) = (Q.J i).obj ((Φ.φ i).obj X)
    rw [P.obj, hF.obj, Q.obj]
    rfl
  · intro X Y f
    change HEq (F.map ((P.J i).map f)) ((Q.J i).map ((Φ.φ i).map f))
    refine (map_heq F (P.obj i X) (P.obj i Y) (P.map i X Y f)).trans ?_
    refine (hF.map _).trans ?_
    rw [family_rep_unit Φ hb]
    exact (Q.map i _ _ ((Φ.φ i).map f)).symm

private def shiftComponent
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ)) (X : RA.Obj) :
    F.obj (X⟦(1 : ℤ)⟧) ≅ (F.obj X)⟦(1 : ℤ)⟧ :=
  eqToIso (by rw [P.shift_obj, hF.obj, Q.obj]; rfl) ≪≫
    (Q.J X.1).mapIso ((c X.1).app X.2) ≪≫
    eqToIso (by rw [hF.obj, Q.shift_obj, Q.obj]; rfl)

private theorem shiftComponent_hom
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ)) (X : RA.Obj) :
    HEq ((shiftComponent A B RA RB P Q Φ F hF c X).hom)
      ((Q.J X.1).map ((c X.1).hom.app X.2)) := by
  simp [shiftComponent]

set_option backward.isDefEq.respectTransparency false in
private theorem shiftComponent_naturality
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ))
    (hShift : ∀ {i j} (h : i ≤ j) (X : A.C i),
      (B.U h).map ((c i).hom.app X) ≫ (B.s h).hom.app ((Φ.φ i).obj X) ≫
          ((Φ.b h).hom.app X)⟦(1 : ℤ)⟧' =
        (Φ.b h).hom.app (X⟦(1 : ℤ)⟧) ≫ (Φ.φ j).map ((A.s h).hom.app X) ≫
          (c j).hom.app ((A.U h).obj X))
    {X Y : RA.Obj} (f : X ⟶ Y) :
    F.map (f⟦(1 : ℤ)⟧') ≫ (shiftComponent A B RA RB P Q Φ F hF c Y).hom =
      (shiftComponent A B RA RB P Q Φ F hF c X).hom ≫
        (F.map f)⟦(1 : ℤ)⟧' := by
  induction f using Quot.inductionOn with
  | h r =>
    let rA : Rep A.toDiagram
        ⟨X.1, X.2⟦(1 : ℤ)⟧⟩ ⟨Y.1, Y.2⟦(1 : ℤ)⟧⟩ :=
      ⟨r.stage, r.source_le, r.target_le,
        (A.s r.source_le).hom.app X.2 ≫ r.arrow⟦(1 : ℤ)⟧' ≫
          (A.s r.target_le).inv.app Y.2⟩
    let rD : Rep B.toDiagram
        ⟨X.1, ((Φ.φ X.1).obj X.2)⟦(1 : ℤ)⟧⟩
        ⟨Y.1, ((Φ.φ Y.1).obj Y.2)⟦(1 : ℤ)⟧⟩ :=
      ⟨r.stage, r.source_le, r.target_le,
        (B.s r.source_le).hom.app ((Φ.φ X.1).obj X.2) ≫
          (Φ.rep r).arrow⟦(1 : ℤ)⟧' ≫
          (B.s r.target_le).inv.app ((Φ.φ Y.1).obj Y.2)⟩
    have hL := (map_heq F (P.shift_obj X) (P.shift_obj Y) (P.shift_map r)).trans
      (hF.map rA)
    have hR := (map_heq (shiftFunctor RB.Obj (1 : ℤ))
      (hF.obj X) (hF.obj Y) (hF.map r)).trans (Q.shift_map (Φ.rep r))
    have hcX := (shiftComponent_hom A B RA RB P Q Φ F hF c X).trans
      (Q.map X.1 _ _ ((c X.1).hom.app X.2))
    have hcY := (shiftComponent_hom A B RA RB P Q Φ F hF c Y).trans
      (Q.map Y.1 _ _ ((c Y.1).hom.app Y.2))
    have hleft := heq_comp
      (by simp only [P.shift_obj, hF.obj, Family.obj])
      (by simp only [P.shift_obj, hF.obj, Family.obj])
      (by simp only [hF.obj, Q.shift_obj, Family.obj]; rfl) hL hcY
    have hright := heq_comp
      (by simp only [P.shift_obj, hF.obj, Family.obj]; rfl)
      (by simp only [hF.obj, Q.shift_obj, Family.obj]; rfl)
      (by simp only [hF.obj, Q.shift_obj, Family.obj]) hcX hR
    apply eq_of_heq
    refine hleft.trans ((heq_of_eq ?_).trans hright.symm)
    rw [repr_comp_stage RB Q.canonical, stage_comp_repr RB Q.canonical]
    congr 2
    dsimp [rA, rD, Family.rep, Family.obj]
    have h := conjugate_naturality (Φ.φ r.stage)
      (shiftFunctor (A.C r.stage) (1 : ℤ)) (shiftFunctor (B.C r.stage) (1 : ℤ))
      (c r.stage) r.arrow
      ((Φ.b r.source_le).app (X.2⟦(1 : ℤ)⟧) ≪≫
        (Φ.φ r.stage).mapIso ((A.s r.source_le).app X.2))
      ((Φ.b r.target_le).app (Y.2⟦(1 : ℤ)⟧) ≪≫
        (Φ.φ r.stage).mapIso ((A.s r.target_le).app Y.2))
      ((B.s r.source_le).app ((Φ.φ X.1).obj X.2) ≪≫
        (shiftFunctor (B.C r.stage) (1 : ℤ)).mapIso ((Φ.b r.source_le).app X.2))
      ((B.s r.target_le).app ((Φ.φ Y.1).obj Y.2) ≪≫
        (shiftFunctor (B.C r.stage) (1 : ℤ)).mapIso ((Φ.b r.target_le).app Y.2))
      ((B.U r.source_le).map ((c X.1).hom.app X.2))
      ((B.U r.target_le).map ((c Y.1).hom.app Y.2))
      (by simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
        Category.assoc] using hShift r.source_le X.2)
      (by simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
        Category.assoc] using hShift r.target_le Y.2)
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc] using h

include hb hF in
set_option backward.isDefEq.respectTransparency false in
private theorem descent_stage_shift
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ))
    (γ : shiftFunctor RA.Obj (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor RB.Obj (1 : ℤ))
    (hγ : ∀ X : RA.Obj, HEq (γ.hom.app X) ((Q.J X.1).map ((c X.1).hom.app X.2)))
    (i : I) : ∃ κ : P.J i ⋙ F ≅ Φ.φ i ⋙ Q.J i,
      (∀ X : A.C i, HEq (κ.hom.app X) (𝟙 ((Q.J i).obj ((Φ.φ i).obj X)))) ∧
      (∀ X : A.C i,
        F.map ((P.j i).hom.app X) ≫ γ.hom.app ((P.J i).obj X) ≫
            (κ.hom.app X)⟦(1 : ℤ)⟧' =
          κ.hom.app (X⟦(1 : ℤ)⟧) ≫ (Q.J i).map ((c i).hom.app X) ≫
            (Q.j i).hom.app ((Φ.φ i).obj X)) := by
  let κ := eqToIso (descent_stage A B RA RB P Q Φ hb F hF i)
  refine ⟨κ, ?_, ?_⟩
  · intro X
    dsimp only [κ, eqToIso.hom]
    rw [eqToHom_app]
    change HEq (eqToHom _) (𝟙 ((Φ.φ i ⋙ Q.J i).obj X))
    exact eqToHom_heq_id_cod _ _ _
  · intro X
    have hp := eqToHom_of_heq_id
      (show (P.J i).obj (X⟦(1 : ℤ)⟧) = ((P.J i).obj X)⟦(1 : ℤ)⟧ by
        rw [P.obj, P.obj, P.shift_obj]) _ (P.j_identity i X)
    have hq := eqToHom_of_heq_id
      (show (Q.J i).obj (((Φ.φ i).obj X)⟦(1 : ℤ)⟧) =
          ((Q.J i).obj ((Φ.φ i).obj X))⟦(1 : ℤ)⟧ by
        rw [Q.obj, Q.obj, Q.shift_obj]) _ (Q.j_identity i ((Φ.φ i).obj X))
    dsimp [κ]
    rw [hp, hq]
    simp only [eqToHom_app, eqToHom_map]
    apply eq_of_heq
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    have hg := hγ ((P.J i).obj X)
    rw [P.obj] at hg ⊢
    exact hg

include P hb hF in
private theorem descent_exact
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ))
    (γ : shiftFunctor RA.Obj (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor RB.Obj (1 : ℤ))
    (hγ : ∀ X : RA.Obj, HEq (γ.hom.app X) ((Q.J X.1).map ((c X.1).hom.app X.2)))
    (hExact : ∀ i (T : Triangle (A.C i)), T ∈ distTriang (A.C i) →
      triangleImageOne (Φ.φ i) (c i) T ∈ distTriang (B.C i))
    (T : Triangle RA.Obj) (hT : T ∈ distTriang RA.Obj) :
    triangleImageOne F γ T ∈ distTriang RB.Obj := by
  obtain ⟨i, T₀, hT₀, ⟨e⟩⟩ := (P.triangles T).1 hT
  obtain ⟨κ, _, hs⟩ := descent_stage_shift A B RA RB P Q Φ hb F hF c γ hγ i
  obtain ⟨e'⟩ := triangle_comp_iso (P.J i) (P.j i) F γ (Φ.φ i) (c i)
    (Q.J i) (Q.j i) κ hs T₀
  have hd := stage_exact B RB Q i _ (hExact i T₀ hT₀)
  exact isomorphic_distinguished _ hd _ ((triangleMapOne F γ).mapIso e ≪≫ e')

include hb hF in
private theorem descent_halves
    (γ : shiftFunctor RA.Obj (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor RB.Obj (1 : ℤ))
    (hLE : ∀ i (X : A.C i), (A.t i).le 0 X → (B.t i).le 0 ((Φ.φ i).obj X))
    (hGE : ∀ i (X : A.C i), (A.t i).ge 0 X → (B.t i).ge 0 ((Φ.φ i).obj X))
    (n : ℤ) (X : RA.Obj) :
    (P.t.le n X → Q.t.le n (F.obj X)) ∧ (P.t.ge n X → Q.t.ge n (F.obj X)) := by
  apply halves_all P.t Q.t F (fun X ↦ γ.app X)
  · intro X hX
    obtain ⟨i, K, hK, ⟨e⟩⟩ := (P.le X).1 hX
    apply (Q.le _).2
    refine ⟨i, (Φ.φ i).obj K, hLE i K hK, ?_⟩
    exact ⟨F.mapIso e ≪≫ eqToIso
      (Functor.congr_obj (descent_stage A B RA RB P Q Φ hb F hF i) K)⟩
  · intro X hX
    obtain ⟨i, K, hK, ⟨e⟩⟩ := (P.ge X).1 hX
    apply (Q.ge _).2
    refine ⟨i, (Φ.φ i).obj K, hGE i K hK, ?_⟩
    exact ⟨F.mapIso e ≪≫ eqToIso
      (Functor.congr_obj (descent_stage A B RA RB P Q Φ hb F hF i) K)⟩

end DescentProperties

private theorem descent_exists
    (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A B : Diagram.{w, u, v} (Padic.FiniteCoefficientFields l Ω))
    (RA : PairStructure A) (RB : PairStructure B)
    (hA : RA.IsCanonical) (hB : RB.IsCanonical)
    (Φ : Family A B) (hb : Φ.Coherent) :
    ∃ F : RA.Obj ⥤ RB.Obj, IsDescent RA RB Φ F := by
  classical
  let : IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) :=
    ⟨fun i j ↦ ⟨Padic.finiteCoefficientCompositum l Ω i j,
      (Padic.finiteCoefficientFields_properties l Ω).1 i j⟩⟩
  obtain ⟨S⟩ := coherent_pair_functor_descent.{w, u, v} l Ω
  let := canonicalIdentity_additive RA (S.pair A) hA (S.canonical A)
  let := canonicalIdentity_additive (S.pair B) RB (S.canonical B) hB
  let F := canonicalIdentity RA (S.pair A) hA (S.canonical A) ⋙ S.descend Φ hb ⋙
    canonicalIdentity (S.pair B) RB (S.canonical B) hB
  have hF := S.formula Φ hb
  let := hF.additive
  refine ⟨F, ⟨hF.obj, ?_, inferInstance⟩⟩
  intro X Y r
  exact hF.map r

/-- Exact t-exact functor descent with its stage and extension comparisons.
Source: Stacks Project, Tags 014V and 00D6; sketch 42, pseudocone exactness
(blueprint: lem-a1-texact-pair-descent).

Proof (the node's six steps):
1. Apply `lem-sbc-coherent-pair-functor-descent` to the normalized additive diagrams
   and coherent family. This gives an additive functor with the object and representative
   formulas in `IsDescent`, independent of stage and representative, without faithfulness.
2. Represent the shift comparison at `(E,X)` by `[E,c_E,X]`, with the stage inverse as
   inverse. At a common stage write dA = b at X[1] followed by F(sC), and dB = sD
   followed by b[1]. The assumed square says V(cE) followed by dB equals dA followed
   by cL. For any representative u, use this square at its target, naturality of cL at u,
   and this square at its source. These three equalities prove naturality of the
   represented comparison. Common-stage composition proves the inverse equations.
3. The stage inclusions preserve identities, sums and composition by canonical pair
   calculus (00D6); their shift comparison is the prescribed identity. They preserve
   distinguished triangles by the finite-stage description, hence are exact (014V).
4. The unit comparison gives F[E,u] = [E,F_E(u)]. Thus the inclusion composites have
   the identity comparison, and their shift squares both equal [E,c_E,X]. The image
   of a stage distinguished triangle is distinguished by exactness of F_E and J_E.
   Naturality of the shift comparison transports triangle isomorphisms, so the assumed
   isomorphism-closure description proves exactness on every distinguished triangle.
5. Each half is the isomorphism closure of a stage half. Stage t-exactness therefore
   proves preservation of both halves by F and by each J. Their shift comparisons and
   inverse comparisons extend preservation to every integer cutoff (def-weil-t-structure).
6. The extension arrow is the class of the identity at the larger field. Evaluating the
   representative formula on it gives the class of b. This proves the displayed extension
   formula; naturality, the shift square and successive-extension compatibility are
   respectively naturality of b, its assumed shift square and its coherent tower equation.
-/
theorem tExactPairDescent
    (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A B : ExactPairDiagram.{w, u, v} (Padic.FiniteCoefficientFields l Ω))
    (RA : PairStructure A.toDiagram) (RB : PairStructure B.toDiagram)
    [HasShift RA.Obj ℤ] [HasZeroObject RA.Obj]
    [∀ n : ℤ, (shiftFunctor RA.Obj n).Additive]
    [Pretriangulated RA.Obj] [IsTriangulated RA.Obj]
    [HasShift RB.Obj ℤ] [HasZeroObject RB.Obj]
    [∀ n : ℤ, (shiftFunctor RB.Obj n).Additive]
    [Pretriangulated RB.Obj] [IsTriangulated RB.Obj]
    (P : ExactPairPresentation A RA) (Q : ExactPairPresentation B RB)
    (Φ : Family A.toDiagram B.toDiagram) (hb : Φ.Coherent)
    (c : ∀ i, shiftFunctor (A.C i) (1 : ℤ) ⋙ Φ.φ i ≅
      Φ.φ i ⋙ shiftFunctor (B.C i) (1 : ℤ))
    (hExact : ∀ i (T : Triangle (A.C i)), T ∈ distTriang (A.C i) →
      triangleImageOne (Φ.φ i) (c i) T ∈ distTriang (B.C i))
    (hLE : ∀ i (X : A.C i), (A.t i).le 0 X → (B.t i).le 0 ((Φ.φ i).obj X))
    (hGE : ∀ i (X : A.C i), (A.t i).ge 0 X → (B.t i).ge 0 ((Φ.φ i).obj X))
    (hShift : ∀ {i j} (h : i ≤ j) (X : A.C i),
      (B.U h).map ((c i).hom.app X) ≫ (B.s h).hom.app ((Φ.φ i).obj X) ≫
          ((Φ.b h).hom.app X)⟦(1 : ℤ)⟧' =
        (Φ.b h).hom.app (X⟦(1 : ℤ)⟧) ≫ (Φ.φ j).map ((A.s h).hom.app X) ≫
          (c j).hom.app ((A.U h).obj X)) :
    ∃ F : RA.Obj ⥤ RB.Obj, IsDescent RA RB Φ F ∧
      ∃ γ : shiftFunctor RA.Obj (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor RB.Obj (1 : ℤ),
        (∀ X : RA.Obj, HEq (γ.hom.app X) ((Q.J X.1).map ((c X.1).hom.app X.2))) ∧
        (∀ T : Triangle RA.Obj, T ∈ distTriang RA.Obj →
          triangleImageOne F γ T ∈ distTriang RB.Obj) ∧
        (∀ (n : ℤ) (X : RA.Obj),
          (P.t.le n X → Q.t.le n (F.obj X)) ∧ (P.t.ge n X → Q.t.ge n (F.obj X))) ∧
        (∀ i, (P.J i).Additive ∧ (Q.J i).Additive ∧
          (∀ T : Triangle (A.C i), T ∈ distTriang (A.C i) →
            triangleImageOne (P.J i) (P.j i) T ∈ distTriang RA.Obj) ∧
          (∀ T : Triangle (B.C i), T ∈ distTriang (B.C i) →
            triangleImageOne (Q.J i) (Q.j i) T ∈ distTriang RB.Obj) ∧
          (∀ (n : ℤ) (X : A.C i),
            ((A.t i).le n X → P.t.le n ((P.J i).obj X)) ∧
            ((A.t i).ge n X → P.t.ge n ((P.J i).obj X))) ∧
          (∀ (n : ℤ) (X : B.C i),
            ((B.t i).le n X → Q.t.le n ((Q.J i).obj X)) ∧
            ((B.t i).ge n X → Q.t.ge n ((Q.J i).obj X)))) ∧
        (∀ i, P.J i ⋙ F = Φ.φ i ⋙ Q.J i) ∧
        (∀ i, ∃ κ : P.J i ⋙ F ≅ Φ.φ i ⋙ Q.J i,
          (∀ X : A.C i, HEq (κ.hom.app X) (𝟙 ((Q.J i).obj ((Φ.φ i).obj X)))) ∧
          (∀ X : A.C i,
            F.map ((P.j i).hom.app X) ≫ γ.hom.app ((P.J i).obj X) ≫
                (κ.hom.app X)⟦(1 : ℤ)⟧' =
              κ.hom.app (X⟦(1 : ℤ)⟧) ≫ (Q.J i).map ((c i).hom.app X) ≫
                (Q.j i).hom.app ((Φ.φ i).obj X))) ∧
        (∀ {i j} (h : i ≤ j) (X : A.C i),
          HEq (F.map (RA.repr (X := ⟨i, X⟩) (Y := ⟨j, (A.U h).obj X⟩)
            ⟨j, h, le_refl _,
              (eqToIso (congrArg (fun G : A.C j ⥤ A.C j ↦ G.obj ((A.U h).obj X))
                (A.unit j))).inv⟩))
            (RB.repr (X := Φ.obj ⟨i, X⟩) (Y := Φ.obj ⟨j, (A.U h).obj X⟩)
              ⟨j, h, le_refl _, (Φ.b h).hom.app X ≫
                (eqToIso (congrArg (fun G : B.C j ⥤ B.C j ↦
                  G.obj ((Φ.φ j).obj ((A.U h).obj X))) (B.unit j))).inv⟩)) := by
  obtain ⟨F, hF⟩ := descent_exists l Ω A.toDiagram B.toDiagram RA RB
    P.canonical Q.canonical Φ hb
  let γ : shiftFunctor RA.Obj (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor RB.Obj (1 : ℤ) :=
    NatIso.ofComponents (shiftComponent A B RA RB P Q Φ F hF c)
      (shiftComponent_naturality A B RA RB P Q Φ F hF c hShift)
  have hγ : ∀ X : RA.Obj,
      HEq (γ.hom.app X) ((Q.J X.1).map ((c X.1).hom.app X.2)) :=
    shiftComponent_hom A B RA RB P Q Φ F hF c
  refine ⟨F, hF, γ, hγ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact descent_exact A B RA RB P Q Φ hb F hF c γ hγ hExact
  · exact descent_halves A B RA RB P Q Φ hb F hF γ hLE hGE
  · intro i
    exact ⟨stage_additive A RA P i, stage_additive B RB Q i,
      stage_exact A RA P i, stage_exact B RB Q i,
      stage_halves A RA P i, stage_halves B RB Q i⟩
  · exact descent_stage A B RA RB P Q Φ hb F hF
  · exact descent_stage_shift A B RA RB P Q Φ hb F hF c γ hγ
  · intro i j h X
    exact (hF.map _).trans (heq_of_eq (congrArg RB.repr (family_rep_extension Φ hb h X)))

end CategoryTheory.CommonStage
