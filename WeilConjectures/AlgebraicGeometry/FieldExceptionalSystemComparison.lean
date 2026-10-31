/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemIso
import WeilConjectures.AlgebraicGeometry.FieldExceptionalNormalizedAdjoints
import WeilConjectures.AlgebraicGeometry.FieldExceptionalFiniteCompatibility
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: lem-sp-field-exceptional-system-comparison).

Natural-number level n means exponent n+1. All morphisms are in ordinary derived
categories of strict systems, in the dependency's section-preserving coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] normalized FieldShriekSystem.iso scalarAssoc scalarUnit
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] FieldShriekSystem.comparison FieldShriekSystem.coefficientMap
attribute [local irreducible] scalarExtensionFunctor reductionCtfCompactSupport
attribute [local irreducible] sourceEvaluation targetEvaluation finiteComponent
attribute [local irreducible] SemilinearSections.derivedTransition

attribute [local semireducible] invertibleLaw naturalityLaw counitLaw unitLaw evaluationLaw
  rightReductionLaw mixedLaw transitionLaw compositionLaw identityLaw

private def supportComparison (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F : Index P} (h : E ≤ F) :
    support P D c a E ⋙ scalar P D a h Y ≅
      scalar P D a h X ⋙ support P D c a F :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((FieldShriekSystem.iso P D c b h).app M))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (FieldShriekSystem.iso P D c b h).hom.naturality v)


private theorem supportComparison_hom (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F : Index P} (h : E ≤ F) (M : N P D E X) :
    (supportComparison P D c b a h).hom.app M =
      ObjectProperty.homMk ((FieldShriekSystem.iso P D c b h).hom.app M) := rfl

private theorem supportComparison_inv (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F : Index P} (h : E ≤ F) (M : N P D E X) :
    (supportComparison P D c b a h).inv.app M =
      ObjectProperty.homMk ((FieldShriekSystem.iso P D c b h).inv.app M) := rfl

private theorem supportComparison_hom_hom (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F : Index P} (h : E ≤ F) (M : N P D E X) :
    ((supportComparison P D c b a h).hom.app M).hom =
      (FieldShriekSystem.comparison P D h c).app M.obj := by
  unfold supportComparison FieldShriekSystem.iso
  rfl

private theorem scalar_map_hom (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (a : Domains P D c) {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (hT : T = X ∨ T = Y) {M K : N P D E T} (v : M ⟶ K) :
    ((scalar P D a h T hT).map v).hom = (D.scalars E F h T).T.map v.hom := rfl

private theorem scalar_obj_obj (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (a : Domains P D c) {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (hT : T = X ∨ T = Y) (M : N P D E T) :
    ((scalar P D a h T hT).obj M).obj = (D.scalars E F h T).T.obj M.obj := rfl

private theorem support_obj_obj (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (a : Domains P D c) (E : Index P) (M : N P D E X) :
    ((support P D c a E).obj M).obj =
      (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M.obj :=
  rfl

private theorem support_map_hom (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (a : Domains P D c) (E : Index P)
    {M K : N P D E X} (v : M ⟶ K) :
    ((support P D c a E).map v).hom =
      (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).map v.hom :=
  rfl

attribute [local irreducible] supportComparison

private theorem transpose_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {M : C} {K : D} (v : F.obj M ⟶ K) :
    F.map (adj.homEquiv M K v) ≫ adj.counit.app K = v :=
  (adj.homEquiv M K).symm_apply_apply v

private theorem counitComparison_natural
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {T : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (b : L ⋙ T ≅ S ⋙ L') (K M : D) (v : K ⟶ M) :
    S.map (R.map v) ≫ adj'.homEquiv _ _
        (b.inv.app (R.obj M) ≫ T.map (adj.counit.app M)) =
      adj'.homEquiv _ _ (b.inv.app (R.obj K) ≫ T.map (adj.counit.app K)) ≫
        R'.map (T.map v) := by
  apply adj'.homEquiv_naturality_left_square
  have hb : L'.map (S.map (R.map v)) ≫ b.inv.app (R.obj M) =
      b.inv.app (R.obj K) ≫ T.map (L.map (R.map v)) := b.inv.naturality _
  have hn : L.map (R.map v) ≫ adj.counit.app M = adj.counit.app K ≫ v :=
    adj.counit.naturality v
  rw [← Category.assoc, hb, Category.assoc, ← T.map_comp, hn]
  rw [T.map_comp, Category.assoc]

private def CounitSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {T : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (b : L ⋙ T ≅ S ⋙ L') (c : R ⋙ S ⟶ T ⋙ R') : Prop :=
  ∀ K, b.hom.app (R.obj K) ≫ L'.map (c.app K) ≫
    adj'.counit.app (T.obj K) = T.map (adj.counit.app K)

private theorem counitSquare_of_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {S : C ⥤ C'} {T : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (b : L ⋙ T ≅ S ⋙ L') (c : R ⋙ S ⟶ T ⋙ R')
    (hc : ∀ K, L'.map (c.app K) ≫ adj'.counit.app (T.obj K) =
      b.inv.app (R.obj K) ≫ T.map (adj.counit.app K)) :
    CounitSquare adj adj' b c := by
  intro K
  rw [hc]
  exact Iso.hom_inv_id_app_assoc b _ _

private theorem counitComparison_unit
    {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁]
    [Category C₂] [Category D₂]
    {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (S : C₁ ⥤ C₂) (T : D₁ ⥤ D₂)
    (b : F₁ ⋙ T ⟶ S ⋙ F₂) (c : G₁ ⋙ S ⟶ T ⋙ G₂)
    (hc : ∀ K, b.app (G₁.obj K) ≫ F₂.map (c.app K) ≫
      a₂.counit.app (T.obj K) = T.map (a₁.counit.app K))
    (M : C₁) [Epi (b.app M)] :
    S.map (a₁.unit.app M) ≫ c.app (F₁.obj M) ≫ G₂.map (b.app M) =
      a₂.unit.app (S.obj M) := by
  apply (a₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  have tr₁ : F₁.map (a₁.unit.app M) ≫ a₁.counit.app (F₁.obj M) = 𝟙 _ :=
    a₁.left_triangle_components M
  have tr₂ : F₂.map (a₂.unit.app (S.obj M)) ≫
      a₂.counit.app (F₂.obj (S.obj M)) = 𝟙 _ := a₂.left_triangle_components _
  rw [tr₂]
  apply (cancel_epi (b.app M)).mp
  have hn : F₂.map (G₂.map (b.app M)) ≫ a₂.counit.app (F₂.obj (S.obj M)) =
      a₂.counit.app (T.obj (F₁.obj M)) ≫ b.app M := a₂.counit.naturality (b.app M)
  have hb : T.map (F₁.map (a₁.unit.app M)) ≫ b.app (G₁.obj (F₁.obj M)) =
      b.app M ≫ F₂.map (S.map (a₁.unit.app M)) := b.naturality (a₁.unit.app M)
  calc
    _ = (b.app M ≫ F₂.map (S.map (a₁.unit.app M))) ≫
        F₂.map (c.app (F₁.obj M)) ≫
        (F₂.map (G₂.map (b.app M)) ≫ a₂.counit.app (F₂.obj (S.obj M))) := by
          simp only [Category.assoc]
    _ = (T.map (F₁.map (a₁.unit.app M)) ≫ b.app (G₁.obj (F₁.obj M))) ≫
        F₂.map (c.app (F₁.obj M)) ≫
        (a₂.counit.app (T.obj (F₁.obj M)) ≫ b.app M) := by rw [← hb, hn]
    _ = T.map (F₁.map (a₁.unit.app M)) ≫
        (b.app (G₁.obj (F₁.obj M)) ≫ F₂.map (c.app (F₁.obj M)) ≫
          a₂.counit.app (T.obj (F₁.obj M))) ≫ b.app M := by
          simp only [Category.assoc]
    _ = _ := by
          rw [hc, ← T.map_comp_assoc, tr₁, T.map_id]
          simp

private theorem transpose_naturality
    {C A B : Type*} [Category C] [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (F : C ⥤ A) (G : C ⥤ B) (t : F ⟶ G ⋙ R) {K M : C} (v : K ⟶ M) :
    L.map (F.map v) ≫ (adj.homEquiv _ _).symm (t.app M) =
      (adj.homEquiv _ _).symm (t.app K) ≫ G.map v :=
  adj.homEquiv_naturality_right_square _ _ _ _ (t.naturality v)

private theorem counitComparison_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (S : C ⥤ C) (T : D ⥤ D) (b : L ⋙ T ≅ S ⋙ L)
    (ux : S ≅ 𝟭 C) (uy : T ≅ 𝟭 D)
    (hb : ∀ M, b.hom.app M ≫ L.map (ux.hom.app M) = uy.hom.app (L.obj M))
    (c : R ⋙ S ⟶ T ⋙ R)
    (hc : ∀ K, L.map (c.app K) ≫ adj.counit.app (T.obj K) =
      b.inv.app (R.obj K) ≫ T.map (adj.counit.app K)) (K : D) :
    c.app K ≫ R.map (uy.hom.app K) = ux.hom.app (R.obj K) := by
  apply (adj.homEquiv (S.obj (R.obj K)) K).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn : L.map (R.map (uy.hom.app K)) ≫ adj.counit.app K =
      adj.counit.app (T.obj K) ≫ uy.hom.app K := adj.counit.naturality _
  rw [hn]
  rw [← Category.assoc, hc, Category.assoc]
  have hy : T.map (adj.counit.app K) ≫ uy.hom.app K =
      uy.hom.app (L.obj (R.obj K)) ≫ adj.counit.app K := uy.hom.naturality _
  rw [hy, ← hb]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj]
  rw [Category.id_comp]


attribute [local irreducible] Adjunction.homEquiv
attribute [local irreducible] Adjoints

private theorem component_counit (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : counitLaw P D c b a A := by
  unfold counitLaw
  intro E F h K
  unfold component
  exact transpose_counit (G := A.right F) (A.adj F) _

attribute [local irreducible] component

private theorem component_natural (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : naturalityLaw P D c b a A := by
  unfold naturalityLaw
  intro E F h K L v
  have hn := counitComparison_natural (R := A.right E) (R' := A.right F)
    (S := scalar P D a h X (.inl rfl)) (T := scalar P D a h Y (.inr rfl))
    (A.adj E) (A.adj F) (supportComparison P D c b a h) K L v
  rw [supportComparison_inv P D c b a h ((A.right E).obj K),
    supportComparison_inv P D c b a h ((A.right E).obj L)] at hn
  unfold component
  apply ObjectProperty.hom_ext
  exact congrArg (fun z ↦ z.hom) hn

private theorem systemReduction_natural (E : Index P) (T : Scheme.{u}) {m n : ℕ}
    (v : m ≤ n) (q : QuotientRestriction P E T v)
    {K L : SpTowerShriek.D P.coefficients.l E.val T} (z : K ⟶ L) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) T).map
        ((SpTowerShriek.Ev P.coefficients.l E.val T n).map z) ≫
      systemReduction P E T v q L =
    systemReduction P E T v q K ≫
      (SpTowerShriek.Ev P.coefficients.l E.val T m).map z := by
  have := preservesFiniteLimits_of_natIso q.ordinary
  have := preservesFiniteColimits_of_natIso q.ordinary
  unfold systemReduction
  exact transpose_naturality
    (finiteScalarAdjunction (SpTowerCalculus.quotient P.coefficients.l E.val v) T)
    (SpTowerShriek.Ev P.coefficients.l E.val T n)
    (SpTowerShriek.Ev P.coefficients.l E.val T m)
    ((SemilinearSections.derivedTransition (Scheme.ProEt.topology T)
      (SpTowerShriek.B P.coefficients.l E.val T)
      (SpTowerShriek.tau P.coefficients.l E.val T) v) ≫
        Functor.whiskerLeft (SpTowerShriek.Ev P.coefficients.l E.val T m)
          (Functor.mapDerivedCategoryNatIso q.ordinary).hom) z

private theorem component_transition (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : transitionLaw P D c b a A := by
  unfold transitionLaw
  intro E F h m n v K
  exact systemReduction_natural P F X v (b.quotientCoordinates F X v)
    (component P D c b a A h K).hom

private theorem counitComparison_composition
    {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Category C₃] [Category D₃]
    {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    {F₃ : C₃ ⥤ D₃} {G₃ : D₃ ⥤ C₃}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃)
    (S₁₂ : C₁ ⥤ C₂) (S₂₃ : C₂ ⥤ C₃) (S₁₃ : C₁ ⥤ C₃)
    (T₁₂ : D₁ ⥤ D₂) (T₂₃ : D₂ ⥤ D₃) (T₁₃ : D₁ ⥤ D₃)
    (ax : S₁₂ ⋙ S₂₃ ⟶ S₁₃) (ay : T₁₂ ⋙ T₂₃ ⟶ T₁₃)
    (b₁₂ : F₁ ⋙ T₁₂ ≅ S₁₂ ⋙ F₂) (b₂₃ : F₂ ⋙ T₂₃ ≅ S₂₃ ⋙ F₃)
    (b₁₃ : F₁ ⋙ T₁₃ ⟶ S₁₃ ⋙ F₃)
    (c₁₂ : G₁ ⋙ S₁₂ ⟶ T₁₂ ⋙ G₂) (c₂₃ : G₂ ⋙ S₂₃ ⟶ T₂₃ ⋙ G₃)
    (c₁₃ : G₁ ⋙ S₁₃ ⟶ T₁₃ ⋙ G₃)
    (h₁₂ : ∀ K, b₁₂.hom.app (G₁.obj K) ≫ F₂.map (c₁₂.app K) ≫
      a₂.counit.app (T₁₂.obj K) = T₁₂.map (a₁.counit.app K))
    (h₂₃ : ∀ K, b₂₃.hom.app (G₂.obj K) ≫ F₃.map (c₂₃.app K) ≫
      a₃.counit.app (T₂₃.obj K) = T₂₃.map (a₂.counit.app K))
    (h₁₃ : ∀ K, b₁₃.app (G₁.obj K) ≫ F₃.map (c₁₃.app K) ≫
      a₃.counit.app (T₁₃.obj K) = T₁₃.map (a₁.counit.app K))
    (hb : ∀ M, ay.app (F₁.obj M) ≫ b₁₃.app M =
      T₂₃.map (b₁₂.hom.app M) ≫ b₂₃.hom.app (S₁₂.obj M) ≫ F₃.map (ax.app M))
    (K : D₁) :
    S₂₃.map (c₁₂.app K) ≫ c₂₃.app (T₁₂.obj K) ≫ G₃.map (ay.app K) =
      ax.app (G₁.obj K) ≫ c₁₃.app K := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Functor.comp_obj]
  apply (cancel_epi (T₂₃.map (b₁₂.hom.app (G₁.obj K)) ≫
    b₂₃.hom.app (S₁₂.obj (G₁.obj K)))).mp
  have hn : T₂₃.map (F₂.map (c₁₂.app K)) ≫ b₂₃.hom.app (G₂.obj (T₁₂.obj K)) =
      b₂₃.hom.app (S₁₂.obj (G₁.obj K)) ≫ F₃.map (S₂₃.map (c₁₂.app K)) :=
    b₂₃.hom.naturality (c₁₂.app K)
  have hn' : F₃.map (G₃.map (ay.app K)) ≫ a₃.counit.app (T₁₃.obj K) =
      a₃.counit.app (T₂₃.obj (T₁₂.obj K)) ≫ ay.app K :=
    a₃.counit.naturality (ay.app K)
  calc
    _ = T₂₃.map (b₁₂.hom.app (G₁.obj K)) ≫
        (b₂₃.hom.app (S₁₂.obj (G₁.obj K)) ≫ F₃.map (S₂₃.map (c₁₂.app K))) ≫
        F₃.map (c₂₃.app (T₁₂.obj K)) ≫
        (F₃.map (G₃.map (ay.app K)) ≫ a₃.counit.app (T₁₃.obj K)) := by
          simp only [Category.assoc]
    _ = T₂₃.map (b₁₂.hom.app (G₁.obj K)) ≫
        (T₂₃.map (F₂.map (c₁₂.app K)) ≫ b₂₃.hom.app (G₂.obj (T₁₂.obj K))) ≫
        F₃.map (c₂₃.app (T₁₂.obj K)) ≫
        (a₃.counit.app (T₂₃.obj (T₁₂.obj K)) ≫ ay.app K) := by rw [← hn, hn']
    _ = T₂₃.map (b₁₂.hom.app (G₁.obj K)) ≫ T₂₃.map (F₂.map (c₁₂.app K)) ≫
        (b₂₃.hom.app (G₂.obj (T₁₂.obj K)) ≫ F₃.map (c₂₃.app (T₁₂.obj K)) ≫
          a₃.counit.app (T₂₃.obj (T₁₂.obj K))) ≫ ay.app K := by
          simp only [Category.assoc]
    _ = T₂₃.map (b₁₂.hom.app (G₁.obj K)) ≫ T₂₃.map (F₂.map (c₁₂.app K)) ≫
        T₂₃.map (a₂.counit.app (T₁₂.obj K)) ≫ ay.app K := by rw [h₂₃]
    _ = T₂₃.map (b₁₂.hom.app (G₁.obj K) ≫ F₂.map (c₁₂.app K) ≫
        a₂.counit.app (T₁₂.obj K)) ≫ ay.app K := by simp only [Functor.map_comp,
          Category.assoc]
    _ = ay.app (F₁.obj (G₁.obj K)) ≫ T₁₃.map (a₁.counit.app K) := by
          rw [h₁₂]
          exact ay.naturality (a₁.counit.app K)
    _ = (ay.app (F₁.obj (G₁.obj K)) ≫ b₁₃.app (G₁.obj K)) ≫
        F₃.map (c₁₃.app K) ≫ a₃.counit.app (T₁₃.obj K) := by rw [Category.assoc, h₁₃]
    _ = _ := by rw [hb]; simp only [Category.assoc]

private def scalarComparison (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F L : Index P} (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u})
    (hT : T = X ∨ T = Y) :
    scalar P D a h T hT ⋙ scalar P D a k T hT ≅ scalar P D a (h.trans k) T hT :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _
      ((scalarAssoc P D h k T (b.coefficientComposition E F L h k T)).app M.obj))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (scalarAssoc P D h k T
        (b.coefficientComposition E F L h k T)).hom.naturality v.hom)

private def scalarIdentity (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (E : Index P) (T : Scheme.{u}) (hT : T = X ∨ T = Y) :
    scalar P D a (E := E) (F := E) le_rfl T hT ≅ 𝟭 (N P D E T) :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _
      ((scalarUnit P D E T (b.coefficientIdentity E T)).app M.obj))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (scalarUnit P D E T (b.coefficientIdentity E T)).hom.naturality v.hom)

private theorem scalarComparison_hom_hom (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    {E F L : Index P} (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u})
    (hT : T = X ∨ T = Y) (M : N P D E T) :
    ((scalarComparison P D c b a h k T hT).hom.app M).hom =
      (scalarAssoc P D h k T (b.coefficientComposition E F L h k T)).hom.app M.obj := rfl

private theorem scalarIdentity_hom_hom (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (E : Index P) (T : Scheme.{u}) (hT : T = X ∨ T = Y) (M : N P D E T) :
    ((scalarIdentity P D c b a E T hT).hom.app M).hom =
      (scalarUnit P D E T (b.coefficientIdentity E T)).hom.app M.obj := rfl

private def exceptionalComparison (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) {E F : Index P} (h : E ≤ F) :
    A.right E ⋙ scalar P D a h X ⟶ scalar P D a h Y ⋙ A.right F where
  app := component P D c b a A h
  naturality := fun _ _ v ↦ component_natural P D c b a A E F h v

private theorem support_component_counit (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) {E F : Index P} (h : E ≤ F) :
    CounitSquare (R := A.right E) (R' := A.right F) (A.adj E) (A.adj F)
      (supportComparison P D c b a h) (exceptionalComparison P D c b a A h) := by
  apply counitSquare_of_transpose
  intro K
  rw [supportComparison_inv P D c b a h ((A.right E).obj K)]
  apply ObjectProperty.hom_ext
  exact congrArg (fun z ↦ z.hom) ((component_counit P D c b a A) E F h K)

private theorem component_unit (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : unitLaw P D c b a A := by
  unfold unitLaw
  intro E F h M
  have hu := counitComparison_unit (G₁ := A.right E) (G₂ := A.right F)
    (A.adj E) (A.adj F) (scalar P D a h X) (scalar P D a h Y)
    (supportComparison P D c b a h).hom (exceptionalComparison P D c b a A h)
    (support_component_counit P D c b a A h) M
  rw [supportComparison_hom P D c b a h M] at hu
  apply ObjectProperty.hom_ext
  exact congrArg (fun z ↦ z.hom) hu

private theorem component_composition (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : compositionLaw P D c b a A := by
  unfold compositionLaw
  intro E F L h k K
  have hc := counitComparison_composition (G₁ := A.right E) (G₂ := A.right F)
    (G₃ := A.right L) (A.adj E) (A.adj F) (A.adj L)
    (scalar P D a h X (.inl rfl)) (scalar P D a k X (.inl rfl))
    (scalar P D a (h.trans k) X (.inl rfl))
    (scalar P D a h Y (.inr rfl)) (scalar P D a k Y (.inr rfl))
    (scalar P D a (h.trans k) Y (.inr rfl))
    (scalarComparison P D c b a h k X (.inl rfl)).hom
    (scalarComparison P D c b a h k Y (.inr rfl)).hom
    (supportComparison P D c b a h) (supportComparison P D c b a k)
    (supportComparison P D c b a (h.trans k)).hom
    (exceptionalComparison P D c b a A h) (exceptionalComparison P D c b a A k)
    (exceptionalComparison P D c b a A (h.trans k))
    (support_component_counit P D c b a A h)
    (support_component_counit P D c b a A k)
    (support_component_counit P D c b a A (h.trans k))
    (fun M ↦ by
      apply ObjectProperty.hom_ext
      simpa only [Functor.comp_obj, Functor.id_obj, ObjectProperty.FullSubcategory.comp_hom,
        scalar_map_hom,
        support_map_hom, supportComparison_hom_hom, scalarComparison_hom_hom,
        scalar_obj_obj, support_obj_obj] using
        (b.composition E F L h k M.obj M.property).symm) K
  exact congrArg (fun v ↦ v.hom) hc

private theorem component_identity (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) : identityLaw P D c b a A := by
  unfold identityLaw
  intro E K
  have hi := counitComparison_identity (R := A.right E) (A.adj E)
    (scalar P D a (E := E) (F := E) le_rfl X)
    (scalar P D a (E := E) (F := E) le_rfl Y)
    (supportComparison P D c b a le_rfl)
    (scalarIdentity P D c b a E X (.inl rfl))
    (scalarIdentity P D c b a E Y (.inr rfl))
    (fun M ↦ by
      apply ObjectProperty.hom_ext
      simpa only [Functor.comp_obj, Functor.id_obj, ObjectProperty.FullSubcategory.comp_hom,
        support_map_hom,
        supportComparison_hom_hom, scalarIdentity_hom_hom, scalar_obj_obj, support_obj_obj] using
        b.identity E M.obj M.property)
    (exceptionalComparison P D c b a A le_rfl)
    (fun K ↦ by
      rw [supportComparison_inv P D c b a (E := E) (F := E) le_rfl
        ((A.right E).obj K)]
      exact (component_counit P D c b a A) E E le_rfl K) K
  exact congrArg (fun v ↦ v.hom) hi

private theorem isIso_of_conjugate_eq
    {C : Type*} [Category C] {W X Y Z : C} (s : W ≅ X) (t : Y ≅ Z)
    (f : X ⟶ Y) (g : W ⟶ Z) (hg : IsIso g) (h : s.hom ≫ f ≫ t.hom = g) :
    IsIso f := by
  have : IsIso (s.hom ≫ f ≫ t.hom) := h.symm ▸ hg
  have : IsIso (f ≫ t.hom) := IsIso.of_isIso_comp_left s.hom _
  exact IsIso.of_isIso_comp_right _ t.hom

private theorem component_invertible (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (he : evaluationLaw P D c b a A)
    (hi : ∀ (E F : Index P) (h : E ≤ F) (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)),
      IsIso (finiteComponent P D c b a A ((D.coefficients E F h).quotient n) K)) :
    invertibleLaw P D c b a A := by
  unfold invertibleLaw
  intro E F h K
  apply (ObjectProperty.isIso_hom_iff (component P D c b a A h K)).mp
  apply ((D.base F).calculus X).detects (component P D c b a A h K).hom
  intro n
  have hf := hi E F h n ((level P D a E Y n).obj K)
  have : IsIso (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
      ((level P D a E Y n).obj K)).hom :=
    (ObjectProperty.isIso_hom_iff _).mpr hf
  exact isIso_of_conjugate_eq
    (sourceEvaluation P D c b a A h n K).symm (targetEvaluation P D c b a A h n K)
    ((SpTowerShriek.Ev P.coefficients.l F.val X n).map
      (component P D c b a A h K).hom)
    (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
      ((level P D a E Y n).obj K)).hom this (he E F h n K)

/-- The exceptional comparison on coefficient systems is the actual whole-system
counit transpose, with all finite, quotient, unit, counit and coherence laws.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-sp-field-exceptional-system-comparison).

Proof: (1) Finite-free scalar extension preserves normalized constructible towers,
including uniform cohomological and Tor bounds, even for ramified extensions
(lem-sp-field-scalar-normalized-systems). The tower gamma theorem preserves these
domains for both adjoints (det-sp-tower-gamma).
(2) Use the actual tower adjunctions of det-sp-tower-gluing. Apply their Hom bijection
to scalar extension of the counit composed with the inverse proper/open comparison
of lem-sp-field-shriek-system-comparison. This defines component, and naturality
of the Hom bijection proves naturality. Its defining equation is the tower counit law.
(3) Evaluate that equation using the scalar and support evaluations and the
counit-preserving finite right-adjoint comparisons. Uniqueness of the finite transpose
in det-sp-reduction-exceptional gives the displayed finite evaluation. Finite comparison
isomorphisms and det-sp-tower-shriek-levels (3) detect invertibility of the constructed
system arrow, without detecting equality of arbitrary arrows by evaluation.
(4) For n >= m, det-sp-tower-gluing (3) identifies right-adjoint reduction with the
finite quotient mate followed by the right adjoint of the input transition. The two
mixed coefficient paths agree by det-sp-reduction-compatibilities (2); naturality
moves the input transition through the finite comparison. This is the transition
square of the already constructed whole-system map.
(5) Transpose the asserted unit word under the target tower adjunction. Naturality
of the target counit, the defining counit law, and naturality of b give b times the
scalar extension of epsilon_A P_A(eta_A) times b inverse, hence identity by the
triangle identity. Injectivity of the tower Hom bijection gives the unit equation.
(6) For E <= F <= L transpose the composite exceptional word. Use the defining
counit law twice and naturality of the second b. The result is scalar extension of
epsilon_E times the inverse composite b, which is the direct b by its whole-system
cocycle. Injectivity gives composition with the canonical tensor associators.
(7) For identity coefficients the tensor unitor identifies b with identity; the
identity of G_E K and component have the same transpose epsilon_E. Injectivity
gives the identity law. No equality argument uses faithfulness of derived evaluation. -/
theorem field_exceptional_system_comparison
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f) :
    ∃ (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
      (A : Adjoints P D c b a), Nonempty (Laws P D c b a A) :=
  (field_shriek_system_comparison P X Y f d c).elim fun D hb ↦
    hb.elim fun b ↦
      (field_exceptional_normalized_adjoints P X Y f d c D b).elim fun a ha ↦
        ha.elim fun A hr ↦
          (field_exceptional_finite_compatibility P X Y f d c D b a A).elim fun he hmi ↦
            hmi.elim fun hm hi ↦
              ⟨D, b, a, A, ⟨Laws.mk
                (component_invertible P D c b a A he hi)
                (component_natural P D c b a A)
                (component_counit P D c b a A)
                (component_unit P D c b a A) he hr hm
                (component_transition P D c b a A)
                (component_composition P D c b a A)
                (component_identity P D c b a A)⟩⟩

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
