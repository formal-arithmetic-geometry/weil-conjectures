/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluingData

import all WeilConjectures.SixFunctors.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SmoothPurityStrictOpenTensorCoordinates
import WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.SemilinearSystemIsoAssembly

/-! # Ordinary graph coordinates for fixed tower operations

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs, ordinary section-model
identification (blueprint: lem-sp-global-graph-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local implicit_reducible] VaryingRing.coefficientTransition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev SS (T : Scheme.{u})
    (σ : ∀ n, SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) :=
  SemilinearSections.Systems.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T) σ

private noncomputable abbrev EE (T : Scheme.{u})
    (σ : ∀ n, SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (ProEt.topology T) (SpTowerShriek.B l E T) σ

private noncomputable abbrev σgraph (T : Scheme.{u}) :=
  SemilinearProperOpen.transition (graphRings l E) (graphTransitions l E) T

private noncomputable def graphPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f ≅
      VaryingRing.push (graphRings l E) (graphTransitions l E) f :=
  SheafOfModules.pushforwardCongr
    (SemilinearProperOpen.coefficientMap_forget_eq (graphRings l E) (graphTransitions l E) f)

-- Keep the adjacent maps abstract until the equality transport is performed once.
set_option maxHeartbeats 2000000 in
-- The section pins compare functors on large coefficient-system categories.
private structure OrdinaryModel
    (σ : ∀ T : Scheme.{u}, ∀ n,
      SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n) where
  presentation : ∀ T : Scheme.{u}, SS l E T (σ T) ≌
    SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T
  [additive : ∀ T, (presentation T).functor.Additive]
  [inverseAdditive : ∀ T, (presentation T).inverse.Additive]
  sections : ∀ T (M : SS l E T (σ T)) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.obj M).val.obj V) (M.val.obj V)
  restrictions : ∀ T (M : SS l E T (σ T)) {V W : (ℕ × T.ProEt)ᵒᵖ} (a : V ⟶ W),
    HEq (((presentation T).functor.obj M).val.map a) (M.val.map a)
  morphisms : ∀ T {M N : SS l E T (σ T)} (a : M ⟶ N) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((presentation T).functor.map a).val.app V) (a.val.app V)
  unit_sections : ∀ T (M : SS l E T (σ T)) (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).unitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  counit_sections : ∀ T
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) T)
    (V : (ℕ × T.ProEt)ᵒᵖ),
    HEq (fun x ↦ ((presentation T).counitIso.hom.app M).val.app V x)
      (fun x : M.val.obj V ↦ x)
  push : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (SS l E X (σ X) ⥤ SS l E Y (σ Y))
  evalP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    push f ⋙ EE l E Y (σ Y) n ≅
      EE l E X (σ X) n ⋙ proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  horizontal : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : SS l E X (σ X))
    {m n : ℕ} (h : n ≤ m) (V : Y.ProEtᵒᵖ)
    (x : ((EE l E Y (σ Y) m).obj ((push f).obj M)).val.obj V),
    ((evalP f n).hom.app M).val.app V
        (SpTowerShriek.HS l E Y (σ Y) h ((push f).obj M) V x) =
      SpTowerShriek.HS l E X (σ X) h M (SpTowerShriek.chart f V)
        (((evalP f m).hom.app M).val.app V x)
  comparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : SS l E X (σ X) ⥤ SS l E Y (σ Y)) (_d : G ≅ push f),
    (presentation X).inverse ⋙ G ⋙ (presentation Y).functor ≅
      SemilinearProperOpen.push (graphRings l E) (graphTransitions l E) f
  comparison_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : SS l E X (σ X) ⥤ SS l E Y (σ Y)) (d : G ≅ push f)
    (M : SemilinearProperOpen.Modules (graphRings l E) (graphTransitions l E) X)
    (n : ℕ) (V : Y.ProEtᵒᵖ),
    HEq (fun x ↦ ((comparison f G d).hom.app M).val.app (op (n, V.unop)) x)
      (fun x ↦ (((EE l E Y (σ Y) n).map
        (d.hom.app ((presentation X).inverse.obj M)) ≫
        (evalP f n).hom.app ((presentation X).inverse.obj M)).val.app V x))

attribute [local instance] OrdinaryModel.additive OrdinaryModel.inverseAdditive

set_option maxHeartbeats 2000000 in
-- Equality transport identifies the full coefficient-system presentation.
private noncomputable def ordinaryModel
    (σ : ∀ T : Scheme.{u}, ∀ n,
      SpTowerShriek.B l E T (n + 1) ⟶ SpTowerShriek.B l E T n)
    (hσ : σ = σgraph l E) : OrdinaryModel l E σ := by
  subst σ
  refine {
    presentation := fun _ ↦ CategoryTheory.Equivalence.refl
    additive := fun _ ↦ { map_add := by intros; rfl }
    inverseAdditive := fun _ ↦ { map_add := by intros; rfl }
    sections := fun _ _ _ ↦ HEq.rfl
    restrictions := fun _ _ _ _ _ ↦ HEq.rfl
    morphisms := fun _ _ _ _ _ ↦ HEq.rfl
    unit_sections := fun _ _ _ ↦ HEq.rfl
    counit_sections := fun _ _ _ ↦ HEq.rfl
    push := fun f ↦ VaryingRing.push (graphRings l E) (graphTransitions l E) f
    evalP := fun f n ↦ VaryingRing.moduleEvalP (graphRings l E) (graphTransitions l E) f n
    horizontal := fun {X Y} f M {m n} h V x ↦
      SpTowerShriek.canonicalPushHorizontal (graphRings l E) (graphTransitions l E) f M h V x
    comparison := fun f G d ↦
      Functor.leftUnitor _ ≪≫ Functor.rightUnitor _ ≪≫ d ≪≫ (graphPushIso l E f).symm
    comparison_sections := ?_ }
  intro X Y f G d M n V
  apply heq_of_eq
  funext x
  change ((d.hom.app M).val.app (op (n, V.unop)) x) =
    ((VaryingRing.moduleEvalP (graphRings l E) (graphTransitions l E) f n).hom.app M).val.app V
      ((d.hom.app M).val.app (op (n, V.unop)) x)
  exact ((VaryingRing.moduleEvalP_existsUnique
    (graphRings l E) (graphTransitions l E) f n).choose_spec.1 M V.unop _).symm

private theorem tau_graph : SpTowerShriek.tau l E = σgraph l E := by
  funext T n
  simp only [SpTowerShriek.tau, spCoefficientCommRings,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private noncomputable def pushLevelIso (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    (c : OrdinaryModel l E (SpTowerShriek.tau l E)) (M : SpTowerShriek.S l E X) (n : ℕ) :
    (SpTowerShriek.ev l E Y n).obj (g.push.obj M) ≅
      (SpTowerShriek.ev l E Y n).obj ((c.push f).obj M) :=
  (g.ordinaryPushEvaluation n).app M ≪≫ ((c.evalP f n).app M).symm

set_option maxHeartbeats 2000000 in
-- Cancellation compares horizontal morphisms on large module-sheaf categories.
private theorem pushLevelIso_horizontal (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (c : OrdinaryModel l E (SpTowerShriek.tau l E))
    (M : SpTowerShriek.S l E X) {m n : ℕ} (h : n ≤ m) :
    (SpTowerShriek.horizontal l E Y h).app (g.push.obj M) ≫
        (SpTowerShriek.restrict l E Y h).map (pushLevelIso l E b g c M n).hom =
      (pushLevelIso l E b g c M m).hom ≫
        (SpTowerShriek.horizontal l E Y h).app ((c.push f).obj M) := by
  have hd (k : ℕ) : (pushLevelIso l E b g c M k).hom ≫ (c.evalP f k).hom.app M =
      (g.ordinaryPushEvaluation k).hom.app M := by
    simp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono ((SpTowerShriek.restrict l E Y h).map ((c.evalP f n).hom.app M))).mp
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hd]
  ext V x
  have hg := SpTowerShriek.push_horizontal l E f b g M h V x
  have hc := c.horizontal f M h V ((pushLevelIso l E b g c M m).hom.val.app V x)
  have hm := congrArg (fun a ↦ a.val.app V x) (hd m)
  change ((c.evalP f m).hom.app M).val.app V
    ((pushLevelIso l E b g c M m).hom.val.app V x) =
      ((g.ordinaryPushEvaluation m).hom.app M).val.app V x at hm
  rw [hm] at hc
  change ((g.ordinaryPushEvaluation n).hom.app M).val.app V
      (SpTowerShriek.HS l E Y (SpTowerShriek.tau l E Y) h (g.push.obj M) V x) =
    ((c.evalP f n).hom.app M).val.app V
      (SpTowerShriek.HS l E Y (SpTowerShriek.tau l E Y) h ((c.push f).obj M) V
        ((pushLevelIso l E b g c M m).hom.val.app V x))
  exact hg.trans hc.symm

set_option maxHeartbeats 2000000 in
-- Assemble the level isomorphisms and check their naturality on every section.
private theorem pushIso_exists (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (c : OrdinaryModel l E (SpTowerShriek.tau l E)) :
    ∃ d : g.push ≅ c.push f, ∀ (M : SpTowerShriek.S l E X) (n : ℕ),
      (SpTowerShriek.ev l E Y n).map (d.hom.app M) =
        (pushLevelIso l E b g c M n).hom := by
  have hc (M : SpTowerShriek.S l E X) :=
    SemilinearSections.systemIsoOfEvaluation_exists.{u + 1, u, u + 1}
      (ProEt.topology Y) (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
      (pushLevelIso l E b g c M) (fun h ↦ pushLevelIso_horizontal l E b g c M h)
  choose d hd using hc
  refine ⟨NatIso.ofComponents d (fun {M N} a ↦ ?_), hd⟩
  ext V x
  have hn := (g.ordinaryPushEvaluation V.unop.1).hom.naturality a
  have hv := (c.evalP f V.unop.1).inv.naturality a
  have hs : (SpTowerShriek.ev l E Y V.unop.1).map (g.push.map a ≫ (d N).hom) =
      (SpTowerShriek.ev l E Y V.unop.1).map ((d M).hom ≫ (c.push f).map a) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hd, hd]
    dsimp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    dsimp only [Functor.comp_map] at hn hv
    rw [← Category.assoc, hn, Category.assoc, hv, Category.assoc]
  exact congrArg (fun a ↦ a.val.app (op V.unop.2) x) hs

/-- For the specified base and operations, ordinary graph coordinates preserve sections
and identify ordinary direct image with its graph model, with exactly the supplied
ordinary push-evaluation functions.

Source: blueprint gluing proof, Local pairs, ordinary section-model identification;
`GraphCoordinates` in the gluing interfaces (blueprint: lem-sp-global-graph-coordinates).

Proof:
1. Retain b and o. The two coefficient families are the same constant ring sheaves
of ULift of R_n, and their adjacent maps are constant sheaf applied to the same lifted
quotient map. Transport across these equalities and use the identity equivalence of
module sheaves on the vertical sequence site. Both functors preserve addition and all
section modules, restrictions, horizontal transitions and morphism components. Their
unit and counit are identity functions on sections.
2. For f, finite direct image commutes on sections with coefficient restriction: both
scalar actions use the canonical constant-section ring map, whose naturality in the
quotient map identifies them.
3. Write a_n and d_n for the supplied ordinary pull and push evaluations. By
SpTowerShriek.geometry_unit_evaluation, the evaluated system unit followed by d_n
and the finite push of a_n is the finite unit. For M = PN, put
k_n = a_n.inv followed by the evaluated system counit. Its finite adjunct is d_n:
substitute the unit formula, cancel a_n with its inverse, use naturality of d_n,
and apply the system adjunction triangle identity.
4. Conjugate the horizontal transition of LM by a_m.inv and a_n to obtain s.
Geometry.ordinaryUnitTransition says its finite m-adjunct is the original transition
followed by the finite n-unit. Naturality of transposition and step 3 identify the
adjunct of s followed by coefficient restriction of k_n with the original transition
followed by coefficient restriction of d_n.
5. Naturality of the system counit identifies that composite before transposition
with k_m followed by the transition of N. Transposing now gives the horizontal
compatibility square for the specified d_n at every pair of indices.
6. Define the push comparison at (n,V) to be exactly d_n at V. Its vertical
naturality and linearity come from d_n; its horizontal naturality is step 5. Every
sequence-site arrow factors into a vertical and a horizontal arrow. The inverse
components of d_n obey the same squares by cancellation, giving the inverse system
map. Naturality in N gives the natural isomorphism of ordinary push functors.
7. Combine it with the presentations of step 1. Every intervening section
identification, unit and counit is the identity function, so push_evaluation is
precisely the heterogeneous equality of the component function with that of d_n.
These are all fields of GraphCoordinates for the original b and o. -/
theorem nonempty_graphCoordinates (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b) :
    Nonempty (GraphCoordinates l E b o) := by
  classical
  let c := ordinaryModel l E (SpTowerShriek.tau l E) (tau_graph l E)
  let d {X Y : Scheme.{u}} (f : X ⟶ Y) : (o.geometry f).push ≅ c.push f :=
    (pushIso_exists l E b (o.geometry f) c).choose
  have hd {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (pushIso_exists l E b (o.geometry f) c).choose_spec
  refine ⟨{
    presentation := c.presentation
    sections := c.sections
    restrictions := c.restrictions
    morphisms := c.morphisms
    unit_sections := c.unit_sections
    counit_sections := c.counit_sections
    push := fun {X Y} f ↦ c.comparison f (o.geometry f).push (d f)
    push_evaluation := ?_ }⟩
  intro X Y f M n V
  apply (c.comparison_sections f (o.geometry f).push (d f) M n V).trans
  have hh := hd f ((c.presentation X).inverse.obj M) n
  rw [hh]
  simp only [pushLevelIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerGluing
