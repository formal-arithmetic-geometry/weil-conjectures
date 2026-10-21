/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.StrictQuotientScalarBalancing
public import Sheaf.CategoryTheory.FlatScalarTowerLimitSquare
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.StrictScalarCompletionUnit
import Sheaf.Paper.StrictScalarOrdinaryAdjunction
import all Sheaf.Paper.CompletedPullbackAdjunction
import all Sheaf.Paper.ConstantCompletionEquivalence

/-! # Completion-unit-normalized scalar comparison of completed adjunctions

Source: main-20261015, sec-proper-base-change/sk-thm-properbasechange,
lemma-weil-pbc-completed-exchange-coherence.proof.md, second paragraph;
strict coefficient supplement, completed scalar unit and adjunction comparison.
Stacks Tags 099M and 099N supply the completion context.
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction).

The small pro-etale model, strict reduction, scalar maps and pullback models are the
published constructions of StrictScalarBalancing. No ring, tower or completion is replaced.
Positive exponent n+1 is indexed by n. Operation choices below retain their ordinary
adjunctions, and the scalar direct comparison is their normalized mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme.CompletedScalar
open StrictScalarBalancing CompletedScalarUnitProof

variable {A : Type (u + 1)} [CommRing A]

/-- The existing local completeness predicate, not a new completion notion.
Source: Stacks 099M and Koszul reconstruction
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev complete (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  IsComplete (finiteMap (topology T) A d.ideal b 0)

/-- The full complete category with the published intrinsic completeness predicate.
Source: Stacks 099M (blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev Complete (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  ObjectProperty.FullSubcategory (complete T d b)

/-- Completion and scalar restriction facts which are conclusions, not assumptions,
of the scalar comparison. The quotient criterion fixes the actual completion unit.
Source: Stacks 099M, 099N and constant-completion-equivalence
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure CompletionFacts (d : AdicCoefficientDatum A) : Prop where
  criterion : ∀ (T : Scheme.{u}) (b : Bool) (L : D (ring T d b)),
    complete T d b L ↔ IsIso ((completionUnit (topology T) A d.ideal b).app L)
  closed : ∀ (T : Scheme.{u}) (b : Bool) (L : D (ring T d b)),
    complete T d b ((completion (topology T) A d.ideal b).obj L)
  restricts : ∀ (T : Scheme.{u}) (L : D (ring T d true)), complete T d true L →
    complete T d false ((dres (scalar T d)).obj L)

/-- Restriction on the full complete categories, using the actual scalar functor.
Source: Stacks 099I (blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def CompletionFacts.restriction {d : AdicCoefficientDatum A} (H : CompletionFacts d)
    (T : Scheme.{u}) : Complete T d true ⥤ Complete T d false :=
  ObjectProperty.lift (complete T d false)
    (ObjectProperty.ι (complete T d true) ⋙ dres (scalar T d))
    (fun L ↦ H.restricts T L.obj L.property)

/-- The compatible-family/K-injective normalization of the existing scalar-limit
comparison. All its maps are the recorded universal right-derived transformations.
Source: Stacks 0940, 0A07; flat-scalar-tower-limit-square
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def LimitNormalized (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false)) : Prop :=
  ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring T d true)) ℤ,
    (dres (scalar T d)).map ((limitComparison (ring T d true)).app P) ≫
        lambda.hom.app ((TQ (ring T d true)).obj P) =
      (resFactors (scalar T d)).inv.app ((ordinaryLimit (ring T d true)).obj P) ≫
        (Q (ring T d false)).map ((limitRestriction (scalar T d)).hom.app P) ≫
        (limitComparison (ring T d false)).app
          (((tres (scalar T d)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (rlim (ring T d false)).map ((tresFactors (scalar T d)).hom.app P)

/-- The scalar completion comparison is the specified limit comparison followed by
strict balancing, including its strict transitions.
Source: strict coefficient supplement, proof Step 3
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def completionComparison (d : AdicCoefficientDatum A) (B : Balancing d)
    (T : Scheme.{u})
    (lambda : rlim (ring T d true) ⋙ dres (scalar T d) ≅
      tdres (scalar T d) ⋙ rlim (ring T d false)) :
    completion (topology T) A d.ideal true ⋙ dres (scalar T d) ≅
      dres (scalar T d) ⋙ completion (topology T) A d.ideal false :=
  (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft (reduction T d true) lambda ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.ρ T) (rlim (ring T d false)) ≪≫
    Functor.associator _ _ _

/-- The ordinary right adjoints and their normalized scalar mate, for the actual
pullbacks supplied by strict balancing. These are the operations stipulated by the node;
there is no completeness hypothesis on ordinary pullback or any ambient object.
Source: flat-ringed-diagram-restriction and pro-etale operations
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure Operations (d : AdicCoefficientDatum A) (B : Balancing d)
    {U V : Scheme.{u}} (f : U ⟶ V) where
  pull : PullCompatibility f d (B.ρ V) (B.ρ U)
  rightA : D (ring U d true) ⥤ D (ring V d true)
  right0 : D (ring U d false) ⥤ D (ring V d false)
  adjA : pull.completed.ordinary ⊣ rightA
  adj0 : pull.constant.ordinary ⊣ right0
  χ : rightA ⋙ dres (scalar V d) ≅ dres (scalar U d) ⋙ right0
  χ_normalized : χ.hom =
    (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ pull.a.inv)).natTrans

/-- The appropriate ordinary pullback, without any completion.
Source: pro-etale operations
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.ordinary {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    D (ring V d b) ⥤ D (ring U d b) :=
  match b with
  | false => O.pull.constant.ordinary
  | true => O.pull.completed.ordinary

/-- The appropriate strict-diagram pullback, retaining every transition.
Source: pro-etale operations and diagram-site realization
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.diagrams {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    TD (ring V d b) ⥤ TD (ring U d b) :=
  match b with
  | false => O.pull.constant.diagrams
  | true => O.pull.completed.diagrams

/-- Ordinary pullback followed by the specified quotient completion, on complete inputs.
Source: completed pullback; Stacks 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.completedPull {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (H : CompletionFacts d)
    (b : Bool) : Complete V d b ⥤ Complete U d b :=
  ObjectProperty.lift (complete U d b)
    (ObjectProperty.ι (complete V d b) ⋙ O.ordinary b ⋙
      completion (topology U) A d.ideal b)
    (fun L ↦ H.closed U b ((O.ordinary b).obj L.obj))

/-- The fixed reconstruction, namely derived limit of canonical strict reassociation.
Source: completed pullback; strict coefficient supplement, proof Step 4
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.reconstruction {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (b : Bool) :
    O.ordinary b ⋙ completion (topology U) A d.ideal b ≅
      reduction V d b ⋙ O.diagrams b ⋙ rlim (ring U d b) :=
  match b with
  | false => (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight O.pull.constantReassociation (rlim (ring U d false)) ≪≫
        Functor.associator _ _ _
  | true => (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight O.pull.τ (rlim (ring U d true)) ≪≫
        Functor.associator _ _ _

/-- The strict q comparison, before taking the derived limit.
Source: strict quotient scalar balancing, displayed pullback equation
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.quotientComparison {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) :
    (reduction V d true ⋙ O.pull.completed.diagrams) ⋙ tdres (scalar U d) ≅
      dres (scalar V d) ⋙ reduction V d false ⋙ O.pull.constant.diagrams :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reduction V d true) O.pull.p ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.ρ V) O.pull.constant.diagrams ≪≫
    Functor.associator _ _ _

/-- The component from the two published completed-pullback functors to constant modules.
Source: strict coefficient supplement, phi
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
abbrev Operations.ComparisonType {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) :=
  (ObjectProperty.ι (complete V d true) ⋙ O.ordinary true ⋙
    completion (topology U) A d.ideal true) ⋙ dres (scalar U d) ≅
      ObjectProperty.ι (complete V d true) ⋙ dres (scalar V d) ⋙
        O.ordinary false ⋙ completion (topology U) A d.ideal false

/-- The completion-unit normalization fixes phi uniquely on the full complete category.
Source: strict coefficient supplement, proof Step 5
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
def Operations.UnitNormalized {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (φ : O.ComparisonType) : Prop :=
  ∀ L : Complete V d true,
    (dres (scalar U d)).map ((completionUnit (topology U) A d.ideal true).app
        (O.pull.completed.ordinary.obj L.obj)) ≫ φ.hom.app L =
      O.pull.a.hom.app L.obj ≫ (completionUnit (topology U) A d.ideal false).app
        (O.pull.constant.ordinary.obj ((dres (scalar V d)).obj L.obj))

/-- The complete adjunction comparison, including actual Hom bijections, units,
counits, strict reconstruction and arbitrary changes of the constant complete input.
Every completeness assertion here is an output of the theorem. The `mate` field
identifies the full adjunctions, and `conjugation` expresses preservation of all
adjunction conjugates, in particular the canonical direct-image composition and
identity maps, including composites of edges as the other adjunction.
Source: strict coefficient supplement, proof Steps 4--9; Stacks 099M, 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction). -/
structure Comparison {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (H : CompletionFacts d)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false)) where
  pushA : ∀ N : D (ring U d true), complete U d true N →
    complete V d true (O.rightA.obj N)
  push0 : ∀ N : D (ring U d false), complete U d false N →
    complete V d false (O.right0.obj N)
  adjA : O.completedPull H true ⊣
    ObjectProperty.lift (complete V d true)
      (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
      (fun N ↦ pushA N.obj N.property)
  adj0 : O.completedPull H false ⊣
    ObjectProperty.lift (complete V d false)
      (ObjectProperty.ι (complete U d false) ⋙ O.right0)
      (fun N ↦ push0 N.obj N.property)
  homA : ∀ (L : Complete V d true) (N : Complete U d true)
    (t : (O.completedPull H true).obj L ⟶ N),
    (adjA.homEquiv L N t).hom = O.adjA.homEquiv L.obj N.obj
      ((completionUnit (topology U) A d.ideal true).app
        (O.pull.completed.ordinary.obj L.obj) ≫ t.hom)
  hom0 : ∀ (L : Complete V d false) (N : Complete U d false)
    (t : (O.completedPull H false).obj L ⟶ N),
    (adj0.homEquiv L N t).hom = O.adj0.homEquiv L.obj N.obj
      ((completionUnit (topology U) A d.ideal false).app
        (O.pull.constant.ordinary.obj L.obj) ≫ t.hom)
  φ : O.ComparisonType
  unit_normalized : O.UnitNormalized φ
  unique : ∀ ψ : O.ComparisonType, O.UnitNormalized ψ → ψ = φ
  reconstruction : ∀ L : Complete V d true,
    (dres (scalar U d)).map ((O.reconstruction true).hom.app L.obj) ≫
        lambda.hom.app ((O.pull.completed.diagrams).obj ((reduction V d true).obj L.obj)) ≫
        (rlim (ring U d false)).map (O.quotientComparison.hom.app L.obj) =
      φ.hom.app L ≫ (O.reconstruction false).hom.app ((dres (scalar V d)).obj L.obj)
  hom_comparison : ∀ (L : Complete V d true) (N : Complete U d true)
    (t : (O.completedPull H true).obj L ⟶ N),
    (adj0.homEquiv ((H.restriction V).obj L) ((H.restriction U).obj N)
      (ObjectProperty.homMk (φ.inv.app L ≫ (dres (scalar U d)).map t.hom))).hom =
        (dres (scalar V d)).map (adjA.homEquiv L N t).hom ≫ O.χ.hom.app N.obj
  unit : ∀ L : Complete V d true,
    (dres (scalar V d)).map (adjA.unit.app L).hom ≫
        O.χ.hom.app ((O.completedPull H true).obj L).obj ≫ O.right0.map (φ.hom.app L) =
      (adj0.unit.app ((H.restriction V).obj L)).hom
  counit : ∀ N : Complete U d true,
    φ.inv.app ⟨O.rightA.obj N.obj, pushA N.obj N.property⟩ ≫
        (dres (scalar U d)).map (adjA.counit.app N).hom =
      (O.ordinary false ⋙ completion (topology U) A d.ideal false).map
          (O.χ.hom.app N.obj) ≫ (adj0.counit.app ((H.restriction U).obj N)).hom
  φ_complete : O.completedPull H true ⋙ H.restriction U ≅
    H.restriction V ⋙ O.completedPull H false
  φ_complete_eq : ∀ L : Complete V d true, (φ_complete.hom.app L).hom = φ.hom.app L
  χ_complete :
    ObjectProperty.lift (complete V d true)
        (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
        (fun N ↦ pushA N.obj N.property) ⋙ H.restriction V ≅
      H.restriction U ⋙ ObjectProperty.lift (complete V d false)
        (ObjectProperty.ι (complete U d false) ⋙ O.right0)
        (fun N ↦ push0 N.obj N.property)
  χ_complete_eq : ∀ N : Complete U d true,
    (χ_complete.hom.app N).hom = O.χ.hom.app N.obj
  mate : (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φ_complete.inv)).natTrans =
    χ_complete.hom
  conjugation :
    ∀ (F : Complete V d true ⥤ Complete U d true)
      (R : Complete U d true ⥤ Complete V d true)
      (F₀ : Complete V d false ⥤ Complete U d false)
      (R₀ : Complete U d false ⥤ Complete V d false)
      (a : F ⊣ R) (a₀ : F₀ ⊣ R₀)
      (φ' : F ⋙ H.restriction U ≅ H.restriction V ⋙ F₀)
      (χ' : R ⋙ H.restriction V ≅ H.restriction U ⋙ R₀),
      (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ φ'.inv)).natTrans = χ'.hom →
      ∀ (α : ObjectProperty.lift (complete V d true)
          (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
          (fun N ↦ pushA N.obj N.property) ⟶ R)
        (β : ObjectProperty.lift (complete V d false)
          (ObjectProperty.ι (complete U d false) ⋙ O.right0)
          (fun N ↦ push0 N.obj N.property) ⟶ R₀),
        (∀ N : Complete U d true,
          (H.restriction V).map (α.app N) ≫ χ'.hom.app N =
            χ_complete.hom.app N ≫ β.app ((H.restriction U).obj N)) →
        ∀ L : Complete V d true,
          (H.restriction U).map (((conjugateEquiv adjA a).symm α).app L) ≫
              φ_complete.hom.app L =
            φ'.hom.app L ≫ ((conjugateEquiv adj0 a₀).symm β).app
              ((H.restriction V).obj L)
  change_input : ∀ (L : Complete V d true) (L₀ : Complete V d false)
    (h : (dres (scalar V d)).obj L.obj ⟶ L₀.obj),
    (dres (scalar U d)).map ((O.reconstruction true).hom.app L.obj) ≫
        lambda.hom.app ((O.pull.completed.diagrams).obj ((reduction V d true).obj L.obj)) ≫
        (rlim (ring U d false)).map (O.quotientComparison.hom.app L.obj) ≫
        (O.pull.constant.diagrams ⋙ rlim (ring U d false)).map
          ((reduction V d false).map h) =
      φ.hom.app L ≫ (O.ordinary false ⋙ completion (topology U) A d.ideal false).map h ≫
        (O.reconstruction false).hom.app L₀.obj


private theorem mate_adjunct
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {RA : D ⥤ C} {L₀ : E ⥤ F} {R₀ : F ⥤ E}
    (a : LA ⊣ RA) (a₀ : L₀ ⊣ R₀) (G : C ⥤ E) (H : D ⥤ F)
    (e : LA ⋙ H ≅ G ⋙ L₀) (X : C) (Y : D) (t : LA.obj X ⟶ Y) :
    a₀.homEquiv (G.obj X) (H.obj Y) (e.inv.app X ≫ H.map t) =
      G.map (a.homEquiv X Y t) ≫
        (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ e.inv)).app Y := by
  let m := mateEquiv a a₀ (TwoSquare.mk _ _ _ _ e.inv)
  have h := unit_mateEquiv a a₀ (TwoSquare.mk _ _ _ _ e.inv) X
  change G.map (a.unit.app X) ≫ m.app (LA.obj X) =
    a₀.unit.app (G.obj X) ≫ R₀.map (e.inv.app X) at h
  rw [a₀.homEquiv_unit, R₀.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : m.app (LA.obj X) ≫ R₀.map (H.map t) =
      G.map (RA.map t) ≫ m.app Y := m.natTrans.naturality t |>.symm
  rw [hd]
  rw [a.homEquiv_unit, G.map_comp, Category.assoc]

private theorem conjugation_compatible
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA L : C ⥤ D} {RA R : D ⥤ C} {LA₀ L₀ : E ⥤ F} {RA₀ R₀ : F ⥤ E}
    (a : LA ⊣ RA) (a₀ : LA₀ ⊣ RA₀) (b : L ⊣ R) (b₀ : L₀ ⊣ R₀)
    (G : C ⥤ E) (H : D ⥤ F) (e : LA ⋙ H ≅ G ⋙ LA₀)
    (e' : L ⋙ H ≅ G ⋙ L₀)
    (c : RA ⋙ G ≅ H ⋙ RA₀) (c' : R ⋙ G ≅ H ⋙ R₀)
    (hc : (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ e.inv)).natTrans = c.hom)
    (hc' : (mateEquiv b b₀ (TwoSquare.mk _ _ _ _ e'.inv)).natTrans = c'.hom)
    (α : RA ⟶ R) (β : RA₀ ⟶ R₀)
    (h : ∀ Y, G.map (α.app Y) ≫ c'.hom.app Y = c.hom.app Y ≫ β.app (H.obj Y))
    (X : C) :
    H.map (((conjugateEquiv a b).symm α).app X) ≫ e.hom.app X =
      e'.hom.app X ≫ ((conjugateEquiv a₀ b₀).symm β).app (G.obj X) := by
  let t := (conjugateEquiv a b).symm α
  let t₀ := (conjugateEquiv a₀ b₀).symm β
  have hm :
      (mateEquiv a b₀) ((TwoSquare.mk _ _ _ _ e'.inv).whiskerLeft t) =
      (mateEquiv a b₀) ((TwoSquare.mk _ _ _ _ e.inv).whiskerRight t₀) := by
    rw [conjugateEquiv_mateEquiv_vcomp a b b₀,
      mateEquiv_conjugateEquiv_vcomp a a₀ b₀]
    have hα : conjugateEquiv a b t = α := (conjugateEquiv a b).apply_symm_apply α
    have hβ : conjugateEquiv a₀ b₀ t₀ = β := (conjugateEquiv a₀ b₀).apply_symm_apply β
    rw [hα, hβ]
    apply TwoSquare.ext
    intro Y
    change G.map (α.app Y) ≫
        (mateEquiv b b₀ (TwoSquare.mk _ _ _ _ e'.inv)).natTrans.app Y =
      (mateEquiv a a₀ (TwoSquare.mk _ _ _ _ e.inv)).natTrans.app Y ≫ β.app (H.obj Y)
    rw [hc, hc']
    exact h Y
  have heq := congrArg (fun z ↦ z.app X) ((mateEquiv a b₀).injective hm)
  change e'.inv.app X ≫ H.map (t.app X) = t₀.app (G.obj X) ≫ e.inv.app X at heq
  apply (cancel_epi (e'.inv.app X)).mp
  have hh := congrArg (fun z ↦ z ≫ e.hom.app X) heq
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  erw [Iso.inv_hom_id_app_assoc]
  exact hh

private def pull_comparison {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false)) : O.ComparisonType :=
  NatIso.ofComponents
    (fun L ↦ (completionComparison d B U lambda).app (O.pull.completed.ordinary.obj L.obj) ≪≫
      (completion (topology U) A d.ideal false).mapIso (O.pull.a.app L.obj))
    (by
      intro L M k
      change (dres (scalar U d)).map
          ((completion (topology U) A d.ideal true).map
            (O.pull.completed.ordinary.map k.hom)) ≫ _ = _
      simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      have hn := (completionComparison d B U lambda).hom.naturality
        (O.pull.completed.ordinary.map k.hom)
      change (dres (scalar U d)).map
          ((completion (topology U) A d.ideal true).map _) ≫ _ =
        _ ≫ (completion (topology U) A d.ideal false).map
          ((dres (scalar U d)).map _) at hn
      erw [reassoc_of% hn]
      erw [← Functor.map_comp, O.pull.a.hom.naturality, Functor.map_comp]
      rfl)

private theorem pull_comparison_normalized {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false))
    (hunit : ∀ L : D (ring U d true),
      (dres (scalar U d)).map ((completionUnit (topology U) A d.ideal true).app L) ≫
        (completionComparison d B U lambda).hom.app L =
          (completionUnit (topology U) A d.ideal false).app
            ((dres (scalar U d)).obj L)) :
    O.UnitNormalized (pull_comparison O lambda) := by
  intro L
  change (dres (scalar U d)).map
      ((completionUnit (topology U) A d.ideal true).app
        (O.pull.completed.ordinary.obj L.obj)) ≫
      ((completionComparison d B U lambda).hom.app (O.pull.completed.ordinary.obj L.obj) ≫
        (completion (topology U) A d.ideal false).map (O.pull.a.hom.app L.obj)) = _
  rw [← Category.assoc, hunit]
  exact ((completionUnit (topology U) A d.ideal false).naturality
    (O.pull.a.hom.app L.obj)).symm

private theorem pull_comparison_reconstruction
    {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false)) (L : Complete V d true) :
    (dres (scalar U d)).map ((O.reconstruction true).hom.app L.obj) ≫
        lambda.hom.app (O.pull.completed.diagrams.obj ((reduction V d true).obj L.obj)) ≫
        (rlim (ring U d false)).map (O.quotientComparison.hom.app L.obj) =
      (pull_comparison O lambda).hom.app L ≫
        (O.reconstruction false).hom.app ((dres (scalar V d)).obj L.obj) := by
  have hn := lambda.hom.naturality (O.pull.τ.hom.app L.obj)
  change (dres (scalar U d)).map
      ((rlim (ring U d true)).map (O.pull.τ.hom.app L.obj)) ≫
      lambda.hom.app (O.pull.completed.diagrams.obj ((reduction V d true).obj L.obj)) =
    lambda.hom.app ((reduction U d true).obj (O.pull.completed.ordinary.obj L.obj)) ≫
      (rlim (ring U d false)).map ((tdres (scalar U d)).map
        (O.pull.τ.hom.app L.obj)) at hn
  simp only [pull_comparison, NatIso.ofComponents_hom_app, Iso.app_hom, completionComparison,
    Functor.mapIso_hom, Operations.reconstruction, Operations.quotientComparison,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom]
  dsimp only [Operations.ordinary, completion, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id]
  change (dres (scalar U d)).map
      ((rlim (ring U d true)).map (O.pull.τ.hom.app L.obj)) ≫
      lambda.hom.app _ ≫ (rlim (ring U d false)).map
        (O.pull.p.hom.app ((reduction V d true).obj L.obj) ≫
          O.pull.constant.diagrams.map ((B.ρ V).hom.app L.obj)) =
    ((lambda.hom.app _ ≫
      (rlim (ring U d false)).map ((B.ρ U).hom.app
        (O.pull.completed.ordinary.obj L.obj))) ≫
      (completion (topology U) A d.ideal false).map (O.pull.a.hom.app L.obj)) ≫
      (rlim (ring U d false)).map
        (O.pull.constantReassociation.hom.app ((dres (scalar V d)).obj L.obj))
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  erw [O.pull.equation]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem unit_precomp_injective
    {C : Type*} [Category C] {M X Y N : C}
    (c : M ⟶ X) (c₀ : M ⟶ Y) (e : X ≅ Y) (he : c ≫ e.hom = c₀)
    (h : Function.Injective (fun t : Y ⟶ N ↦ c₀ ≫ t)) :
    Function.Injective (fun t : X ⟶ N ↦ c ≫ t) := by
  intro f g hfg
  apply (cancel_epi e.inv).mp
  apply h
  rw [← he]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hfg

private theorem pull_comparison_unique
    {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false))
    (hunit : ∀ L : D (ring U d true),
      (dres (scalar U d)).map ((completionUnit (topology U) A d.ideal true).app L) ≫
        (completionComparison d B U lambda).hom.app L =
          (completionUnit (topology U) A d.ideal false).app
            ((dres (scalar U d)).obj L))
    (ψ : O.ComparisonType) (hψ : O.UnitNormalized ψ) : ψ = pull_comparison O lambda := by
  let := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  obtain ⟨_, _, hclosed, hbij, _⟩ :=
    koszul_quotient_reflector (topology U) A d.ideal false r a ha
  apply Iso.ext
  apply NatTrans.ext
  funext L
  apply unit_precomp_injective _ _
    ((completionComparison d B U lambda).app (O.pull.completed.ordinary.obj L.obj))
    (hunit _) (hbij _ _ (hclosed _)).injective
  exact (hψ L).trans ((pull_comparison_normalized O lambda hunit) L).symm

private theorem completion_facts (d : AdicCoefficientDatum A) :
    ∃ H : CompletionFacts d, ∀ T : Scheme.{u}, (H.restriction T).IsEquivalence := by
  let := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  have facts (T : Scheme.{u}) (b : Bool) :=
    koszul_quotient_reflector (topology T) A d.ideal b r a ha
  have restricts (T : Scheme.{u}) (L : D (ring T d true)) (hL : complete T d true L) :
      complete T d false ((dres (scalar T d)).obj L) := by
    obtain ⟨e, he⟩ := equivalence (topology T) A d.ideal
    obtain ⟨i⟩ := he
    have hX := (facts T false).choose_spec.2.2.2 ((e.functor.obj ⟨L, hL⟩).obj)
    have hY := (facts T false).choose_spec.2.2.2 ((dres (scalar T d)).obj L)
    exact hY.mp ((NatTrans.isIso_app_iff_of_iso
      (completionUnit (topology T) A d.ideal false) (i.app ⟨L, hL⟩)).mp
        (hX.mpr (e.functor.obj ⟨L, hL⟩).property))
  let H : CompletionFacts d := {
    criterion := fun T b L ↦ (facts T b).choose_spec.2.2.2 L |>.symm
    closed := fun T b L ↦ (facts T b).choose_spec.2.1 L
    restricts := restricts }
  refine ⟨H, ?_⟩
  intro T
  obtain ⟨e, he⟩ := equivalence (topology T) A d.ideal
  obtain ⟨i⟩ := he
  let j : e.functor ≅ H.restriction T := NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _ (i.app L))
    (by intro L M f; apply ObjectProperty.hom_ext; exact i.hom.naturality f)
  exact Functor.isEquivalence_of_iso j

private theorem comparison_of_preservation
    {d : AdicCoefficientDatum A} {B : Balancing d}
    {U V : Scheme.{u}} {f : U ⟶ V} (O : Operations d B f) (H : CompletionFacts d)
    (lambda : rlim (ring U d true) ⋙ dres (scalar U d) ≅
      tdres (scalar U d) ⋙ rlim (ring U d false))
    (hunit : ∀ L : D (ring U d true),
      (dres (scalar U d)).map ((completionUnit (topology U) A d.ideal true).app L) ≫
        (completionComparison d B U lambda).hom.app L =
          (completionUnit (topology U) A d.ideal false).app
            ((dres (scalar U d)).obj L))
    (pushA : ∀ N : D (ring U d true), complete U d true N →
      complete V d true (O.rightA.obj N))
    (push0 : ∀ N : D (ring U d false), complete U d false N →
      complete V d false (O.right0.obj N)) : Nonempty (Comparison O H lambda) := by
  let := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing d.ideal)
  have hb (b : Bool) := (koszul_quotient_reflector (topology U) A d.ideal b r a ha).choose_spec
  obtain ⟨cA, hcA⟩ := reflector_of_bijective (complete U d true)
    (completion (topology U) A d.ideal true) (completionUnit (topology U) A d.ideal true)
    (H.closed U true) (hb true).2.2.1
  obtain ⟨c0, hc0⟩ := reflector_of_bijective (complete U d false)
    (completion (topology U) A d.ideal false) (completionUnit (topology U) A d.ideal false)
    (H.closed U false) (hb false).2.2.1
  obtain ⟨adjA, homA⟩ := complete_adjunction (complete V d true) (complete U d true)
    O.pull.completed.ordinary O.rightA O.adjA _ _ (H.closed U true) pushA cA hcA
  obtain ⟨adj0, hom0⟩ := complete_adjunction (complete V d false) (complete U d false)
    O.pull.constant.ordinary O.right0 O.adj0 _ _ (H.closed U false) push0 c0 hc0
  let φ := pull_comparison O lambda
  have hn : O.UnitNormalized φ := pull_comparison_normalized O lambda hunit
  let φc : O.completedPull H true ⋙ H.restriction U ≅
      H.restriction V ⋙ O.completedPull H false :=
    NatIso.ofComponents (fun L ↦ ObjectProperty.isoMk _ (φ.app L))
      (by intro L M k; apply ObjectProperty.hom_ext; exact φ.hom.naturality k)
  let χc :
      ObjectProperty.lift (complete V d true)
        (ObjectProperty.ι (complete U d true) ⋙ O.rightA)
        (fun N ↦ pushA N.obj N.property) ⋙ H.restriction V ≅
      H.restriction U ⋙ ObjectProperty.lift (complete V d false)
        (ObjectProperty.ι (complete U d false) ⋙ O.right0)
        (fun N ↦ push0 N.obj N.property) :=
    NatIso.ofComponents (fun N ↦ ObjectProperty.isoMk _ (O.χ.app N.obj))
      (by intro N M k; apply ObjectProperty.hom_ext; exact O.χ.hom.naturality k.hom)
  have hhom (L : Complete V d true) (N : Complete U d true)
      (t : (O.completedPull H true).obj L ⟶ N) :
      (adj0.homEquiv ((H.restriction V).obj L) ((H.restriction U).obj N)
        (ObjectProperty.homMk (φ.inv.app L ≫ (dres (scalar U d)).map t.hom))).hom =
      (dres (scalar V d)).map (adjA.homEquiv L N t).hom ≫ O.χ.hom.app N.obj := by
    erw [hom0]
    have ht := homA L N t.hom
    change (adjA.homEquiv L N t).hom = _ at ht
    erw [ht]
    have he : (completionUnit (topology U) A d.ideal false).app
          (O.pull.constant.ordinary.obj ((dres (scalar V d)).obj L.obj)) ≫ φ.inv.app L =
        O.pull.a.inv.app L.obj ≫ (dres (scalar U d)).map
          ((completionUnit (topology U) A d.ideal true).app
            (O.pull.completed.ordinary.obj L.obj)) := by
      apply (cancel_mono (φ.hom.app L)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id, hn L, Iso.inv_hom_id_app_assoc]
    erw [← Category.assoc, he, Category.assoc, ← Functor.map_comp]
    erw [O.χ_normalized]
    exact mate_adjunct O.adjA O.adj0 _ _ O.pull.a _ _ _
  have hm : (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv)).natTrans = χc.hom := by
    apply NatTrans.ext
    funext N
    apply ObjectProperty.hom_ext
    have hh := hhom ⟨O.rightA.obj N.obj, pushA N.obj N.property⟩ N (adjA.counit.app N)
    have htri : adjA.homEquiv _ N (adjA.counit.app N) = 𝟙 _ :=
      by
        rw [← adjA.homEquiv_symm_id N]
        exact Equiv.apply_symm_apply _ _
    have hmate := mate_adjunct adjA adj0 (H.restriction V) (H.restriction U)
      φc _ N (adjA.counit.app N)
    rw [htri, CategoryTheory.Functor.map_id, Category.id_comp] at hmate
    have hmate' := congrArg (fun k ↦ k.hom) hmate
    change (adj0.homEquiv _ _
      (ObjectProperty.homMk (φ.inv.app _ ≫
        (dres (scalar U d)).map (adjA.counit.app N).hom))).hom =
      ((mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv)).natTrans.app N).hom at hmate'
    erw [htri] at hh
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at hh
    exact hmate'.symm.trans hh
  refine ⟨{
    pushA := pushA
    push0 := push0
    adjA := adjA
    adj0 := adj0
    homA := fun L N t ↦ homA L N t.hom
    hom0 := fun L N t ↦ hom0 L N t.hom
    φ := φ, unit_normalized := hn,
    unique := fun ψ hψ ↦ pull_comparison_unique O lambda hunit ψ hψ,
    reconstruction := pull_comparison_reconstruction O lambda,
    hom_comparison := hhom,
    unit := ?_, counit := ?_, φ_complete := φc, φ_complete_eq := fun _ ↦ rfl,
    χ_complete := χc, χ_complete_eq := fun _ ↦ rfl, mate := hm,
    conjugation := ?_, change_input := ?_ }⟩
  · intro L
    have hh := unit_mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv) L
    change (H.restriction V).map (adjA.unit.app L) ≫
      (mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv)).natTrans.app
        ((O.completedPull H true).obj L) =
      adj0.unit.app ((H.restriction V).obj L) ≫
        (ObjectProperty.lift (complete V d false)
          (ObjectProperty.ι (complete U d false) ⋙ O.right0)
          (fun N ↦ push0 N.obj N.property)).map (φc.inv.app L) at hh
    rw [hm] at hh
    have hh' := congrArg (fun k ↦ k.hom) hh
    change (dres (scalar V d)).map (adjA.unit.app L).hom ≫
      O.χ.hom.app ((O.completedPull H true).obj L).obj =
        (adj0.unit.app ((H.restriction V).obj L)).hom ≫
          O.right0.map (φ.inv.app L) at hh'
    rw [← Category.assoc, hh', Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro N
    have hh := mateEquiv_counit adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv) N
    change _ ≫ _ = _ at hh
    have hh' := congrArg (fun k ↦ k.hom) hh
    change (O.ordinary false ⋙ completion (topology U) A d.ideal false).map
      (((mateEquiv adjA adj0 (TwoSquare.mk _ _ _ _ φc.inv)).natTrans.app N).hom) ≫
      (adj0.counit.app _).hom = _ at hh'
    rw [hm] at hh'
    exact hh'.symm
  · intro F R F₀ R₀ a a₀ φ' χ' hχ α β hα L
    exact conjugation_compatible adjA adj0 a a₀ _ _ φc φ' χc χ' hm hχ α β hα L
  · intro L L₀ h
    have hr := congrArg (fun k ↦ k ≫
      (O.pull.constant.diagrams ⋙ rlim (ring U d false)).map
        ((reduction V d false).map h)) (pull_comparison_reconstruction O lambda L)
    simp only [Category.assoc] at hr
    erw [hr]
    have hr₀ := (O.reconstruction false).hom.naturality h
    change (O.ordinary false ⋙ completion (topology U) A d.ideal false).map h ≫
      (O.reconstruction false).hom.app L₀.obj =
      (O.reconstruction false).hom.app _ ≫
        (O.pull.constant.diagrams ⋙ rlim (ring U d false)).map
          ((reduction V d false).map h) at hr₀
    erw [← hr₀]

/-- Restriction identifies the actual quotient units on every ambient input, and the
unique completion-unit-normalized pullback comparison identifies the completed
adjunctions, their strict reconstruction and their Hom bijections. The operations in
`Operations` are the stipulated normalized ordinary operations, with arbitrary choices
of their universal derived presentations. In particular their direct images of complete
objects are complete, so they can themselves be substituted for the complete input.

Source: main-20261015, completed-exchange-coherence proof, second paragraph;
strict scalar supplement, Stacks Tags 099M and 099N
(blueprint: lem-weil-pbc-completed-scalar-unit-adjunction).

Proof: the published Koszul/quotient reflector gives completeness of every completion,
the universal property of its unit and the equivalence of full complete categories.
Choose the normalized derived-limit restriction comparison. On flat-term K-flat
representatives, strictScalarCompletionUnit identifies its composite with strict
balancing with the actual constant quotient unit; localization extends the identity
to all ambient objects. Construct the pullback comparison by whiskering this composite
and the normalized ordinary pullback comparison. Naturality and the strict balancing
equation give its reconstruction identity. The quotient-unit equation gives its unit
normalization; injectivity of precomposition with the constant quotient unit gives
uniqueness. The normalized ordinary adjunctions and their completeness preservation
come from strictScalarOrdinaryAdjunction; right-adjoint uniqueness handles every choice
of Operations. Compose the completion reflector Hom bijections with these ordinary
adjunctions. The mate transpose equation identifies the resulting Hom bijections;
unit_mateEquiv and mateEquiv_counit then identify units and counits. The same transpose
calculation identifies adjunction conjugates. Finally, naturality of the fixed constant
reconstruction gives change of complete input. All assertions use unbounded ambient
or full complete categories, with no additional geometric hypotheses.
-/
theorem completedScalarUnitAdjunction (d : AdicCoefficientDatum A) (B : Balancing d) :
    ∃ H : CompletionFacts d,
      (∀ T : Scheme.{u}, (H.restriction T).IsEquivalence) ∧
      ∃ lambda : ∀ T : Scheme.{u},
          rlim (ring T d true) ⋙ dres (scalar T d) ≅
            tdres (scalar T d) ⋙ rlim (ring T d false),
        (∀ T : Scheme.{u}, LimitNormalized T d (lambda T)) ∧
        (∀ (T : Scheme.{u}) (L : D (ring T d true)),
          (dres (scalar T d)).map ((completionUnit (topology T) A d.ideal true).app L) ≫
              (completionComparison d B T (lambda T)).hom.app L =
            (completionUnit (topology T) A d.ideal false).app
              ((dres (scalar T d)).obj L)) ∧
        (∀ (U V : Scheme.{u}) (f : U ⟶ V), Nonempty (Operations d B f)) ∧
        ∀ (U V : Scheme.{u}) (f : U ⟶ V) (O : Operations d B f),
          Nonempty (Comparison O H (lambda U)) := by
  let := d.noetherian
  obtain ⟨H, hH⟩ := completion_facts d
  have hlim (T : Scheme.{u}) := derivedLimitRestriction (topology T) A d.ideal
  let lambda := fun T : Scheme.{u} ↦ (hlim T).choose
  have hlimn (T : Scheme.{u}) : LimitNormalized T d (lambda T) := (hlim T).choose_spec
  have hunit (T : Scheme.{u}) (L : D (ring T d true)) :
      (dres (scalar T d)).map ((completionUnit (topology T) A d.ideal true).app L) ≫
          (completionComparison d B T (lambda T)).hom.app L =
        (completionUnit (topology T) A d.ideal false).app ((dres (scalar T d)).obj L) := by
    dsimp only [completionComparison]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp]
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
      strictScalarCompletionUnit d B T (lambda T) (hlimn T) L
  refine ⟨H, hH, lambda, hlimn, hunit, ?_, ?_⟩
  · intro U V f
    obtain ⟨P⟩ := B.pullback f
    obtain ⟨RA, R0, aA, a0, χ, hχ, _, _⟩ := strictScalarOrdinaryAdjunction d B f P
    exact ⟨{
      pull := P
      rightA := RA
      right0 := R0
      adjA := aA
      adj0 := a0
      χ := χ
      χ_normalized := hχ }⟩
  · intro U V f O
    obtain ⟨RA, R0, aA, a0, _, _, hpA, hp0⟩ :=
      strictScalarOrdinaryAdjunction d B f O.pull
    apply comparison_of_preservation O H (lambda U) (hunit U)
    · intro N hN
      have e := aA.rightAdjointUniq O.adjA
      apply (H.criterion V true _).mpr
      have hi := (H.criterion V true _).mp (hpA N hN)
      exact (NatTrans.isIso_app_iff_of_iso (completionUnit (topology V) A d.ideal true)
        (e.app N)).mp hi
    · intro N hN
      have e := a0.rightAdjointUniq O.adj0
      apply (H.criterion V false _).mpr
      have hi := (H.criterion V false _).mp (hp0 N hN)
      exact (NatTrans.isIso_app_iff_of_iso (completionUnit (topology V) A d.ideal false)
        (e.app N)).mp hi

end AlgebraicGeometry.Scheme.CompletedScalar
