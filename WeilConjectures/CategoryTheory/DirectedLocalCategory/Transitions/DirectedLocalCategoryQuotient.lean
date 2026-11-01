/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
import Mathlib.Data.Quot

/-!
# Eventual morphisms of directed local categories

Source: latest blueprint, `sec-six-functors-basics/sk-prop-qlbar-two-colimit/`
`det-def-sfb-filtered-two-colimit-model.proof.md`, paragraphs “The colimit is filtered”
and “Composition” (blueprint: lem-sfb-directed-local-category-quotient).

The declarations below are the input data, concrete quotient constructions and individual
clauses of that lemma. Stage Hom sets, labels and indices have independent universes.
`ULift` places the Hom diagram in a universe containing both its indices and its Hom sets.
-/

@[expose] public section

set_option autoImplicit false

universe w u v z

namespace CategoryTheory.DirectedLocalCategory

open CategoryTheory Limits

variable {I : Type w} [Preorder I] {O : Type u}

/-- The labels born by stage `k`.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
abbrev StageObject (birth : O → I) (k : I) := {a : O // birth a ≤ k}

variable (birth : O → I) [E : ∀ k : I, Category.{v} (StageObject birth k)]

/-- The stage Hom set, retaining the proofs that both labels have been born.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
abbrev StageHom (k : I) (a b : O) (ha : birth a ≤ k) (hb : birth b ≤ k) :=
  (⟨a, ha⟩ : StageObject birth k) ⟶ ⟨b, hb⟩

variable {birth} (T : Transitions birth)

/-- The common-stage preorder `J_ab`.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
abbrev Index (birth : O → I) (a b : O) := {k : I // birth a ≤ k ∧ birth b ≤ k}

variable (birth)

/-- A representative is a stage in `J_ab` and a morphism at that stage.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
abbrev Rep (a b : O) :=
  (k : Index birth a b) × StageHom birth k.val a b k.property.1 k.property.2

variable {birth}

namespace Transitions

/-- Eventual equality means equality after transport to one common later stage.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def Eventual {a b : O} (r s : Rep birth a b) : Prop :=
  ∃ (p : I) (hr : r.1.val ≤ p) (hs : s.1.val ≤ p), T.map hr r.2 = T.map hs s.2

/-- The generating relation, a single forward transport.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def Step {a b : O} (r s : Rep birth a b) : Prop :=
  ∃ h : r.1.val ≤ s.1.val, T.map h r.2 = s.2

/-- The quotient by eventual equality; no injectivity of transport is assumed.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def Hom (a b : O) : Type (max w v) := Quot (T.Eventual (a := a) (b := b))

/-- The class of a stage representative in the eventual-equality quotient.
Source: the blueprint proof, “The colimit is filtered”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def classOf {a b : O} (r : Rep birth a b) : T.Hom a b := Quot.mk _ r

variable [hI : Nonempty I] [hdir : IsDirected I (· ≤ ·)]

include hI hdir

/-- A chosen common upper bound, used only in the concrete composition construction.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
noncomputable def upper (k n : I) : {m : I // k ≤ m ∧ n ≤ m} :=
  ⟨(exists_ge_ge k n).choose, (exists_ge_ge k n).choose_spec⟩

/-- Compose representatives at a specified common stage.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def compAt {a b c : O} (r : Rep birth a b) (s : Rep birth b c)
    (m : I) (hr : r.1.val ≤ m) (hs : s.1.val ≤ m) : Rep birth a c :=
  ⟨⟨m, r.1.property.1.trans hr, s.1.property.2.trans hs⟩,
    T.map hr r.2 ≫ T.map hs s.2⟩

/-- The composite class before descent, evaluated at the chosen upper bound.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
noncomputable def compositeClass {a b c : O} (r : Rep birth a b) (s : Rep birth b c) :
    T.Hom a c :=
  T.classOf (T.compAt r s (upper r.1.val s.1.val).val
    (upper r.1.val s.1.val).property.1 (upper r.1.val s.1.val).property.2)

/-- The formula is independent of both the representatives and the common stage.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient).
Proof: move the witnesses for eventual equality and both choices of common stage to a
further upper bound. Apply `map_trans` and `map_comp`, then compare the resulting equal
stage composites. No injectivity or antisymmetry is used. -/
theorem compositeClass_independent {a b c : O}
    (r r' : Rep birth a b) (s s' : Rep birth b c)
    (hr : T.Eventual r r') (hs : T.Eventual s s')
    (m n : I) (hmr : r.1.val ≤ m) (hms : s.1.val ≤ m)
    (hnr : r'.1.val ≤ n) (hns : s'.1.val ≤ n) :
    T.classOf (T.compAt r s m hmr hms) = T.classOf (T.compAt r' s' n hnr hns) := by
  sorry

/-- Well-definedness in the second input, needed by `Quot.lift₂`.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient).
Proof: use `compositeClass_independent` with the first representative unchanged and the
chosen upper bounds. Reflexivity of eventual equality supplies the unchanged input. -/
theorem compositeClass_right {a b c : O} (r : Rep birth a b) (s s' : Rep birth b c)
    (h : T.Eventual s s') : T.compositeClass r s = T.compositeClass r s' := by
  sorry

/-- Well-definedness in the first input, needed by `Quot.lift₂`.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient).
Proof: use `compositeClass_independent` with the second representative unchanged and the
chosen upper bounds. Reflexivity supplies the unchanged input. -/
theorem compositeClass_left {a b c : O} (r r' : Rep birth a b) (s : Rep birth b c)
    (h : T.Eventual r r') : T.compositeClass r s = T.compositeClass r' s := by
  sorry

/-- Composition on the concrete quotient, by separate descent in its two inputs.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
noncomputable def comp {a b c : O} : T.Hom a b → T.Hom b c → T.Hom a c :=
  Quot.lift₂ T.compositeClass T.compositeClass_right T.compositeClass_left

variable (birth) in
/-- The identity representative is the stage identity at the birth index.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def identityRep (a : O) : Rep birth a a :=
  ⟨⟨birth a, le_rfl, le_rfl⟩, 𝟙 (⟨a, le_rfl⟩ : StageObject birth (birth a))⟩

/-- The identity class is exactly the class of the birth-stage identity.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
def identity (a : O) : T.Hom a a := T.classOf (identityRep birth a)

/-- The displayed common-stage formula holds for every choice of upper bound.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient).
Proof: unfold the two quotient lifts on classes and compare the chosen common stage with
`m` using `compositeClass_independent` and reflexivity. -/
theorem comp_classOf {a b c : O} (r : Rep birth a b) (s : Rep birth b c)
    (m : I) (hr : r.1.val ≤ m) (hs : s.1.val ≤ m) :
    T.comp (T.classOf r) (T.classOf s) = T.classOf (T.compAt r s m hr hs) := by
  sorry

/-- The actual category on the given label set `O`, with the constructed quotient Hom sets.
Source: the blueprint proof, “Composition”
(blueprint: lem-sfb-directed-local-category-quotient). -/
@[instance_reducible]
noncomputable def category : Category.{max w v} O where
  Hom := T.Hom
  id := T.identity
  comp := T.comp
  id_comp := T.category_laws.1
  comp_id := T.category_laws.2.1
  assoc := T.category_laws.2.2

end Transitions

end CategoryTheory.DirectedLocalCategory
