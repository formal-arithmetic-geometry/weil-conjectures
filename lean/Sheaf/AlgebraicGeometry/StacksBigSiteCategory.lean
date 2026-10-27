/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCardinalSize
public import Mathlib.SetTheory.ZFC.VonNeumann

/-! # Admissible underlying categories of Stacks big sites

Source: Stacks Project, topologies.tex, Tag 021R (definition-big-fppf-site), clause (2),
and sets.tex, Tag 000J (lemma-construct-category), clauses (1)--(4)
(blueprint: def-sfb-stacks-big-site-category).

The set-theoretic coding of schemes is explicit: `code` assigns distinct ZFC sets to
schemes in the fixed ambient universe. `stacksBigSiteObjects code α` cuts out precisely
the objects whose codes belong to the cumulative hierarchy stage `V_α`. Its full
subcategory retains every scheme morphism between these objects. The admissibility
predicate records the four conditions on this chosen category, without choosing an
ordinal or asserting that an admissible ordinal exists. The larger coding universe
implements the size convention of `def-weil-size-convention`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Membership of a scheme's chosen set-theoretic code in `V_α`.

Source: Stacks Project, sets.tex, section-categories-schemes, before Tag 000J;
`ZFSet.vonNeumann` is the cumulative hierarchy with empty zeroth stage, powerset
successor stages, and union limit stages (blueprint: def-sfb-stacks-big-site-category). -/
noncomputable def stacksBigSiteObjects (code : Scheme.{u} ↪ ZFSet.{u + 1})
    (α : Ordinal.{u + 1}) : ObjectProperty Scheme.{u} :=
  fun X => code X ∈ ZFSet.vonNeumann α

/-- The full category `Sch_α`: schemes whose codes lie in `V_α`, with all scheme morphisms.

Source: Stacks Project, sets.tex, section-categories-schemes, before Tag 000J
(blueprint: def-sfb-stacks-big-site-category). -/
abbrev StacksBigSiteCategory (code : Scheme.{u} ↪ ZFSet.{u + 1})
    (α : Ordinal.{u + 1}) :=
  (stacksBigSiteObjects code α).FullSubcategory

/-- Admissibility of a chosen underlying category for a big fppf site containing `S₀`.

The ordinal is a nonzero limit ordinal. The category contains `S₀` and representatives
of every scheme of size at most `max (s(S)^ℵ₀) (succ (s(S)))` for each of its objects `S`.
For every diagram with countably many objects and countable hom sets, a limit (respectively
colimit) exists internally exactly when it exists among all ambient schemes, and inclusion
preserves every such limit (respectively colimit). Thus their canonical comparisons are
isomorphisms whenever the objects exist; no existence of arbitrary countable scheme
limits or colimits is imposed. Countability includes finite and empty diagram categories.

Here the injective coding is the chosen presentation of the underlying set-theoretic
codes, rather than additional geometric data. One may use a full skeleton under the
standing size convention; the displayed predicate uses the full category itself.

Source: Stacks Project, topologies.tex, Tag 021R, definition-big-fppf-site, clause (2),
and sets.tex, Tag 000J, lemma-construct-category, clauses (1)--(4), equation-bound
(blueprint: def-sfb-stacks-big-site-category). -/
def IsStacksBigSiteCategory (code : Scheme.{u} ↪ ZFSet.{u + 1})
    (S₀ : Set Scheme.{u}) (α : Ordinal.{u + 1}) : Prop :=
  Order.IsSuccLimit α ∧
    (∀ X ∈ S₀, stacksBigSiteObjects code α X) ∧
    (∀ S : StacksBigSiteCategory code α, ∀ W : Scheme.{u},
      W.cardinalSize ≤ max (S.obj.cardinalSize ^ Cardinal.aleph0)
        (Order.succ S.obj.cardinalSize) →
      ∃ S' : StacksBigSiteCategory code α, Nonempty (W ≅ S'.obj)) ∧
    (∀ (I : Type u) [SmallCategory I] [Countable I]
      [∀ i j : I, Countable (i ⟶ j)] (F : I ⥤ StacksBigSiteCategory code α),
      (HasLimit F ↔ HasLimit (F ⋙ (stacksBigSiteObjects code α).ι)) ∧
        PreservesLimit F (stacksBigSiteObjects code α).ι) ∧
    (∀ (I : Type u) [SmallCategory I] [Countable I]
      [∀ i j : I, Countable (i ⟶ j)] (F : I ⥤ StacksBigSiteCategory code α),
      (HasColimit F ↔ HasColimit (F ⋙ (stacksBigSiteObjects code α).ι)) ∧
        PreservesColimit F (stacksBigSiteObjects code α).ι)

end AlgebraicGeometry.Scheme
