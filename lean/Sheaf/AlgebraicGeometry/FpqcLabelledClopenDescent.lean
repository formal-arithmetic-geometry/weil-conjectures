/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!+# Fpqc descent of labelled clopen partitions

Source: literature/stacks-project/descent.tex, Tag 03N0, lemma-open-fpqc-covering;
literature/stacks-project/topologies.tex, Tag 022D, lemma-fpqc (3).
(blueprint: lem-sfb-fpqc-labelled-clopen-descent)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compatible labels with open fibres on an arbitrary fpqc covering descend to a unique
clopen partition. Each `Z a : X.Opens` carries its canonical open subscheme structure
`(Z a).toScheme`, with open immersion `(Z a).ι`. The partition also detects any compatible
label function on a test scheme, without assuming that function has open fibres.

Source: literature/stacks-project/descent.tex, Tag 03N0, lemma-open-fpqc-covering,
applied to label fibres; literature/stacks-project/topologies.tex, Tag 022D, lemma-fpqc (3).
(blueprint: lem-sfb-fpqc-labelled-clopen-descent)

Proof:
1. For each label `a`, the opens `ρ i ⁻¹' {a}` agree after pullback to every double overlap
   by `hcompat`. Apply `lem-weil-pbc-open-subscheme-fpqc-descent` to obtain `Z a` with
   the prescribed inverse images and its open subscheme structure
   (`def-weil-open-immersion`).
2. Joint surjectivity from `def-weil-pbc-fpqc-covering` gives a lift of every point of `X`.
   Membership in `Z a` is equivalent to that lift having label `a`. Thus the pieces are
   pairwise disjoint, cover `X`, and are unique. The complement of `Z a` is the union of
   the other open pieces, so `Z a` is closed. If `A` is empty, a lift would give an element
   of `A`, so `X` is empty and the empty family satisfies the conclusion.
3. By `lem-galois-fpqc-covering-base-change`, the second projections from `U i ×_X V`
   form an fpqc covering of `V`, exchanging the two factors by `def-pc-fibre-product`.
   These projections are jointly surjective by `def-weil-pbc-fpqc-covering`.
4. Lift a point `z` of `V` to some `U i ×_X V`. The fibre-product equation, the prescribed
   inverse image of `Z a`, and test compatibility show `h z ∈ Z a` iff `σ z = a`.
   This gives the required equality of inverse images. Continuity of `h` implies that
   each fibre of `σ` is open and closed. The argument includes empty test schemes.
-/
theorem labelledClopenPartition_existsUnique_of_fpqc
    {X : Scheme.{u}} {I : Type v} {A : Type w} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ X)
    (hf : Presieve.ofArrows U f ∈ Scheme.fpqcPrecoverage X)
    (ρ : ∀ i, U i → A)
    (hρ : ∀ (i : I) (a : A), IsOpen (ρ i ⁻¹' {a}))
    (hcompat : ∀ (i j : I),
      ρ i ∘ pullback.fst (f i) (f j) = ρ j ∘ pullback.snd (f i) (f j)) :
    ∃! Z : A → X.Opens,
      (∀ a, IsClosed (Z a : Set X)) ∧
      Pairwise (fun a b ↦ Disjoint (Z a) (Z b)) ∧
      (⋃ a, (Z a : Set X)) = Set.univ ∧
      (∀ (i : I) (a : A), f i ⁻¹' (Z a : Set X) = ρ i ⁻¹' {a}) ∧
      ∀ (V : Scheme.{u}) (h : V ⟶ X) (σ : V → A),
        (∀ i, ρ i ∘ pullback.fst (f i) h = σ ∘ pullback.snd (f i) h) →
          ∀ a, h ⁻¹' (Z a : Set X) = σ ⁻¹' {a} ∧ IsClopen (σ ⁻¹' {a}) := by
  sorry

end AlgebraicGeometry
