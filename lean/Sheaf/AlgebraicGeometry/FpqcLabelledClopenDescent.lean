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
  classical
  let W (a : A) (i : I) : (U i).Opens := ⟨ρ i ⁻¹' {a}, hρ i a⟩
  have hW (a : A) (i j : I) :
      pullback.fst (f i) (f j) ⁻¹ᵁ W a i =
        pullback.snd (f i) (f j) ⁻¹ᵁ W a j := by
    ext z
    exact congrArg (fun t : A ↦ t = a) (congrFun (hcompat i j) z) |>.to_iff
  choose Z hZ using fun a ↦ (openSubscheme_existsUnique_of_fpqc f hf (W a) (hW a)).exists
  have hmem (i : I) (a : A) (x : U i) : f i x ∈ Z a ↔ ρ i x = a := by
    change x ∈ f i ⁻¹ᵁ Z a ↔ _
    rw [hZ a i]
    rfl
  have hsurj : ∀ x : X, ∃ i, ∃ y : U i, f i y = x := by
    intro x
    obtain ⟨Y, g, hg, y, hy⟩ := Scheme.JointlySurjective.exists_eq
      (K := Scheme.precoverage @Flat) (Presieve.ofArrows U f) hf.2 x
    obtain ⟨i⟩ := hg
    exact ⟨i, y, hy⟩
  have hclosed (a : A) : IsClosed (Z a : Set X) := by
    apply isOpen_compl_iff.mp
    have heq : (Z a : Set X)ᶜ = ⋃ b : {b : A // b ≠ a}, (Z b.1 : Set X) := by
      ext x
      obtain ⟨i, y, rfl⟩ := hsurj x
      constructor
      · intro hy
        have hne : ρ i y ≠ a := fun he ↦ hy ((hmem i a y).mpr he)
        exact Set.mem_iUnion.mpr ⟨⟨ρ i y, hne⟩, (hmem i (ρ i y) y).mpr rfl⟩
      · intro hy ha
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hy
        exact b.2 (((hmem i b.1 y).mp hb).symm.trans ((hmem i a y).mp ha))
    rw [heq]
    exact isOpen_iUnion fun b ↦ (Z b.1).isOpen
  refine ⟨Z, ⟨hclosed, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b hab
    apply disjoint_iff.mpr
    apply SetLike.ext
    intro x
    change (x ∈ Z a ∧ x ∈ Z b) ↔ False
    refine ⟨fun ⟨hxa, hxb⟩ ↦ ?_, False.elim⟩
    obtain ⟨i, y, rfl⟩ := hsurj x
    exact hab (((hmem i a y).mp hxa).symm.trans ((hmem i b y).mp hxb))
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, rfl⟩ := hsurj x
    exact Set.mem_iUnion.mpr ⟨ρ i y, (hmem i (ρ i y) y).mpr rfl⟩
  · intro i a
    ext x
    exact hmem i a x
  · intro V h σ hσ a
    have hcover : Presieve.ofArrows (fun i ↦ pullback (f i) h)
        (fun i ↦ pullback.snd (f i) h) ∈ Scheme.fpqcPrecoverage V :=
      Precoverage.mem_coverings_of_isPullback f hf h
        (fun i ↦ pullback.snd (f i) h) (fun i ↦ pullback.fst (f i) h)
        (fun i ↦ (IsPullback.of_hasPullback (f i) h).flip)
    have heq : h ⁻¹' (Z a : Set X) = σ ⁻¹' {a} := by
      ext z
      obtain ⟨Y, g, hg, t, ht⟩ := Scheme.JointlySurjective.exists_eq
        (K := Scheme.precoverage @Flat) _ hcover.2 z
      obtain ⟨i⟩ := hg
      subst z
      have hcomm := congrArg (fun g : pullback (f i) h ⟶ X ↦ g t)
        (pullback.condition (f := f i) (g := h))
      change f i (pullback.fst (f i) h t) = h (pullback.snd (f i) h t) at hcomm
      change h (pullback.snd (f i) h t) ∈ Z a ↔ σ (pullback.snd (f i) h t) = a
      rw [← hcomm, hmem]
      exact congrArg (fun b : A ↦ b = a) (congrFun (hσ i) t) |>.to_iff
    refine ⟨heq, ?_⟩
    rw [← heq]
    exact ⟨(hclosed a).preimage h.continuous, (Z a).isOpen.preimage h.continuous⟩
  · intro Z' hZ'
    funext a
    apply SetLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := hsurj x
    have heq := congrArg (fun s : Set (U i) ↦ y ∈ s) (hZ'.2.2.2.1 i a)
    exact heq.to_iff.trans (hmem i a y).symm

end AlgebraicGeometry
