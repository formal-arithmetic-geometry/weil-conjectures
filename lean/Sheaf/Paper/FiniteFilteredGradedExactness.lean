/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Finite filtered graded exactness

Source: Stacks Project, Homology, Tag 05QH, lemma-filtered-acyclic,
parts (1)--(5), with the finite filtrations of Tag 0121
(blueprint: lem-trf-finite-filtered-graded-exactness).

The filtered objects, filtration-preserving maps, filtration steps, graded pieces and the
canonical step and graded maps are the recorded ones of `def-sp-filtration`
(`CategoryTheory.FilteredObject` over `CategoryTheory.DecreasingFiltration`, with
`FilteredObject.restrictionSteps` and `FilteredObject.gradedMapSteps`).

## Main definitions

- `CategoryTheory.FilteredObject.IsStrict`: strict filtered maps.
- `CategoryTheory.FilteredObject.quotientObject`, `CategoryTheory.FilteredObject.quotientMap`:
  the quotients `A/FᵖA` and the induced maps.

## Main statements

- `CategoryTheory.FilteredObject.finite_filtered_graded_exactness`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

/-- A filtered map `f : M → N` is strict when `f(FᵖM) = im(f) ∩ FᵖN` for every
integer `p`, as subobjects of `N`.
Source: Stacks Project, Homology, Tag 05QH, part (4)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
def IsStrict {A B : FilteredObject C} (f : A ⟶ B) : Prop :=
  ∀ p : ℤ,
    imageSubobject (restrictionSteps f p ≫ (B.filtration.step p).arrow) =
      imageSubobject f.hom ⊓ B.filtration.step p

/-- The `p`-th quotient object `A/FᵖA` of a filtered object: the cokernel of the
inclusion of the `p`-th filtration step.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
noncomputable def quotientObject (A : FilteredObject C) (p : ℤ) : C :=
  cokernel (A.filtration.step p).arrow

/-- A filtered map composed with the projection onto `B/FᵖB` kills `FᵖA`.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: by `f.preserves p`, the inclusion `FᵖA → A` followed by `f` factors through
the inclusion `FᵖB → B`, which the cokernel projection of `B` kills. -/
theorem quotientMap_condition {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (A.filtration.step p).arrow ≫ f.hom ≫
      cokernel.π (B.filtration.step p).arrow = 0 := by
  obtain ⟨g, hg⟩ := f.preserves p
  rw [← Category.assoc, ← hg, Category.assoc, cokernel.condition, comp_zero]

/-- The map `A/FᵖA → B/FᵖB` induced by a filtered map, by the cokernel universal
property.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
noncomputable def quotientMap {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    quotientObject A p ⟶ quotientObject B p :=
  cokernel.desc (A.filtration.step p).arrow
    (f.hom ≫ cokernel.π (B.filtration.step p).arrow)
    (quotientMap_condition f p)

/-- The induced quotient maps of a filtered complex `vu = 0` compose to zero.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: precompose with the epimorphic cokernel projection of `X`; by the two
`cokernel.π_desc` equations the composite becomes `u ≫ v ≫ π = 0`. -/
theorem quotientMap_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    quotientMap u p ≫ quotientMap v p = 0 := by
  apply (cancel_epi (cokernel.π (X.filtration.step p).arrow)).1
  simp only [quotientMap, quotientObject, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc, comp_zero]
  rw [← Category.assoc, hvu, zero_comp]

/-- The induced maps on `p`-th filtration steps of a filtered complex `vu = 0`
compose to zero.
Source: Stacks Project, Homology, Tag 05QH, part (2)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: postcompose with the monic inclusion `FᵖZ → Z`; by the defining equations of
`restrictionSteps` the composite becomes `FᵖX → X` followed by `u ≫ v = 0`. -/
theorem restrictionSteps_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    restrictionSteps u p ≫ restrictionSteps v p = 0 := by
  have hV : restrictionSteps v p ≫ (Z.filtration.step p).arrow =
      (Y.filtration.step p).arrow ≫ v.hom := Classical.choose_spec (v.preserves p)
  have hU : restrictionSteps u p ≫ (Y.filtration.step p).arrow =
      (X.filtration.step p).arrow ≫ u.hom := Classical.choose_spec (u.preserves p)
  apply (cancel_mono (Z.filtration.step p).arrow).1
  rw [Category.assoc, hV, ← Category.assoc, hU,
    Category.assoc, hvu, comp_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The induced maps on `p`-th graded pieces of a filtered complex `vu = 0` compose
to zero.
Source: Stacks Project, Homology, Tag 05QH, parts (1)--(3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: precompose with the epimorphic cokernel projection `FᵖX → grᵖX`; by
`exists_gradedMap_steps` the composite becomes the composite of the restrictions
followed by a projection, which vanishes by `restrictionSteps_comp`. -/
theorem gradedMapSteps_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    gradedMapSteps u p ≫ gradedMapSteps v p = 0 := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (X.filtration.step (p + 1))
    (X.filtration.step p) (X.filtration.antitone_step (by omega))))).1
  simp only [gradedMapSteps]
  rw [← Category.assoc, Classical.choose_spec (exists_gradedMap_steps X Y u p),
    Category.assoc, Classical.choose_spec (exists_gradedMap_steps Y Z v p)]
  rw [← Category.assoc, restrictionSteps_comp u v hvu p, zero_comp, comp_zero]

private theorem restriction_fac {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    restrictionSteps f p ≫ (B.filtration.step p).arrow =
      (A.filtration.step p).arrow ≫ f.hom := Classical.choose_spec (f.preserves p)

private theorem restriction_naturality {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    Subobject.ofLE (A.filtration.step (p + 1)) (A.filtration.step p)
        (A.filtration.antitone_step (by omega)) ≫ restrictionSteps f p =
      restrictionSteps f (p + 1) ≫ Subobject.ofLE (B.filtration.step (p + 1))
        (B.filtration.step p) (B.filtration.antitone_step (by omega)) := by
  rw [← cancel_mono (B.filtration.step p).arrow]
  simp only [Category.assoc, restriction_fac, Subobject.ofLE_arrow]
  rw [← Category.assoc, Subobject.ofLE_arrow]

private theorem quotient_fac {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    cokernel.π (A.filtration.step p).arrow ≫ quotientMap f p =
      f.hom ≫ cokernel.π (B.filtration.step p).arrow := cokernel.π_desc _ _ _

private theorem exact_extension {L M N : ShortComplex C}
    (i : L ⟶ M) (q : M ⟶ N)
    (w₂ : i.τ₂ ≫ q.τ₂ = 0)
    (h₂ : (ShortComplex.mk i.τ₂ q.τ₂ w₂).Exact)
    [Mono i.τ₂] [Mono i.τ₃] [Epi q.τ₁]
    (hL : L.Exact) (hN : N.Exact) : M.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A y hy
  have hyq : (y ≫ q.τ₂) ≫ N.g = 0 := by
    rw [Category.assoc, q.comm₂₃, ← Category.assoc, hy, zero_comp]
  obtain ⟨A₁, e₁, he₁, x₃, hx₃⟩ := hN.exact_up_to_refinements (y ≫ q.τ₂) hyq
  obtain ⟨A₂, e₂, he₂, x₂, hx₂⟩ := surjective_up_to_refinements_of_epi q.τ₁ x₃
  let d : A₂ ⟶ M.X₂ := e₂ ≫ e₁ ≫ y - x₂ ≫ M.f
  have hd : d ≫ q.τ₂ = 0 := by
    dsimp [d]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hx₃,
      ← Category.assoc e₂ x₃, hx₂, Category.assoc, q.comm₁₂,
      Category.assoc, sub_self]
  obtain ⟨y₁, hy₁⟩ := h₂.lift' d hd
  have hy₁g : y₁ ≫ L.g = 0 := by
    apply (cancel_mono i.τ₃).1
    rw [Category.assoc, ← i.comm₂₃, ← Category.assoc, hy₁]
    simp [d, Category.assoc, hy, M.zero]
  obtain ⟨A₃, e₃, he₃, x₁, hx₁⟩ := hL.exact_up_to_refinements y₁ hy₁g
  refine ⟨A₃, e₃ ≫ e₂ ≫ e₁, inferInstance, x₁ ≫ i.τ₁ + e₃ ≫ x₂, ?_⟩
  rw [Preadditive.add_comp, Category.assoc x₁, i.comm₁₂,
    ← Category.assoc x₁, ← hx₁, Category.assoc e₃ y₁, hy₁]
  dsimp [d]
  simp only [Preadditive.comp_sub, Category.assoc]
  abel

set_option backward.isDefEq.respectTransparency false in
private theorem step_exact_of_succ {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ)
    (hs : (ShortComplex.mk (restrictionSteps u (p + 1))
      (restrictionSteps v (p + 1)) (restrictionSteps_comp u v hvu (p + 1))).Exact)
    (hg : (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
      (gradedMapSteps_comp u v hvu p)).Exact) :
    (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
      (restrictionSteps_comp u v hvu p)).Exact := by
  let i (A : FilteredObject C) := Subobject.ofLE (A.filtration.step (p + 1))
    (A.filtration.step p) (A.filtration.antitone_step (by omega))
  let L := ShortComplex.mk (restrictionSteps u (p + 1)) (restrictionSteps v (p + 1))
    (restrictionSteps_comp u v hvu (p + 1))
  let M := ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
    (restrictionSteps_comp u v hvu p)
  let N := ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
    (gradedMapSteps_comp u v hvu p)
  let a : L ⟶ M :=
    { τ₁ := i X
      τ₂ := i Y
      τ₃ := i Z
      comm₁₂ := restriction_naturality u p
      comm₂₃ := restriction_naturality v p }
  let b : M ⟶ N :=
    { τ₁ := cokernel.π (i X)
      τ₂ := cokernel.π (i Y)
      τ₃ := cokernel.π (i Z)
      comm₁₂ := Classical.choose_spec (exists_gradedMap_steps X Y u p)
      comm₂₃ := Classical.choose_spec (exists_gradedMap_steps Y Z v p) }
  exact exact_extension a b (cokernel.condition (i Y))
    (ShortComplex.cokernelSequence_exact (i Y)) hs hg

private theorem step_eq_bot {A : FilteredObject C} {m p : ℤ}
    (hm : A.filtration.step m = ⊥) (hp : m ≤ p) : A.filtration.step p = ⊥ := by
  apply le_antisymm _ bot_le
  simpa [hm] using A.filtration.antitone_step hp

private theorem step_eq_top {A : FilteredObject C} {n p : ℤ}
    (hn : A.filtration.step n = ⊤) (hp : p ≤ n) : A.filtration.step p = ⊤ := by
  apply top_unique
  rw [← hn]
  exact A.filtration.antitone_step hp

private theorem all_steps_exact {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hY : Y.filtration.IsFinite)
    (hgr : ∀ p : ℤ, (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
      (gradedMapSteps_comp u v hvu p)).Exact) :
    ∀ p : ℤ, (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
      (restrictionSteps_comp u v hvu p)).Exact := by
  obtain ⟨n, m, hn, hm⟩ := hY
  have hz (p : ℤ) (hp : m ≤ p) :
      (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
        (restrictionSteps_comp u v hvu p)).Exact := by
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (Y.filtration.step p : C)
    rw [step_eq_bot hm hp]
    exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
  have hi : ∀ k : ℕ, ∀ p : ℤ, m ≤ p + k →
      (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
        (restrictionSteps_comp u v hvu p)).Exact := by
    intro k
    induction k with
    | zero => intro p hp; exact hz p (by simpa using hp)
    | succ k ih =>
      intro p hp
      exact step_exact_of_succ u v hvu p (ih (p + 1) (by omega)) (hgr p)
  intro p
  exact hi (m - p).toNat p (by omega)

private theorem underlying_exact {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hX : X.filtration.IsFinite) (hY : Y.filtration.IsFinite)
    (hs : ∀ p : ℤ, (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
      (restrictionSteps_comp u v hvu p)).Exact) :
    (ShortComplex.mk u.hom v.hom hvu).Exact := by
  obtain ⟨nx, mx, hnx, hmx⟩ := hX
  obtain ⟨ny, my, hny, hmy⟩ := hY
  let p := min nx ny
  have : IsIso (X.filtration.step p).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (step_eq_top hnx (min_le_left _ _))
  have : IsIso (Y.filtration.step p).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (step_eq_top hny (min_le_right _ _))
  let φ : ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
      (restrictionSteps_comp u v hvu p) ⟶ ShortComplex.mk u.hom v.hom hvu :=
    { τ₁ := (X.filtration.step p).arrow
      τ₂ := (Y.filtration.step p).arrow
      τ₃ := (Z.filtration.step p).arrow
      comm₁₂ := (restriction_fac u p).symm
      comm₂₃ := (restriction_fac v p).symm }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (hs p)

private noncomputable def nextInclusion (A : FilteredObject C) (p : ℤ) :=
  Subobject.ofLE (A.filtration.step (p + 1)) (A.filtration.step p)
    (A.filtration.antitone_step (by omega))

private noncomputable def gradedToQuotient (A : FilteredObject C) (p : ℤ) :
    A.filtration.gradedPiece p ⟶ quotientObject A (p + 1) :=
  cokernel.desc (nextInclusion A p)
    ((A.filtration.step p).arrow ≫ cokernel.π (A.filtration.step (p + 1)).arrow)
    (by simp [nextInclusion, ← Category.assoc])

private noncomputable def quotientTransition (A : FilteredObject C) (p : ℤ) :
    quotientObject A (p + 1) ⟶ quotientObject A p :=
  cokernel.desc (A.filtration.step (p + 1)).arrow
    (cokernel.π (A.filtration.step p).arrow)
    (by rw [← Subobject.ofLE_arrow (A.filtration.antitone_step (show p ≤ p + 1 by omega)),
      Category.assoc, cokernel.condition, comp_zero])

private theorem gradedToQuotient_fac (A : FilteredObject C) (p : ℤ) :
    cokernel.π (nextInclusion A p) ≫ gradedToQuotient A p =
      (A.filtration.step p).arrow ≫ cokernel.π (A.filtration.step (p + 1)).arrow :=
  cokernel.π_desc _ _ _

private theorem quotientTransition_fac (A : FilteredObject C) (p : ℤ) :
    cokernel.π (A.filtration.step (p + 1)).arrow ≫ quotientTransition A p =
      cokernel.π (A.filtration.step p).arrow := cokernel.π_desc _ _ _

private instance quotientTransition_epi (A : FilteredObject C) (p : ℤ) :
    Epi (quotientTransition A p) := epi_of_epi_fac (quotientTransition_fac A p)

private theorem graded_quotient_zero (A : FilteredObject C) (p : ℤ) :
    gradedToQuotient A p ≫ quotientTransition A p = 0 := by
  apply (cancel_epi (cokernel.π (nextInclusion A p))).1
  rw [← Category.assoc, gradedToQuotient_fac, Category.assoc,
    quotientTransition_fac, cokernel.condition, comp_zero]

private theorem graded_quotient_exact (A : FilteredObject C) (p : ℤ) :
    (ShortComplex.mk (gradedToQuotient A p) (quotientTransition A p)
      (graded_quotient_zero A p)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T y hy
  obtain ⟨T₁, e₁, he₁, a, ha⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π (A.filtration.step (p + 1)).arrow) y
  have hap : a ≫ cokernel.π (A.filtration.step p).arrow = 0 := by
    rw [← quotientTransition_fac A p, ← Category.assoc, ← ha, Category.assoc, hy,
      comp_zero]
  let b := Abelian.monoLift (A.filtration.step p).arrow a hap
  refine ⟨T₁, e₁, inferInstance, b ≫ cokernel.π (nextInclusion A p), ?_⟩
  rw [ha, Category.assoc, gradedToQuotient_fac, ← Category.assoc,
    Abelian.monoLift_comp]

private instance gradedToQuotient_mono (A : FilteredObject C) (p : ℤ) :
    Mono (gradedToQuotient A p) := by
  apply Preadditive.mono_of_cancel_zero
  intro T z hz
  obtain ⟨T₁, e₁, he₁, a, ha⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π (nextInclusion A p)) z
  have ha0 : (a ≫ (A.filtration.step p).arrow) ≫
      cokernel.π (A.filtration.step (p + 1)).arrow = 0 := by
    rw [Category.assoc, ← gradedToQuotient_fac, ← Category.assoc, ← ha,
      Category.assoc, hz, comp_zero]
  let b := Abelian.monoLift (A.filtration.step (p + 1)).arrow
    (a ≫ (A.filtration.step p).arrow) ha0
  have hb : b ≫ nextInclusion A p = a := by
    apply (cancel_mono (A.filtration.step p).arrow).1
    rw [Category.assoc]
    simp only [nextInclusion, Subobject.ofLE_arrow]
    exact Abelian.monoLift_comp _ _ _
  rw [← cancel_epi e₁, comp_zero, ha, ← hb, Category.assoc, cokernel.condition,
    comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem gradedToQuotient_naturality {A B : FilteredObject C}
    (f : A ⟶ B) (p : ℤ) :
    gradedToQuotient A p ≫ quotientMap f (p + 1) =
      gradedMapSteps f p ≫ gradedToQuotient B p := by
  apply (cancel_epi (cokernel.π (nextInclusion A p))).1
  rw [← Category.assoc, gradedToQuotient_fac]
  have hgr := Classical.choose_spec (exists_gradedMap_steps A B f p)
  change cokernel.π (nextInclusion A p) ≫ gradedMapSteps f p =
    restrictionSteps f p ≫ cokernel.π (nextInclusion B p) at hgr
  rw [← Category.assoc, hgr]
  simp only [Category.assoc, gradedToQuotient_fac, quotient_fac]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ cokernel.π (B.filtration.step (p + 1)).arrow)
      (restriction_fac f p).symm

private theorem quotientTransition_naturality {A B : FilteredObject C}
    (f : A ⟶ B) (p : ℤ) :
    quotientTransition A p ≫ quotientMap f p =
      quotientMap f (p + 1) ≫ quotientTransition B p := by
  apply (cancel_epi (cokernel.π (A.filtration.step (p + 1)).arrow)).1
  rw [← Category.assoc, quotientTransition_fac, quotient_fac,
    ← Category.assoc, quotient_fac, Category.assoc, quotientTransition_fac]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_exact_of_prev {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ)
    (hq : (ShortComplex.mk (quotientMap u p) (quotientMap v p)
      (quotientMap_comp u v hvu p)).Exact)
    (hg : (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
      (gradedMapSteps_comp u v hvu p)).Exact) :
    (ShortComplex.mk (quotientMap u (p + 1)) (quotientMap v (p + 1))
      (quotientMap_comp u v hvu (p + 1))).Exact := by
  let L := ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
    (gradedMapSteps_comp u v hvu p)
  let M := ShortComplex.mk (quotientMap u (p + 1)) (quotientMap v (p + 1))
    (quotientMap_comp u v hvu (p + 1))
  let N := ShortComplex.mk (quotientMap u p) (quotientMap v p)
    (quotientMap_comp u v hvu p)
  let a : L ⟶ M :=
    { τ₁ := gradedToQuotient X p
      τ₂ := gradedToQuotient Y p
      τ₃ := gradedToQuotient Z p
      comm₁₂ := gradedToQuotient_naturality u p
      comm₂₃ := gradedToQuotient_naturality v p }
  let b : M ⟶ N :=
    { τ₁ := quotientTransition X p
      τ₂ := quotientTransition Y p
      τ₃ := quotientTransition Z p
      comm₁₂ := quotientTransition_naturality u p
      comm₂₃ := quotientTransition_naturality v p }
  exact exact_extension a b (graded_quotient_zero Y p) (graded_quotient_exact Y p) hg hq

private theorem all_quotients_exact {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hY : Y.filtration.IsFinite)
    (hgr : ∀ p : ℤ, (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
      (gradedMapSteps_comp u v hvu p)).Exact) :
    ∀ p : ℤ, (ShortComplex.mk (quotientMap u p) (quotientMap v p)
      (quotientMap_comp u v hvu p)).Exact := by
  obtain ⟨n, m, hn, hm⟩ := hY
  have hz (p : ℤ) (hp : p ≤ n) :
      (ShortComplex.mk (quotientMap u p) (quotientMap v p)
        (quotientMap_comp u v hvu p)).Exact := by
    have : IsIso (Y.filtration.step p).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (step_eq_top hn hp)
    apply ShortComplex.exact_of_isZero_X₂
    exact isZero_cokernel_of_epi _
  have hi : ∀ k : ℕ, ∀ p : ℤ, p ≤ n + k →
      (ShortComplex.mk (quotientMap u p) (quotientMap v p)
        (quotientMap_comp u v hvu p)).Exact := by
    intro k
    induction k with
    | zero => intro p hp; exact hz p (by simpa using hp)
    | succ k ih =>
      intro p hp
      have h := quotient_exact_of_prev u v hvu (p - 1)
        (ih (p - 1) (by omega)) (hgr (p - 1))
      have hp1 : p - 1 + 1 = p := by omega
      rw [hp1] at h
      exact h
  intro p
  exact hi (p - n).toNat p (by omega)

private theorem le_image_of_refinement {A B T : C} (f : A ⟶ B) (P : Subobject B)
    (e : T ⟶ (P : C)) [Epi e] (a : T ⟶ A) (ha : e ≫ P.arrow = a ≫ f) :
    P ≤ imageSubobject f := by
  have h := imageSubobject_comp_le a f
  rw [← ha, imageSubobject_comp_eq_of_epi, imageSubobject_mono, Subobject.mk_arrow] at h
  exact h

private theorem strict_first {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hs : ∀ p : ℤ, (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
      (restrictionSteps_comp u v hvu p)).Exact) : IsStrict u := by
  intro p
  simp only [restriction_fac]
  apply le_antisymm
  · apply le_inf
    · exact imageSubobject_comp_le _ _
    · simpa only [restriction_fac] using
        imageSubobject_le (restrictionSteps u p ≫ (Y.filtration.step p).arrow)
          (restrictionSteps u p) rfl
  · let P := imageSubobject u.hom ⊓ Y.filtration.step p
    let a := Subobject.ofLE P (Y.filtration.step p) inf_le_right
    have hav : a ≫ restrictionSteps v p = 0 := by
      apply (cancel_mono (Z.filtration.step p).arrow).1
      rw [Category.assoc, restriction_fac, ← Category.assoc, Subobject.ofLE_arrow]
      have hPv : P.arrow ≫ v.hom = 0 := by
        rw [← Subobject.ofLE_arrow (show P ≤ imageSubobject u.hom from inf_le_left),
          Category.assoc, imageSubobject_arrow_comp_eq_zero hvu, comp_zero]
      rw [hPv, zero_comp]
    obtain ⟨T, e, he, x, hx⟩ := (hs p).exact_up_to_refinements a hav
    apply le_image_of_refinement _ P e x
    rw [← Subobject.ofLE_arrow (show P ≤ Y.filtration.step p from inf_le_right),
      ← Category.assoc, hx, Category.assoc, restriction_fac]

private theorem strict_second {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hq : ∀ p : ℤ, (ShortComplex.mk (quotientMap u p) (quotientMap v p)
      (quotientMap_comp u v hvu p)).Exact) : IsStrict v := by
  intro p
  simp only [restriction_fac]
  apply le_antisymm
  · apply le_inf
    · exact imageSubobject_comp_le _ _
    · simpa only [restriction_fac] using
        imageSubobject_le (restrictionSteps v p ≫ (Z.filtration.step p).arrow)
          (restrictionSteps v p) rfl
  · let P := imageSubobject v.hom ⊓ Z.filtration.step p
    let t := Subobject.ofLE P (imageSubobject v.hom) inf_le_left
    obtain ⟨T₁, e₁, he₁, y, hy⟩ :=
      surjective_up_to_refinements_of_epi (factorThruImageSubobject v.hom) t
    have hyv : e₁ ≫ P.arrow = y ≫ v.hom := by
      rw [← Subobject.ofLE_arrow (show P ≤ imageSubobject v.hom from inf_le_left),
        ← Category.assoc, hy, Category.assoc, imageSubobject_arrow_comp]
    have hyq : (y ≫ cokernel.π (Y.filtration.step p).arrow) ≫ quotientMap v p = 0 := by
      rw [Category.assoc, quotient_fac, ← Category.assoc, ← hyv]
      rw [Category.assoc,
        ← Subobject.ofLE_arrow (show P ≤ Z.filtration.step p from inf_le_right)]
      simp only [Category.assoc, cokernel.condition, comp_zero]
    obtain ⟨T₂, e₂, he₂, xq, hxq⟩ := (hq p).exact_up_to_refinements
      (y ≫ cokernel.π (Y.filtration.step p).arrow) hyq
    obtain ⟨T₃, e₃, he₃, x, hx⟩ :=
      surjective_up_to_refinements_of_epi (cokernel.π (X.filtration.step p).arrow) xq
    let d : T₃ ⟶ Y.obj := e₃ ≫ e₂ ≫ y - x ≫ u.hom
    have hd : d ≫ cokernel.π (Y.filtration.step p).arrow = 0 := by
      dsimp [d]
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hxq,
        ← Category.assoc e₃ xq, hx, Category.assoc, quotient_fac,
        Category.assoc, sub_self]
    let b := Abelian.monoLift (Y.filtration.step p).arrow d hd
    apply le_image_of_refinement _ P (e₃ ≫ e₂ ≫ e₁) b
    rw [← Category.assoc b, Abelian.monoLift_comp]
    simp only [Category.assoc, hyv, d, Preadditive.sub_comp, hvu, comp_zero, sub_zero]

/-- Graded exactness implies strict exactness for finite filtered objects: for
filtration-preserving maps `X → Y → Z` of finitely filtered objects with `vu = 0` and
exact `grᵖX → grᵖY → grᵖZ` for every `p`, the maps `u` and `v` are strict, `X → Y → Z`
is exact, and for every `p` both `FᵖX → FᵖY → FᵖZ` and `X/FᵖX → Y/FᵖY → Z/FᵖZ` are exact.

Source: Stacks Project, Homology, Tag 05QH, lemma-filtered-acyclic, parts (1)--(5)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof.
1. Choose common integers `a ≤ b` with `FᵃT = T` and `FᵇT = 0` for `T = X, Y, Z`: `a` the
   minimum of the three whole-object bounds, `b` the maximum of `a` and the three zero
   bounds [def-sp-filtration]. Put `K = (X → Y → Z)` in degrees `0, 1, 2`. As `vu = 0`
   it is a complex; filtration preservation makes each `FᵖK` a subcomplex, and `K/FᵖK`,
   `grᵖK = FᵖK/Fᵖ⁺¹K` carry the induced differentials. `H¹` of a three-term complex is
   the kernel of the second map modulo the image of the first, so the hypothesis says
   `H¹(grᵖK) = 0` for every `p`.
2. Prove `H¹(FᵖK) = 0` by descending induction from `b` (zero for `p ≥ b`). The sequence
   `0 → Fᵖ⁺¹K → FᵖK → grᵖK → 0` is termwise short exact. The helper
   `exact_extension` proves exactness of its middle short complex directly: refine a
   cycle along an epimorphism to lift its boundary in the quotient, subtract that
   boundary, factor the difference through the subcomplex, and use its exactness.
   This is the usual proof of the vanishing consequence of the long exact sequence.
   For `p ≤ a` the complex is `K`; the step inclusions at a common lower bound
   identify step exactness with exactness of `X → Y → Z`.
3. Prove `H¹(K/FᵖK) = 0` by ascending induction from `a` (zero for `p ≤ a`). The sequence
   `0 → grᵖK → K/Fᵖ⁺¹K → K/FᵖK → 0` is termwise short exact. Construct its maps
   by cokernel descent and prove the first is monic using successive inclusions and
   the kernel property of a monomorphism and its cokernel. The same `exact_extension`
   helper then proves the induction step. Starting at any `p ≤ a` and iterating gives
   exactness for every quotient `X/FᵖX → Y/FᵖY → Z/FᵖZ`.
4. Strictness of `u`: as subobjects of `Y`,
   `u(FᵖX) = ker(v|FᵖY) = ker(v) ∩ FᵖY = im(u) ∩ FᵖY`, by step exactness, the pullback
   description of the kernel along `FᵖY → Y`, and underlying exactness.
5. Strictness of `v`: with `q : Y → Y/FᵖY` and the induced `ū, v̄`, the square defining
   `v̄` gives `v⁻¹(FᵖZ) = q⁻¹(ker v̄)`; quotient exactness gives
   `ker v̄ = im ū = q(im u)`, as `X → X/FᵖX` is epi. Hence `v⁻¹(FᵖZ) = FᵖY + im u`, and
   `im(v) ∩ FᵖZ = v(v⁻¹(FᵖZ)) = v(FᵖY + im u) = v(FᵖY)` because `vu = 0`. These are
   subobject inverse-image, sum and image identities; no element is lifted. -/
theorem finite_filtered_graded_exactness
    {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z)
    (hvu : u.hom ≫ v.hom = 0)
    (hX : DecreasingFiltration.IsFinite X.filtration)
    (hY : DecreasingFiltration.IsFinite Y.filtration)
    (hZ : DecreasingFiltration.IsFinite Z.filtration)
    (hgr : ∀ p : ℤ,
      (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
        (gradedMapSteps_comp u v hvu p)).Exact) :
    FilteredObject.IsStrict u ∧
      FilteredObject.IsStrict v ∧
      (ShortComplex.mk u.hom v.hom hvu).Exact ∧
      (∀ p : ℤ,
        (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
          (restrictionSteps_comp u v hvu p)).Exact ∧
        (ShortComplex.mk (quotientMap u p) (quotientMap v p)
          (quotientMap_comp u v hvu p)).Exact) := by
  have _finiteZ := hZ
  have hs := all_steps_exact u v hvu hY hgr
  have hq := all_quotients_exact u v hvu hY hgr
  exact ⟨strict_first u v hvu hs, strict_second u v hvu hq,
    underlying_exact u v hvu hX hY hs, fun p ↦ ⟨hs p, hq p⟩⟩

end FilteredObject

end CategoryTheory
