/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Convergence of a first quadrant cohomological spectral sequence

Mathlib knows about spectral sequences (`CategoryTheory.SpectralSequence`) but has no notion of
convergence or of an abutment. This file adds the little that the Grothendieck and
Čech-to-derived spectral sequences need.

For a first quadrant cohomological spectral sequence `E` starting at the `E₂`-page (that is, a
term of `CategoryTheory.E₂CohomologicalSpectralSequenceNat C`) both differentials into and out of
the spot `(p, q)` vanish as soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)`
become constant. `SpectralSequence.pageInfinity` picks out this stable value at the explicit
page `p + q + 2`; no degeneration hypothesis is needed.

`SpectralSequence.Abutment E H` then bundles the data that the image filtration of a first
quadrant double complex produces: a decreasing filtration
`H n = F⁰ ⊇ F¹ ⊇ ⋯ ⊇ Fⁿ ⊇ Fⁿ⁺¹ = 0` of the `n`-th graded piece of the abutment by subobjects,
together with isomorphisms `Fᵖ / Fᵖ⁺¹ ≅ E∞^{p, q}` for `p + q = n`. Since the filtration and
the isomorphisms are genuine data, this is a structure; the `Prop`-valued statement used in the
theorems that consume it is `SpectralSequence.AbutsTo E H`, its `Nonempty`.

## Main definitions

- `CategoryTheory.SpectralSequence.pageInfinity`: the `E∞`-term of a first quadrant
  cohomological spectral sequence, as the stable value of the pages.
- `CategoryTheory.SpectralSequence.Abutment`: a filtration of a graded object exhibiting it as
  the abutment of a first quadrant cohomological spectral sequence.
- `CategoryTheory.SpectralSequence.AbutsTo`: the associated `Prop`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The `E∞`-term of a first quadrant cohomological spectral sequence at the spot `(p, q)`.

In the first quadrant both differentials into and out of `(p, q)` vanish on the `r`-th page as
soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)` are canonically isomorphic for
all large `r`; we read off this stable value on the page `p + q + 2`. -/
noncomputable def SpectralSequence.pageInfinity (E : E₂CohomologicalSpectralSequenceNat C)
    (pq : ℕ × ℕ) : C :=
  (E.page (pq.1 + pq.2 + 2 : ℕ)).X pq

/-- The data exhibiting the `ℕ`-graded object `H` of `C` as the abutment of the first quadrant
cohomological spectral sequence `E`: a decreasing filtration of each `H n` by subobjects, which
is exhaustive (`F⁰ = ⊤`) and separated in the strong first quadrant sense (`Fⁿ⁺¹ = ⊥`), whose
successive quotients are the `E∞`-terms of total degree `n`. This is the filtration that the
image filtration on the total complex of a first quadrant double complex produces.

(blueprint: `sk-def-groth-ss`) -/
structure SpectralSequence.Abutment (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) where
  /-- The `p`-th step of the decreasing filtration of `H n`. -/
  filtration (n p : ℕ) : Subobject (H n)
  /-- The filtration is decreasing. -/
  filtration_succ_le (n p : ℕ) : filtration n (p + 1) ≤ filtration n p
  /-- The filtration is exhaustive. -/
  filtration_zero (n : ℕ) : filtration n 0 = ⊤
  /-- The filtration is separated: in the first quadrant it stops in degree `n`. -/
  filtration_succ_self (n : ℕ) : filtration n (n + 1) = ⊥
  /-- The successive quotients of the filtration are the `E∞`-terms. -/
  nonempty_gradedIso (n p q : ℕ) (hpq : p + q = n) :
    Nonempty (cokernel (Subobject.ofLE _ _ (filtration_succ_le n p)) ≅ E.pageInfinity (p, q))

/-- A first quadrant cohomological spectral sequence `E` *abuts to* the `ℕ`-graded object `H`
if there exists a `SpectralSequence.Abutment E H`, that is, a finite decreasing filtration of
each `H n` whose successive quotients are the `E∞`-terms `E∞^{p, q}` with `p + q = n`. -/
def SpectralSequence.AbutsTo (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) : Prop :=
  Nonempty (E.Abutment H)

/-- Transport of an abutment along isomorphisms of the graded object. -/
noncomputable def SpectralSequence.Abutment.ofIso {E : E₂CohomologicalSpectralSequenceNat C}
    {H H' : ℕ → C} (h : E.Abutment H) (e : ∀ n, H n ≅ H' n) : E.Abutment H' where
  filtration n p := Subobject.mapIsoToOrderIso (e n) (h.filtration n p)
  filtration_succ_le n p := (Subobject.mapIsoToOrderIso (e n)).monotone (h.filtration_succ_le n p)
  filtration_zero n := by rw [h.filtration_zero, OrderIso.map_top]
  filtration_succ_self n := by rw [h.filtration_succ_self, OrderIso.map_bot]
  nonempty_gradedIso n p q hpq := by
    obtain ⟨i⟩ := h.nonempty_gradedIso n p q hpq
    exact ⟨Subobject.cokernelOfLEMapIso (e n).hom _ _ (h.filtration_succ_le n p) _ ≪≫ i⟩

/-- Convergence of a spectral sequence is invariant under isomorphisms of the abutment. -/
theorem SpectralSequence.AbutsTo.of_iso {E : E₂CohomologicalSpectralSequenceNat C}
    {H H' : ℕ → C} (h : E.AbutsTo H) (e : ∀ n, H n ≅ H' n) : E.AbutsTo H' :=
  let ⟨a⟩ := h
  ⟨a.ofIso e⟩

/-- Convergence of a spectral sequence is invariant under (unspecified) isomorphisms of the
abutment. -/
theorem SpectralSequence.AbutsTo.of_nonempty_iso {E : E₂CohomologicalSpectralSequenceNat C}
    {H H' : ℕ → C} (h : E.AbutsTo H) (e : ∀ n, Nonempty (H n ≅ H' n)) : E.AbutsTo H' :=
  h.of_iso fun n ↦ (e n).some

end CategoryTheory
