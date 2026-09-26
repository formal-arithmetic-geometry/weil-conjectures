/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Subobject.Lattice

@[expose] public section

/-!
# The Grothendieck spectral sequence

Let `A ⥤ B ⥤ C` be left exact additive functors between Grothendieck abelian categories such
that `F` sends injective objects of `A` to `G`-acyclic objects of `B`. Then for every `X : A`
there is a first quadrant cohomological spectral sequence with `E₂`-page `R^p G (R^q F X)`
abutting to `R^{p + q} (F ⋙ G) X`.

## Convergence

Mathlib knows about spectral sequences (`CategoryTheory.SpectralSequence`) but has no notion of
convergence or of an abutment, so we introduce the little that is needed here.

For a first quadrant cohomological spectral sequence `E` starting at the `E₂`-page (that is, a
term of `CategoryTheory.E₂CohomologicalSpectralSequenceNat C`) both differentials into and out of
the spot `(p, q)` vanish as soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)`
become constant. `SpectralSequence.pageInfinity` picks out this stable value at the explicit
page `p + q + 2`; no degeneration hypothesis is needed.

`SpectralSequence.Abutment E H` then bundles exactly the data that the blueprint's "image
filtration" of a first quadrant double complex produces: a decreasing filtration
`H n = F⁰ ⊇ F¹ ⊇ ⋯ ⊇ Fⁿ ⊇ Fⁿ⁺¹ = 0` of the `n`-th graded piece of the abutment by subobjects,
together with isomorphisms `Fᵖ / Fᵖ⁺¹ ≅ E∞^{p, q}` for `p + q = n`. Since the filtration and
the isomorphisms are genuine data, this is a structure; the `Prop`-valued statement used in the
theorems below is `SpectralSequence.AbutsTo E H`, its `Nonempty`.

Because the blueprint's `sk-def-groth-ss` describes both the acyclicity hypothesis on the pair
`(F, G)` and the image filtration attached to a first quadrant double complex, the second half of
that subsection is folded into `SpectralSequence.Abutment` / `SpectralSequence.AbutsTo`: the two
spectral sequences of a double complex are not named separately, the only thing used downstream
being the statement that a spectral sequence abuts to a graded object via a filtration whose
successive quotients are the `E∞`-terms.

## Main definitions

- `CategoryTheory.SpectralSequence.pageInfinity`: the `E∞`-term of a first quadrant
  cohomological spectral sequence, as the stable value of the pages.
- `CategoryTheory.SpectralSequence.Abutment`: a filtration of a graded object exhibiting it as
  the abutment of a first quadrant cohomological spectral sequence.
- `CategoryTheory.SpectralSequence.AbutsTo`: the associated `Prop`.
- `CategoryTheory.Functor.IsAcyclicComposablePair`: a composable pair with acyclicity.

## Main statements

- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`: the Grothendieck spectral
  sequence of a composable pair with acyclicity.
-/

universe v u

namespace CategoryTheory

open Limits

section Abutment

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The `E∞`-term of a first quadrant cohomological spectral sequence at the spot `(p, q)`.

In the first quadrant both differentials into and out of `(p, q)` vanish on the `r`-th page as
soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)` are canonically isomorphic for
all large `r`; we read off this stable value on the page `p + q + 2`. -/
noncomputable def SpectralSequence.pageInfinity (E : E₂CohomologicalSpectralSequenceNat C)
    (pq : ℕ × ℕ) : C :=
  (E.page (pq.1 + pq.2 + 2 : ℕ)).X pq

/-- Blueprint `sk-def-groth-ss`: Composable pair with acyclicity; the couple of a double complex.

The data exhibiting the `ℕ`-graded object `H` of `C` as the abutment of the first quadrant
cohomological spectral sequence `E`: a decreasing filtration of each `H n` by subobjects, which
is exhaustive (`F⁰ = ⊤`) and separated in the strong first quadrant sense (`Fⁿ⁺¹ = ⊥`), whose
successive quotients are the `E∞`-terms of total degree `n`. This is the filtration that the
blueprint obtains as the image filtration on the total complex of a first quadrant double
complex. -/
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

end Abutment

section Grothendieck

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- Blueprint `sk-def-groth-ss`: Composable pair with acyclicity; the couple of a double complex.

The pair of additive functors `A ⥤ B ⥤ C` is a *composable pair with acyclicity* if `F` sends
every injective object `I` of `A` to a `G`-acyclic object of `B`, that is, one at which all the
higher right derived functors `R^q G` for `q > 0` vanish. This is what makes an injective
resolution of `X : A` compute `R^n (F ⋙ G) X` after applying `F`, and hence what makes the
Grothendieck spectral sequence of `Functor.exists_grothendieckSpectralSequence` exist.

The blueprint also records that the abutment of such a spectral sequence carries the image
filtration of the associated first quadrant double complex; that part of the subsection is
`SpectralSequence.Abutment`. -/
def Functor.IsAcyclicComposablePair (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
  ∀ (I : A) [Injective I] (q : ℕ), 0 < q → IsZero ((G.rightDerived q).obj (F.obj I))

/-- Blueprint `sk-thm-groth-ss`: Grothendieck spectral sequence and its Leray specialization.

If `F : A ⥤ B` and `G : B ⥤ C` are left exact additive functors between Grothendieck abelian
categories forming a composable pair with acyclicity, then for every `X : A` there is a first
quadrant cohomological spectral sequence with `E₂^{p, q} ≅ R^p G (R^q F X)` abutting to
`R^{p + q} (F ⋙ G) X`.

For `A` the abelian sheaves on a site `X`, `F = f_*` and `G = h_*` along morphisms of sites
`X ⥤ Y ⥤ Z`, the acyclicity hypothesis holds because `f_*` is right adjoint to the exact functor
`f^{-1}` and hence preserves injectives, and the statement specializes to
`R^p h_* R^q f_* F ⟹ R^{p + q} (h ∘ f)_* F`. Taking `Z` to be the punctual site, so that
`h_* = Γ(Y, -)`, it specializes further to the Leray spectral sequence
`H^p(Y, R^q f_* F) ⟹ H^{p + q}(X, F)`. -/
theorem Functor.exists_grothendieckSpectralSequence (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ,
        Nonempty ((E.page 2).X (p, q) ≅ (G.rightDerived p).obj ((F.rightDerived q).obj X))) ∧
      E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) :=
  sorry

end Grothendieck

end CategoryTheory
