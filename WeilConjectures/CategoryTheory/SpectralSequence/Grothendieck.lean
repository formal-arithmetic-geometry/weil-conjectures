/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The Grothendieck spectral sequence

Let `A ⥤ B ⥤ C` be left exact additive functors such that `F` sends injective objects of `A` to
`G`-acyclic objects of `B`. Then for every `X : A` there is a first quadrant cohomological
spectral sequence with `E₂`-page `R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

Convergence is expressed through `CategoryTheory.SpectralSequence.AbutsTo` of
`WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`; the blueprint's
`sk-def-groth-ss` describes both the acyclicity hypothesis on the pair `(F, G)` and the image
filtration attached to a first quadrant double complex, and the second half of that subsection
is what `SpectralSequence.Abutment` records.

## Main definitions

- `CategoryTheory.Functor.IsAcyclicComposablePair`: a composable pair with acyclicity.

## Main statements

- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`: the Grothendieck spectral
  sequence of a composable pair with acyclicity.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]

/-- The pair of additive functors `A ⥤ B ⥤ C` is a *composable pair with acyclicity* if `F` sends
every injective object `I` of `A` to a `G`-acyclic object of `B`, that is, one at which all the
higher right derived functors `R^q G` for `q > 0` vanish. This is what makes an injective
resolution of `X : A` compute `R^n (F ⋙ G) X` after applying `F`, and hence what makes the
Grothendieck spectral sequence of `Functor.exists_grothendieckSpectralSequence` exist.

(blueprint: `sk-def-groth-ss`) -/
def Functor.IsAcyclicComposablePair (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
  ∀ (I : A) [Injective I] (q : ℕ), 0 < q → IsZero ((G.rightDerived q).obj (F.obj I))

/-- **The Grothendieck spectral sequence.** If `F : A ⥤ B` and `G : B ⥤ C` are left exact
additive functors forming a composable pair with acyclicity

```
    A ───── F ─────▶ B ───── G ─────▶ C
     ╲                                ▲
      ╲───────────── F ⋙ G ──────────╱
```

then for every `X : A` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

For `A` the abelian sheaves on a site `X`, `F = f_*` and `G = h_*` along morphisms of sites
`X ⥤ Y ⥤ Z`, the acyclicity hypothesis holds because `f_*` is right adjoint to the exact functor
`f^{-1}` and hence preserves injectives, and the statement specializes to
`R^p h_* R^q f_* F ⟹ R^{p + q} (h ∘ f)_* F`. Taking `Z` to be the punctual site, so that
`h_* = Γ(Y, -)`, it specializes further to the Leray spectral sequence
`H^p(Y, R^q f_* F) ⟹ H^{p + q}(X, F)`.

(blueprint: `sk-thm-groth-ss`) -/
theorem Functor.exists_grothendieckSpectralSequence (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ,
        Nonempty ((E.page 2).X (p, q) ≅ (G.rightDerived p).obj ((F.rightDerived q).obj X))) ∧
      E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) :=
  sorry

end CategoryTheory
