/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # A factor algebra with standard smooth reduction

Source: Stacks Project, Tag 07CK, the construction of `A'` before lifting the equations.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

/-- A map into an algebra with ind standard smooth reduction factors through a finitely
presented algebra whose reduction is itself standard smooth.

Source: Stacks Project, Smoothing Ring Maps, Tag 07CK (lemma-lift-once), construction
of `A'` (blueprint: lem-weil-pbc-popescu-standard-reduction-factor).

Proof: Reducing a finite presentation of `A` shows that `A/IA` is finitely presented
over `R/I`. The map induced by `φ` therefore factors through a standard smooth stage
`C` of the given filtered colimit (Tag 00QO). Since `C` is finitely presented over
`R/I` and `A/IA` is finite type over it, `C` is finitely presented over `A/IA`
(Tag 00F4). Write `C = (A/IA)[t]/(gbar)` with finite lists of variables and relations.
Lift the images of the variables to elements `λ` of `Λ`, and lift the coefficients of
`gbar` to polynomials `g` over `A`. Each evaluation `φ(g)(λ)` lies in `IΛ`, because
its image in the quotient is zero by the factorization through `C`. Write it as a
finite sum of products `ε * μ`, with `ε` in `I`. Adjoin one variable `δ` for each
such product and impose the relations `g - sum ε * δ`. Evaluation at `λ` and `μ`
defines the map to `Λ`; its restriction to `A` is `φ`. This quotient is finitely
presented over `A` and therefore over `R`. Modulo `I` the correction terms vanish,
so the reduction is `C[δ]`. Adjoining finitely many variables preserves a standard
smooth presentation: retain the original equations and original invertible Jacobian
minor, with the new variables outside that minor. The finite polynomial quotient
has carrier universe at most `max u v w`; use `ULift` to reach that universe exactly.
This argument also covers empty lists, the zero ring, and `I = top`; it uses no
nilpotence hypothesis. -/
theorem exists_standardSmooth_reduction_factorization
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (A' : Type (max u v w)) (_ : CommRing A') (_ : Algebra R A'),
      FinitePresentation R A' ∧
      ∃ (ι : A →ₐ[R] A') (φ' : A' →ₐ[R] Λ), φ'.comp ι = φ ∧
        IsStandardSmooth (R ⧸ I) (A' ⧸ I.map (algebraMap R A')) := by sorry

end Algebra
