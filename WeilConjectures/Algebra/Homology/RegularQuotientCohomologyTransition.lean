/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ConcreteCategory
public import WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Cohomology of regular scalar quotients

Source: Stacks Project, Tag 0117, `lemma-long-exact-sequence-cochain`, its
Snake-Lemma boundary and functoriality; blueprint `sk-lem-integral-scalar-towers`,
proof paragraph (2) (blueprint: lem-pe-regular-quotient-cohomology-transition).

The quotient functor below is the existing ideal-quotient functor, restricted
back to the original coefficient ring. The principal ideal `(t^n)` gives exactly
`t^n M`. Reduction and transition maps in the statement are characterized on
EVERY quotient representative, so they are the actual quotient maps.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

open CategoryTheory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Reduction modulo `(t^n)`, with scalars restricted back to `R`.
Source: Stacks Project, Tag 0117, specialization to scalar powers
(blueprint: lem-pe-regular-quotient-cohomology-transition).
This is a composite of the existing quotient and restriction functors. -/
abbrev scalarPowerQuotientFunctor (t : R) (n : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  ModuleCat.quotSMulTop (Ideal.span {t ^ n}) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {t ^ n}))

/-- The termwise quotient cochain complex `C/t^n C`, with its induced differential.
Source: Stacks Project, Tag 0117, specialization to scalar powers
(blueprint: lem-pe-regular-quotient-cohomology-transition). -/
abbrev scalarPowerQuotient (t : R) (n : ℕ) (C : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  ((scalarPowerQuotientFunctor t n).mapHomologicalComplex (.up ℤ)).obj C

/-- The quotient `H^q(C)/t^n H^q(C)` using the same existing quotient functor.
Source: Stacks Project, Tag 0117, the cokernel of the scalar cohomology map
(blueprint: lem-pe-regular-quotient-cohomology-transition). -/
abbrev scalarPowerCohomologyQuotient (t : R) (n : ℕ)
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) : ModuleCat.{v} R :=
  (scalarPowerQuotientFunctor t n).obj (C.homology q)

/-- The kernel `H^q(C)[t^n]` of scalar multiplication on cohomology.
Source: Stacks Project, Tag 0117, the kernel of the scalar cohomology map
(blueprint: lem-pe-regular-quotient-cohomology-transition). -/
abbrev scalarPowerCohomologyTorsion (t : R) (n : ℕ)
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R (C.homology q) (t ^ n)))

/-- The normalized short exact cohomology sequences of regular scalar quotients,
with their quotient transitions and naturality for linear chain maps.
Source: Stacks Project, Tag 0117, `lemma-long-exact-sequence-cochain`, its
Snake-Lemma boundary and functoriality; blueprint `sk-lem-integral-scalar-towers`,
proof paragraph (2) (blueprint: lem-pe-regular-quotient-cohomology-transition).

Proof:
1. Iterating termwise injectivity of `t` gives injectivity of `t^n`. Scalar
multiplication commutes with the differential, and quotient reduction has kernel
`t^n C` and is surjective. Thus `0 → C → C → C/t^n C → 0` is degreewise short exact.
2. Apply `lem-weil-pbc-complex-ses-homology-long-exact` (Mathlib's
`ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`, `homology_exact₃`).
Its five-term segment identifies the reduction kernel with `t^n H^q(C)` and the
boundary image with `H^(q+1)(C)[t^n]`. Descend the reduction to its cokernel and
corestrict the boundary to this kernel to get the asserted short exact sequence.
3. For a quotient cocycle lifted to `x`, write `dx = t^n y`. Injectivity implies
`dy = 0`. The boundary formula `lem-pe-module-complex-ses-boundary-formula`
(Mathlib's `ShortComplex.ShortExact.δ_apply`) gives the class of `y`, fixing the sign.
4. The morphism of scalar short exact sequences from level `m` to `n` has maps
`(t^(m-n), 1, r_mn)`. Its squares commute by the power identity and quotient
reduction. Apply `lem-weil-pbc-complex-ses-long-exact-naturality` (Mathlib's
`HomologicalComplex.HomologySequence.δ_naturality`). Descending on the left gives
quotient projection; restricting on the right gives multiplication by `t^(m-n)`.
5. A linear chain map gives the morphism `(f, f, f_n)` of scalar short exact
sequences. The same naturality lemma gives both cohomology squares. Quotient
representatives also give `f_m r'_mn = r_mn f_n`, proving naturality of transitions.
-/
theorem regular_quotient_cohomology_transition (t : R) :
    ∃ (p : ∀ (C : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ+),
        C ⟶ scalarPowerQuotient t n C)
      (r : ∀ (C : CochainComplex (ModuleCat.{v} R) ℤ) (m n : ℕ+),
        (n : ℕ) ≤ m → (scalarPowerQuotient t m C ⟶ scalarPowerQuotient t n C))
      (iota : ∀ (C : CochainComplex (ModuleCat.{v} R) ℤ)
        (_ : ∀ j : ℤ, Function.Injective (fun x : C.X j ↦ t • x)) (n : ℕ+) (q : ℤ),
        scalarPowerCohomologyQuotient t n C q ⟶ (scalarPowerQuotient t n C).homology q)
      (delta : ∀ (C : CochainComplex (ModuleCat.{v} R) ℤ)
        (_ : ∀ j : ℤ, Function.Injective (fun x : C.X j ↦ t • x)) (n : ℕ+) (q : ℤ),
        (scalarPowerQuotient t n C).homology q ⟶
          scalarPowerCohomologyTorsion t n C (q + 1)),
      (∀ (C : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ+) (j : ℤ) (x : C.X j),
        (p C n).f j x = Submodule.Quotient.mk x) ∧
      (∀ (C : CochainComplex (ModuleCat.{v} R) ℤ) (m n : ℕ+) (h : (n : ℕ) ≤ m)
        (j : ℤ) (x : C.X j),
        (r C m n h).f j (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) ∧
      (∀ (C : CochainComplex (ModuleCat.{v} R) ℤ)
        (hC : ∀ j : ℤ, Function.Injective (fun x : C.X j ↦ t • x)) (n : ℕ+) (q : ℤ),
        Function.Injective (iota C hC n q) ∧
        Function.Exact (iota C hC n q) (delta C hC n q) ∧
        Function.Surjective (delta C hC n q) ∧
        (∀ z : C.homology q,
          iota C hC n q (Submodule.Quotient.mk z) = HomologicalComplex.homologyMap (p C n) q z) ∧
        (∀ (z : (scalarPowerQuotient t n C).cycles q)
          (x : C.X q) (y : C.cycles (q + 1)),
          (p C n).f q x = (scalarPowerQuotient t n C).iCycles q z →
          C.d q (q + 1) x = t ^ (n : ℕ) • C.iCycles (q + 1) y →
          (delta C hC n q ((scalarPowerQuotient t n C).homologyπ q z)).val =
            C.homologyπ (q + 1) y)) ∧
      (∀ (C : CochainComplex (ModuleCat.{v} R) ℤ)
        (hC : ∀ j : ℤ, Function.Injective (fun x : C.X j ↦ t • x))
        (m n : ℕ+) (h : (n : ℕ) ≤ m) (q : ℤ),
        (∀ z : C.homology q,
          HomologicalComplex.homologyMap (r C m n h) q
              (iota C hC m q (Submodule.Quotient.mk z)) =
            iota C hC n q (Submodule.Quotient.mk z)) ∧
        (∀ z : (scalarPowerQuotient t m C).homology q,
          (delta C hC n q (HomologicalComplex.homologyMap (r C m n h) q z)).val =
            t ^ ((m : ℕ) - (n : ℕ)) • (delta C hC m q z).val)) ∧
      (∀ (C D : CochainComplex (ModuleCat.{v} R) ℤ)
        (hC : ∀ j : ℤ, Function.Injective (fun x : C.X j ↦ t • x))
        (hD : ∀ j : ℤ, Function.Injective (fun x : D.X j ↦ t • x))
        (f : C ⟶ D) (n : ℕ+) (q : ℤ),
        (∀ z : C.homology q,
          HomologicalComplex.homologyMap
              (((scalarPowerQuotientFunctor t n).mapHomologicalComplex (.up ℤ)).map f) q
              (iota C hC n q (Submodule.Quotient.mk z)) =
            iota D hD n q (Submodule.Quotient.mk (HomologicalComplex.homologyMap f q z))) ∧
        (∀ z : (scalarPowerQuotient t n C).homology q,
          (delta D hD n q (HomologicalComplex.homologyMap
              (((scalarPowerQuotientFunctor t n).mapHomologicalComplex (.up ℤ)).map f) q z)).val =
            HomologicalComplex.homologyMap f (q + 1) (delta C hC n q z).val)) ∧
      (∀ (C D : CochainComplex (ModuleCat.{v} R) ℤ) (f : C ⟶ D) (n : ℕ+),
        f ≫ p D n = p C n ≫
          ((scalarPowerQuotientFunctor t n).mapHomologicalComplex (.up ℤ)).map f) ∧
      (∀ (C D : CochainComplex (ModuleCat.{v} R) ℤ) (f : C ⟶ D)
        (m n : ℕ+) (h : (n : ℕ) ≤ m),
        r C m n h ≫ ((scalarPowerQuotientFunctor t n).mapHomologicalComplex (.up ℤ)).map f =
          ((scalarPowerQuotientFunctor t m).mapHomologicalComplex (.up ℤ)).map f ≫ r D m n h) := by
  classical
  have htrivial : True := trivial
  sorry

end CochainComplex
