/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finite flat modules over finite type algebras over valuation rings are finitely presented

Source: Stacks Project, `more-algebra.tex`, Lemma Tag 053E
(lemma-flat-finite-type-valuation-ring-finite-presentation), part (2),
statement and proof at lines 5966--6001
(blueprint: lem-trf-valuation-finite-type-module-presentation).

## Main statement

The theorem records the finite-presentation conclusion for a finite module over a finite type
algebra over a valuation ring when the module is flat over the valuation ring.  The proof uses
polynomial generators, a graded homogenization, evaluation at the extra variable, and descent
of finite presentation along the resulting polynomial presentation.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w

namespace Algebra

/--
A finite flat module over a finite type algebra over a valuation ring is finitely presented.

Source: Stacks Project, `more-algebra.tex`, Lemma Tag 053E
(lemma-flat-finite-type-valuation-ring-finite-presentation), part (2),
statement and proof at lines 5966--6001
(blueprint: lem-trf-valuation-finite-type-module-presentation).

Proof steps:
1. The valuation-ring fraction-field criterion gives total divisibility, hence locality.
   Choose finitely many algebra generators of `B` and module generators of `M`.
2. Let `F_d M` be the `A`-span of generator monomials of total degree at most `d`.
   Form `N = ⨁ d ≥ 0, F_d M t^d`. Over `P = A[X₀, …, Xₙ]`, let `X₀` act by `t`
   and `Xᵢ` act by `bᵢ t`. The degree-zero module generators generate this graded module
   (`def-weil-pbc-mv-polynomial-ring`).
3. Flatness makes `M` torsion-free (`lem-trf-flat-module-torsionfree-domain`).
   Coefficientwise, `N` is torsion-free too, hence flat over the valuation ring
   (`lem-trf-valuation-torsionfree-flat`).
4. Apply `lem-trf-local-graded-flat-module-finite-presentation` to `N` over the local
   coefficient ring `A`, with all variables of weight one. Thus `N` is finitely presented.
5. Evaluation at `t = 1` is surjective, since the filtration exhausts `M`. Its kernel is
   `(X₀ - 1)N`: if the coefficients `x_d` sum to zero, the coefficients
   `y_d = -∑ i ≤ d, x_i` express the element as `(t - 1)∑ d, y_d t^d`.
   For degree zero the kernel element is zero. Thus `N/(X₀ - 1)N ≅ M`.
6. Evaluate a finite free presentation of `N` at `X₀ = 1`. The polynomial universal
   property identifies `P/(X₀ - 1)` with `Q = A[X₁, …, Xₙ]`; the evaluated finite
   relation family presents `M` over `Q` (`def-sc-finitely-presented-module`).
7. The chosen algebra generators give a surjection `Q → B`, and the `Q`-action just
   constructed is restriction of the given `B`-action. Apply
   `lem-trf-finitely-presented-over-subring` to conclude finite presentation over `B`.
-/
theorem valuation_finite_type_module_presentation
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] [Module.Flat A M]
    (hAB : RingHom.FiniteType (algebraMap A B)) :
    Module.FinitePresentation B M := by
  sorry

end Algebra

end
