module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Algebraically closed extensions with a prescribed cardinal lower bound

Source: Stacks Project, Fields, Tags 09FJ and 09GT, together with the cardinal-enlargement
construction by independent variables
(blueprint: lem-sfb-algclosed-extension-cardinal-lower-bound).
-/

@[expose] public section

universe u

namespace Field

/-- A field has an algebraically closed extension in the same universe with cardinality
at least any prescribed infinite cardinal. The extension need not be algebraic.

Source: Stacks Project, Fields, Tag 09FJ (fraction fields), then Tag 09GT (existence of
algebraic closures); the cardinal-enlargement consequence is the following construction,
not the literal statement of either tag
(blueprint: lem-sfb-algclosed-extension-cardinal-lower-bound).

Proof plan:
1. Choose a type `I : Type u` of cardinality `κ`. Form `R = MvPolynomial I k` using
   `def-weil-pbc-mv-polynomial-ring`. Since `k` is a field (`def-weil-field`), it is a
   domain, so `lem-weil-pbc-polynomial-ring-domain` makes `R` a domain. The coefficient
   of the monomial `X i` distinguishes `X i` from `X j` when `i ≠ j`; thus the variables
   give an injection `I → R`. Constant coefficients likewise show that `k → R` is
   injective. Finite supports ensure that `R` belongs to the same universe.
2. Localize `R` at its nonzero elements, using the localization construction in
   `def-weil-pbc-essentially-finite-type-algebra`, without any finite-type assertion.
   In a domain the fraction equality criterion is cross-multiplication, so `R → F`
   is injective for this localization `F`, and `0 ≠ 1` in `F`. A nonzero fraction
   `a / s` has inverse `s / a`, hence `F` is a field (Tag 09FJ). Fractions are a
   quotient of a small product, so `F : Type u`.
3. Take `K = AlgebraicClosure F` by clause (1) of
   `lem-pc-algebraic-closure-exists-unique` (Tag 09GT). This is an algebraically closed
   field in `Type u`. Its field map from `F` is injective (`def-pc-field-extension`).
   The composite `k → R → F → K` supplies the `Algebra k K` structure.
4. The composite injection `I → R → F → K` gives `κ = Cardinal.mk I ≤ Cardinal.mk K`.
   Only `K / F` is required to be algebraic; no algebraicity over `k` is imposed. -/
theorem exists_algClosed_extension_cardinal_le (k : Type u) [Field k]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsAlgClosed K ∧ κ ≤ Cardinal.mk K := by
  sorry

end Field
