module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-! # Perfect core in a separable closure

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Lemma 3.2.2,
printed pp. 55–56 (blueprint: lem-per-separable-closure-perfect-core).

The perfect core is written as the intersection of the image subfields of the iterated
Frobenius maps. Its inclusion into the separable closure is the composite of the subfield
inclusion and the given base-field inclusion.
-/

@[expose] public section

universe u v

namespace Field

/-- The relative separable closure of the perfect core of `K` inside a separable closure `Ks`
is the perfect core of `Ks`.

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Lemma 3.2.2,
printed pp. 55–56 (blueprint: lem-per-separable-closure-perfect-core).

Proof: Write `C` and `D` for the intersections of all Frobenius image subfields in `K` and
`Ks`, respectively. These are subfields because Frobenius is a field homomorphism
(def-weil-ring-frobenius). If `c ∈ C`, choose `b` with `b ^ p = c`. For every `n`, choose
`a` with `a ^ (p ^ (n + 1)) = c`. Frobenius injectivity gives `b = a ^ (p ^ n)`, so `b ∈ C`.
Thus `C` is perfect. Its relative separable closure `S` in `Ks` is algebraic over `C`
(def-weil-pbc-relative-separable-closure), hence perfect by
lem-per-algebraic-extension-perfect. Taking iterated roots in `S` proves `S ⊆ D`.

Conversely, for `x ∈ D` choose `x_n ∈ Ks` with `x_n ^ (p ^ n) = x`. Each `x_n` is separable
algebraic over `K` (def-pd-separable-closure, def-weil-pbc-separable-algebraic-extension).
By lem-per-minpoly-iterated-frobenius, the minimal polynomial of `x` is the coefficientwise
`p ^ n`-th power of that of `x_n`. Every coefficient therefore belongs to `C`. This polynomial
remains irreducible over `C`, since a factorization there would give one over `K`. Its
derivative is nonzero by separability over `K`; irreducibility and the smaller derivative
degree give coprimality with the derivative over `C` (def-pc-separable-polynomial). Hence `x`
is separable algebraic over `C` and lies in `S`, proving the reverse inclusion. -/
theorem separableClosure_perfect_core (K : Type u) (Ks : Type v) [Field K] [Field Ks]
    [Algebra K Ks] [IsSepClosure K Ks] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ((@separableClosure (↥(⨅ n : ℕ, (iterateFrobenius K p n).fieldRange)) Ks
        inferInstance inferInstance
        ((algebraMap K Ks).comp
          (⨅ n : ℕ, (iterateFrobenius K p n).fieldRange).subtype).toAlgebra) : Set Ks) =
      {x : Ks | ∀ n : ℕ, ∃ a : Ks, a ^ (p ^ n) = x} := by
  sorry

end Field
