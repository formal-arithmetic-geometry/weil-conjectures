/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Sheaf.FieldTheory.SeparableExtension

/-!
# Making a finitely generated field extension separably generated

Source: Stacks Project, Algebra, Lemma Tag 04KM (lemma-make-separably-generated)
(blueprint: lem-weil-pbc-make-separably-generated).

## Main statements

* `FieldExtension.exists_finitePurelyInseparable_separablyGenerated`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FieldExtension

/-- A finitely generated field extension becomes separably generated after finite purely
inseparable extensions of the base and the extension.
Source: Stacks Project, Algebra, Lemma Tag 04KM (lemma-make-separably-generated)
(blueprint: lem-weil-pbc-make-separably-generated).

Proof, following the ten steps of the node and Stacks Tag 04KM:

1. In characteristic zero, `lem-weil-pbc-char-zero-field-extension-separable` makes the
   finitely generated extension separably generated. Use the identity extensions.
2. In characteristic p > 0 choose a finite transcendence basis x using
   `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`. Put E = k(x).
   The generators are algebraic over E, so `lem-weil-pbc-algebraic-generators-finite-extension`
   makes K/E finite. Its relative separable closure K_s gives a separable algebraic
   extension K_s/E and a purely inseparable extension K/K_s by
   `lem-weil-pbc-separable-first-purely-inseparable`. Induct strongly on e = [K : K_s],
   simultaneously for all extensions and finite transcendence bases.
3. If e = 1 then K = K_s, so x is separating. Again use the identity extensions.
4. Otherwise take an element outside K_s, and its least p-power in K_s. This gives
   beta outside K_s with alpha = beta^p in K_s. The minimal polynomial P of alpha
   over E is separable and has distinct roots (`def-pc-separable-polynomial`).
5. In an algebraic closure of K, write each coefficient c_j of P as f_j(x)/g_j(x),
   and set h_j = f_j * g_j^(p-1). Adjoin to k the p-th roots of the finitely many
   coefficients of all h_j, obtaining k_1. Put E_1 = k_1(x_i^(1/p)). Frobenius
   (`def-weil-ring-frobenius`) shows c_j is the p-th power of the polynomial with
   rooted coefficients evaluated at x_i^(1/p), divided by g_j(x).
6. Adjoining finitely many elements whose p-th powers lie in a field is finite
   algebraic and purely inseparable: the elements whose p-th powers lie in that
   field form a subfield. Thus k_1/k is finite purely inseparable, k_1^p lies in k,
   and the compositum L = K E_1 is finite purely inseparable over K.
7. L/k_1 is finitely generated, and `lem-weil-pbc-compositum-degree-bound` makes
   L/E_1 finite. Raising an alleged polynomial relation among x_i^(1/p) to the
   p-th power yields a nonzero relation among x_i over k, a contradiction.
   Consequently x_i^(1/p) is a finite transcendence basis of L/k_1.
8. Let L_s be the relative separable closure of E_1 in L. The minimal polynomial
   over E_1 of an element of K_s divides its separable polynomial over E, so K_s
   lies in L_s. By `lem-weil-pbc-separable-root-pth-power`, since P has distinct
   roots and p-th-power coefficients in E_1, alpha has a p-th root alpha_1 in L_s.
   Injectivity of Frobenius gives beta = alpha_1, hence beta lies in L_s.
9. Put K_1 = K_s(beta). The compositum K L_s equals L, so
   `lem-weil-pbc-compositum-degree-bound` gives [L : L_s] <= [K : K_1]. The tower law
   (`lem-weil-pbc-field-degree-multiplicativity`) and [K_1 : K_s] >= 2 give
   [L : L_s] < e.
10. Apply induction to L/k_1 with its rooted transcendence basis, obtaining L'/L
    and k_2/k_1. Compose the maps and use
    `lem-weil-pbc-finite-purely-inseparable-transitive` to obtain finite purely
    inseparable L'/K and k_2/k. The square commutes and L'/k_2 is separably generated.
    Finite extensions and subfields can be represented in Type (max u v).
-/
theorem exists_finitePurelyInseparable_separablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (k' : Type (max u v)) (hk' : Field k') (akk' : Algebra k k')
      (K' : Type (max u v)) (hK' : Field K') (aKK' : Algebra K K') (akK' : Algebra k' K'),
      letI := hk'
      letI := akk'
      letI := hK'
      letI := aKK'
      letI := akK'
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
      Module.Finite K K' ∧ IsPurelyInseparable K K' ∧
      Algebra.IsSeparablyGenerated k' K' ∧
      (algebraMap k' K').comp (algebraMap k k') =
        (algebraMap K K').comp (algebraMap k K) := by
  sorry

end FieldExtension
