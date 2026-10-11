/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.RingTheory.FormallySmoothAdic

/-!
# Base change of formal smoothness for an adic topology

Source: Stacks Project, More on Algebra, Lemma 07EG (blueprint: lem-weil-pbc-fs-adic-base-change).
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Formal smoothness for an adic topology is preserved by arbitrary base change.
Source: Stacks Project, More on Algebra, Lemma 07EG
(blueprint: lem-weil-pbc-fs-adic-base-change).

Proof:
1. For a square-zero ideal `J` of a commutative `R'`-algebra `D` and an `R'`-algebra
   map `g' : S ⊗[R] R' → D/J` killing the `k`-th power of the extended ideal,
   restrict along `includeLeft` to an `R`-algebra map `g : S → D/J`. Regard `D`
   as an `R`-algebra through `R → R' → D`
   (`def-weil-pbc-algebra-hom-quotient`,
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`).
2. The inclusion carries `n ^ k` into the `k`-th power of the extended ideal,
   since it carries every product of `k` elements of `n` there. Thus `g` kills
   `n ^ k` and is continuous (`def-weil-pbc-algebra-hom-quotient`).
3. Apply `h` to obtain an `R`-algebra lift `f : S → D` of `g`
   (`def-weil-pbc-formally-smooth-adic`).
4. The tensor-product pushout property extends `f` and the structure map `R' → D`
   to `f' : S ⊗[R] R' → D`, sending `s ⊗ r'` to `f(s) * r'`. Its restriction
   to `R'` is the structure map, so it is an `R'`-algebra map
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`).
5. The quotient of `f'` and `g'` agree after both tensor-factor inclusions;
   pushout uniqueness makes them equal. This solves every lifting problem
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`,
   `def-weil-pbc-algebra-hom-quotient`, `def-weil-pbc-formally-smooth-adic`). -/
theorem formallySmoothAdic_tensorProduct
    (R : Type u) (S : Type v) (R' : Type w)
    [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (n : Ideal S)
    (h : FormallySmoothAdic R S n) :
    letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    FormallySmoothAdic R' (S ⊗[R] R')
      (n.map (algebraMap S (S ⊗[R] R'))) := by
  sorry

end Algebra
