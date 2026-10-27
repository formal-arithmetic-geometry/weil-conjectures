/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension

/-!
# Separating bases in an algebraic field diamond

Source: Stacks Project, Algebra, Tags 030W and 030Z; Fields, Tags 09HB, 09H2 and 09GH;
the algebraic argument for de Jong, Families of curves and alterations (1997), Lemma 5.2,
printed p. 613 (blueprint: lem-sfb-separating-basis-algebraic-diamond).
-/

@[expose] public section

universe u v w z q

open scoped TensorProduct

namespace Algebra

/-- A separating transcendence basis inside `F` remains algebraically independent over `k`
and makes `E` finite separable over its parameter field, for an algebraic field diamond.
The two scalar towers express the inclusions into the same `E`; neither an inclusion of `k`
in `F` nor an inclusion of `F` in `k` is assumed. The parameter field formed inside `F`
identifies canonically with its image inside `E`. The geometric reducedness test uses a
common enlarged universe, so it includes extension fields of the base in every case.

Source: Stacks Project, Algebra, Tags 030W and 030Z; Fields, Tags 09HB, 09H2 and 09GH;
agent extraction of steps 7--9 in the de Jong Lemma 5.2 argument, printed p. 613
(blueprint: lem-sfb-separating-basis-algebraic-diamond).

Proof:
1. In characteristic zero use `lem-weil-pbc-perfect-field-separating-basis`. In positive
   characteristic, geometric reducedness and
   `lem-weil-pbc-geometrically-reduced-extension-separable` imply separability in the
   sense of `def-weil-pbc-separable-field-extension`. Finite generation then gives a
   separating transcendence basis of `F/k₀`. Its cardinality is `d` by
   `def-kun-transcendence-degree`, so enumerate it by `Fin d`. Put `A = k₀(t)` and
   `B = k(t)`; the extension `F/A` is separable algebraic.
2. The inclusion `F → E` preserves algebraic independence over `k₀`. Apply
   `lem-zl-independence-algebraic-base` to `k₀ ⊆ k ⊆ E` to obtain independence over `k`.
3. By `lem-zl-separable-permanence`, the separable algebraic tower `A ⊆ F ⊆ E`
   gives separability of `E/A`.
4. Generated-subfield minimality gives `A ⊆ B ⊆ E`. Since `E/A` is algebraic,
   this is an algebraic tower. Apply `lem-sfb-separable-algebraic-intermediate-base`
   to conclude that `E/B` is separable algebraic. No containment between `k` and `F`
   enters this argument.
5. A finite field generating family of `E/k₀` also generates `E/B`. Its elements are
   algebraic over `B` by step 4, so `lem-weil-pbc-algebraic-generators-finite-extension`
   makes `E/B` finite-dimensional. These are all the conclusions. When `d = 0`,
   `A = k₀` and `B = k`, and the same proof applies to the empty family.
-/
theorem exists_separating_basis_algebraic_diamond
    (k₀ : Type u) (k : Type v) (F : Type w) (E : Type z)
    [Field k₀] [Field k] [Field F] [Field E]
    [Algebra k₀ k] [Algebra k₀ F] [Algebra k₀ E] [Algebra k E] [Algebra F E]
    [IsScalarTower k₀ k E] [IsScalarTower k₀ F E]
    [Algebra.IsAlgebraic k₀ k] [Algebra.IsSeparable F E]
    (hEfg : (⊤ : IntermediateField k₀ E).FG)
    (hFfg : (⊤ : IntermediateField k₀ F).FG)
    (hred : ∀ (L : Type (max u v w z q)) [Field L] [Algebra k₀ L],
      IsReduced (F ⊗[k₀] L))
    (d : ℕ) (hd : Algebra.trdeg k₀ F = (d : Cardinal)) :
    ∃ t : Fin d → F,
      IsTranscendenceBasis k₀ t ∧
      Algebra.IsSeparable (IntermediateField.adjoin k₀ (Set.range t)) F ∧
      AlgebraicIndependent k (fun i ↦ algebraMap F E (t i)) ∧
      FiniteDimensional
        (IntermediateField.adjoin k (Set.range (fun i ↦ algebraMap F E (t i)))) E ∧
      Algebra.IsSeparable
        (IntermediateField.adjoin k (Set.range (fun i ↦ algebraMap F E (t i)))) E := by
  sorry

end Algebra
