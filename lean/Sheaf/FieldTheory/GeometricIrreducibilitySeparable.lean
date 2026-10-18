/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import WeilConjectures.FieldTheory.SeparableExtension

/-!
# Geometric irreducibility and separable elements

Source: Stacks Project, Algebra, Tag 0G33 (lemma-geometrically-irreducible-separable-elements),
equivalence of (1) and (2) (blueprint: lem-zl-geometric-irreducibility-separable).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A field extension is geometrically irreducible exactly when its separably algebraic
elements over the base field already lie in the base field.
Source: Stacks Project, Algebra, Tag 0G33 (lemma-geometrically-irreducible-separable-elements),
equivalence of (1) and (2) (blueprint: lem-zl-geometric-irreducibility-separable).

Proof:
1. Given a separably algebraic element α, its simple intermediate field k(α) lies in the
   relative separable closure (`def-weil-pbc-relative-separable-closure`), so it is separable
   algebraic. Its power basis (`lem-weil-pbc-simple-algebraic-extension-power-basis`) makes
   it finite. The subalgebra clause of `lem-zl-geometric-irreducibility-subalgebra-colimit`
   makes k(α)/k geometrically irreducible.
2. A finite separable algebraic extension is separable in the sense of
   `def-weil-pbc-separable-field-extension`: every finitely generated intermediate field
   has the empty transcendence basis. Apply `lem-pc-separable-tensor-algebraic-closure`:
   k(α) tensored with an algebraic closure of k is a product of [k(α):k] copies of that
   closure. Its spectrum is irreducible, so it has exactly one factor (two or more factors
   give disjoint nonempty complementary opens). Thus [k(α):k] = 1 and α lies in k.
3. Conversely, let k' be the algebraic closure of k in K
   (`def-weil-relative-algebraic-closure`). It is algebraically closed in K: for a polynomial
   over k' vanishing at β in K, its finitely many coefficients generate a finite extension
   F/k by `lem-weil-pbc-algebraic-generators-finite-extension`. A power basis makes F(β)/F
   finite. Products of bases show F(β)/k finite, hence β is algebraic over k and lies in k'.
   Now `lem-zl-field-extension-algebraically-closed-geometric` gives geometric irreducibility
   of K/k'.
4. Every element of k' separably algebraic over k lies in k by the hypothesis. Therefore
   `lem-weil-pbc-separable-first-purely-inseparable` makes k'/k purely inseparable: in
   characteristic p > 0 every x in k' has x^(p^n) in k for some n; in characteristic zero,
   k' = k.
5. In positive characteristic take p to be the characteristic, and in characteristic zero
   take p = 2. The inclusion k → k' has zero kernel. Every x in k' has x^(p^n) and p^n*x
   in k for some n > 0: in characteristic p increase n and use p^n*x = 0; in
   characteristic zero use k' = k. Apply `lem-pur-power-generated-spectrum-homeomorphism`
   to the generating set of all elements of k'. After every field extension L/k this
   identifies the spectrum of L tensored with k' with the one-point spectrum of L.
   Hence k'/k is geometrically irreducible.
6. Apply `lem-zl-geometric-irreducibility-transitive` to the tower k ⊆ k' ⊆ K and the
   geometric irreducibility conclusions in steps 3 and 5.
-/
theorem geometricallyIrreducible_iff_separableElements_mem
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↔
      ∀ α : K, IsSeparable k α → α ∈ Set.range (algebraMap k K) := by
  sorry

end AlgebraicGeometry
