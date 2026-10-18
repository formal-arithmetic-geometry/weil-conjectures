/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.AlgebraicNumberRealization
public import Sheaf.Paper.WeilNumbers
public import Mathlib.NumberTheory.NumberField.Basic

import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.Mathlib.NumberTheory.Padics.Complex

/-!
# Extension of embeddings and intrinsic weights

Source: Weil conjectures blueprint, `sec-zeta-weil`, unit `sk-thm-intfactors`,
`lem-embedding-extension.md` and its proof, main-20261015
(blueprint: lem-embedding-extension).

The three conjuncts give extension with prescribed restriction, the intrinsic weight
criterion on a simple number field, and Galois stability of the Weil-number condition.
No topology or continuity is imposed on the ambient field isomorphisms.
-/

@[expose] public section

universe u v

namespace WeilConjectures

/-- Embeddings of number subfields of the chosen adic algebraic closure extend to complex
field isomorphisms; universal realization weights are intrinsic and Galois invariant.
Source: blueprint `sec-zeta-weil/sk-thm-intfactors/lem-embedding-extension.md`,
main-20261015 (blueprint: lem-embedding-extension).

Proof (the seven steps of the DAG node):
1. Give both ambient fields their `L`-algebra structures, using inclusion and `σ`.
   A finite rational basis shows that the number field `L` is countable
   (`def-weil-number-field`, `def-weil-field-extension-isomorphism`).
2. Both ambient fields are algebraically closed and have cardinality continuum.
   Use `lem-weil-complex-algebraically-closed`,
   `lem-weil-padic-algebraic-closure-cardinality`,
   `lem-pc-algebraic-closure-exists-unique` to transfer cardinality to `C.Qbar`, and
   `lem-weil-complex-cardinality`; Cantor makes both fields uncountable.
3. Choose transcendence bases over `L` by `lem-exc-transcendence-basis-exists`.
   Their cardinalities are continuum by `lem-weil-countable-base-transcendence-cardinality`,
   so choose a bijection of their index sets.
4. Algebraic independence (`def-weil-pbc-transcendence-basis`) identifies the generated
   polynomial subalgebras with polynomial rings over `L`. Rename variables by this
   bijection, map coefficients by `σ`, and extend to fractions by `a/b ↦ f(a)/f(b)`.
   Cross multiplication proves well-definedness, and the inverse substitution gives
   the inverse field map, still extending `σ`.
5. The ambient fields are algebraic closures of these fraction fields by
   `lem-exc-transcendence-basis-algebraic-closure`. Pull back the complex field's structure
   along the fraction-field isomorphism. Algebraic-closure uniqueness
   (`lem-pc-algebraic-closure-exists-unique`) now extends that specified isomorphism,
   hence restricts to `σ` on `L`.
6. Choose a realization by `lem-weil-realization-exists`. The field `ℚ(α)` is finite by
   `lem-weil-pbc-algebraic-generators-finite-extension`. Transport an arbitrary embedding
   `τ` to the number subfield which is its realization's image. Apply steps 1–5 to
   `τ` composed with the inverse realization on this image. The resulting ambient
   isomorphism sends the realized `α` to `τ α`, so the assumed norm equality applies.
7. A rational automorphism carries `ℚ(β)` isomorphically onto `ℚ(γ β)`
   (`def-weil-simple-field-extension`). Composing any embedding of the latter with this
   restriction gives an embedding of the former. Apply `def-weil-numbers` to obtain
   the same absolute value, and use injectivity to preserve nonzeroness. This last
   step uses only the Weil condition, independently of the realization hypothesis. -/
theorem embedding_extension_and_intrinsic_weights (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (Qbar : Type v) [Field Qbar] [Algebra ℚ Qbar]
    [IsAlgClosure ℚ Qbar] (i : ℤ) (L : Subfield C.Qbar) [NumberField L]
    (σ : L →+* ℂ) :
    (∃ ι : C.Qbar ≃+* ℂ, ∀ x : L, ι (x : C.Qbar) = σ x) ∧
    (∀ α : Qbar,
      (∀ (j : C.AlgebraicNumberRealization D Qbar) (ι : C.Qbar ≃+* ℂ),
        ‖ι ((AlgEquiv.toEquiv j) α : C.Qbar)‖ = (D.q : ℝ) ^ ((i : ℝ) / 2)) →
      ∀ τ : IntermediateField.adjoin ℚ ({α} : Set Qbar) →+* ℂ,
        ‖τ (IntermediateField.AdjoinSimple.gen ℚ α)‖ = (D.q : ℝ) ^ ((i : ℝ) / 2)) ∧
    (∀ (γ : Qbar ≃ₐ[ℚ] Qbar) (α : Qbar),
      IsWeilNumber D α (i : ℝ) → IsWeilNumber D (γ α) (i : ℝ)) := by
  sorry

end WeilConjectures
