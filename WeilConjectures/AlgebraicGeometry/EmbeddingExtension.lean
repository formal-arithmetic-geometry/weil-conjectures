/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicNumberRealization
public import WeilConjectures.AlgebraicGeometry.WeilNumbers
public import Mathlib.NumberTheory.NumberField.Basic

import Mathlib.Algebra.Algebra.Hom.Rat
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
6. Choose a realization `j` by `lem-weil-realization-exists`, and let `F = ℚ(α)` act on
   `C.Qbar` through `j` and the inclusion of the relative algebraic closure. `Qbar` is
   algebraic over the countable field `ℚ`, hence countable, and so is its subset `F`.
   Apply the countable-base extension of steps 1–5 (`IsAlgClosed.exists_ringEquiv_extend`)
   to an arbitrary embedding `τ` of `F`. The resulting ambient isomorphism sends the
   realized `α` to `τ α`, so the assumed norm equality applies.
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
  classical
  let : IsAlgClosed C.Qbar := IsAlgClosure.isAlgClosed (Padic C.l)
  let e := IsAlgClosure.equiv (Padic C.l) C.Qbar (PadicAlgCl C.l)
  obtain ⟨eComplex⟩ := PadicAlgCl.nonempty_ringEquiv_complex C.l
  have hKL : Nonempty (C.Qbar ≃ ℂ) := ⟨e.toEquiv.trans eComplex.toEquiv⟩
  have hK : Cardinal.aleph0 < Cardinal.mk C.Qbar := by
    rw [← Cardinal.aleph0_lt_lift.{u, 0}, Cardinal.lift_mk_eq'.2 hKL,
      Cardinal.aleph0_lt_lift, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have hL : Cardinal.mk L ≤ Cardinal.aleph0 := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ L
  refine ⟨IsAlgClosed.exists_ringEquiv_extend hL hK hKL σ, ?_, ?_⟩
  · intro α hα τ
    let j : C.AlgebraicNumberRealization D Qbar := by
      letI : Algebra ℚ (algebraicClosure ℚ C.Qbar) :=
        (algebraicClosure ℚ C.Qbar).algebra'
      let e' := IsAlgClosure.equiv ℚ Qbar (algebraicClosure ℚ C.Qbar)
      exact @RingEquiv.toRatAlgEquiv Qbar (algebraicClosure ℚ C.Qbar) _ _ _
        DivisionRing.toRatAlgebra e'.toRingEquiv
    let f : Qbar →+* C.Qbar :=
      (algebraicClosure ℚ C.Qbar).toSubfield.subtype.comp j.toRingHom
    let F := IntermediateField.adjoin ℚ ({α} : Set Qbar)
    let : Algebra F C.Qbar := (f.comp F.toSubfield.subtype).toAlgebra
    have hQbar : Cardinal.mk Qbar ≤ Cardinal.aleph0 := by
      simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ Qbar
    have hF : Cardinal.mk F ≤ Cardinal.aleph0 :=
      (Cardinal.mk_le_of_injective (f := fun x : F ↦ (x : Qbar))
        Subtype.val_injective).trans hQbar
    obtain ⟨ι, hι⟩ := IsAlgClosed.exists_ringEquiv_extend hF hK hKL τ
    have hgen := hι (IntermediateField.AdjoinSimple.gen ℚ α)
    have heq : ι ((AlgEquiv.toEquiv j) α : C.Qbar) =
        τ (IntermediateField.AdjoinSimple.gen ℚ α) := hgen
    rw [← heq]
    exact hα j ι
  · intro γ α hα
    refine ⟨fun h ↦ hα.1 (γ.injective (h.trans (map_zero γ).symm)), ?_⟩
    intro τ
    have hmp : minpoly ℚ α = minpoly ℚ (γ α) :=
      (minpoly.algHom_eq γ.toAlgHom γ.injective α).symm
    let eα := minpoly.algEquiv (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α) hmp
    have h := hα.2 (τ.comp eα.toRingHom)
    change ‖τ (eα (IntermediateField.AdjoinSimple.gen ℚ α))‖ = _ at h
    rwa [minpoly.algEquiv_apply] at h

end WeilConjectures
