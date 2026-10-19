## Worker report

The module `Sheaf.Paper.EmbeddingExtension` states
`WeilConjectures.embedding_extension_and_intrinsic_weights`, with one postponed proof and
all three clauses of `lem-embedding-extension`. The node statement is unchanged.
The current main-20261015 statement and proof were read in full and agree with the imported
statement and the seven-step DAG proof. The theorem docstring records those seven steps,
including existence of a realization before using the universal hypothesis.

Hypotheses and clauses, individually:

- `D : FiniteFieldDatum.{u}` carries the prime `p`, the natural exponent `a ≥ 1`,
  `q = p ^ a`, the field `k₀` of cardinality `q`, and its fixed algebraic closure `k`.
- `C : D.CoefficientDatum` carries a prime `C.l`, `C.l ≠ D.p`, and an arbitrary
  chosen algebraic closure `C.Qbar` of `Padic C.l`. Its algebra and closure instances
  are the dependency's existing structures, not additional assumptions.
- `Qbar : Type v`, `[Field Qbar]`, `[Algebra ℚ Qbar]`, `[IsAlgClosure ℚ Qbar]`
  represents any fixed algebraic closure of the rational numbers, independently of `u`.
- `i : ℤ` retains all integer weights. `(D.q : ℝ) ^ ((i : ℝ) / 2)` uses real
  division and `Real.rpow`, not integer division or a natural power.
- `L : Subfield C.Qbar`, `[NumberField L]`, and `σ : L →+* ℂ` give exactly a
  number subfield of the chosen coefficient closure and a complex embedding. Field
  homomorphisms are automatically injective and fix the rational prime subfield.
- The first conjunct is `∃ ι : C.Qbar ≃+* ℂ, ∀ x : L, ι (x : C.Qbar) = σ x`.
  Thus the isomorphism extends the specified embedding, point by point, and is abstract:
  there is no continuity condition.
- The second conjunct quantifies over every `α : Qbar`. Its hypothesis quantifies
  over every `j : C.AlgebraicNumberRealization D Qbar` and every abstract
  `ι : C.Qbar ≃+* ℂ`. The realization's underlying equivalence is
  `AlgEquiv.toEquiv j`; its value is coerced from `algebraicClosure ℚ C.Qbar` into
  `C.Qbar`, the canonical subfield inclusion. The norm equality is exactly the
  universal realization hypothesis. The conclusion quantifies over
  `τ : IntermediateField.adjoin ℚ ({α} : Set Qbar) →+* ℂ` and applies `τ` to
  `IntermediateField.AdjoinSimple.gen ℚ α`, the element `α` in its simple field.
  This concludes the same norm equality for every embedding of `ℚ(α)`.
- The third conjunct quantifies over every `γ : Qbar ≃ₐ[ℚ] Qbar` and `α : Qbar`,
  and states `IsWeilNumber D α (i : ℝ) → IsWeilNumber D (γ α) (i : ℝ)`.
  This is stability under the full rational Galois group, including nonzeroness.
  It does not depend on the stronger universal realization hypothesis.

Statement dependencies and the declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.CoefficientDatum` (complete structures and docstrings).
- `Sheaf.Paper.AlgebraicNumberRealization`:
  `WeilConjectures.FiniteFieldDatum.CoefficientDatum.ratAlgebra` and
  `.AlgebraicNumberRealization`; these use the existing `algebraicClosure ℚ C.Qbar`.
- `Mathlib.NumberTheory.NumberField.Basic`: `NumberField`, precisely characteristic
  zero and finite rational dimension, applied to the subtype field `L`.
- `Mathlib.Algebra.Ring.Hom.Defs`: `RingHom` for field embeddings, with the complex
  embedding convention in `Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings`.
- `Mathlib.Algebra.Algebra.Equiv`: `AlgEquiv`, used both for the recorded realization
  and for rational automorphisms; the abstract ambient isomorphism is its underlying
  notion `RingEquiv`, since no base compatibility beyond the prime field is imposed.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`: `IntermediateField.adjoin`,
  instantiated on a singleton, and `IntermediateField.AdjoinSimple.gen`.
- `Mathlib.Analysis.Complex.Norm`: `Complex.instNorm`, so the absolute value is `‖z‖`.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`: `Real.rpow`.
- `Sheaf.Paper.WeilNumbers`: the same `WeilConjectures.IsWeilNumber`, generalized
  under §1(B) as described below; its two defining clauses are unchanged.

The proof imports make available `IsAlgClosed.isAlgClosure_of_transcendence_basis`,
`exists_isTranscendenceBasis`,
`IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`,
`IntermediateField.finiteDimensional_adjoin`, `IsAlgClosure.equiv`,
`algebraicClosure.isAlgClosure`, `Complex.isAlgClosed`, `Cardinal.mk_complex`, and
`PadicAlgCl.mk_eq_continuum`. The last is in the upstream module
`WeilConjectures.Mathlib.NumberTheory.Padics.Complex`; its DAG proof prerequisite
`lem-weil-padic-algebraic-closure-cardinality` currently has no recorded Lean interface,
so the existing upstream theorem is imported without altering that node.
The relevant source signatures and docstrings were read.

Edge cases checked before writing:

- `L = ℚ` still requires restriction to the rational embedding, which is automatic,
  while general `L` requires the explicit pointwise extension clause.
- `α = 0` is allowed in the intrinsic-weight implication. The universal norm equality
  cannot hold, since `D.q > 0` and realizations/ambient isomorphisms exist. No nonzero
  hypothesis is added to that implication.
- `i = 0` gives modulus one; negative and positive integer weights are both retained.
- The Weil predicate itself excludes zero, and the automorphism preserves this.
- `γ = 1`, the smallest prime values, and every coefficient prime different from `p`
  remain admitted. Neither closure is restricted to the canonical model.
- Universes `u` and `v` are independent. No countability, chosen realization,
  uncountability or extra isomorphism is assumed: these are proof consequences.

Searches for an existing complete statement:

- `msearch.py ... leanfinder` with “Extend a number field embedding into the complex
  numbers to an isomorphism from an algebraic closure of the p-adic numbers to complex
  numbers”: eight hits, including `NumberField.ComplexEmbedding.Extension`,
  `.lift`, infinite-place completion embeddings/isomorphisms, and `PadicComplex`.
  None states the prescribed ambient extension together with the two weight clauses.
- `msearch.py ... loogle "IsAlgClosed.equivOfTranscendenceBasis"`: one hit, the
  classification construction, which has transcendence-basis inputs rather than this
  statement's number-field embedding, and has no intrinsic-weight/Galois clauses.
- `msearch.py ... grep "embedding.*[Ee]xtension|IsWeilNumber|equivOfTranscendenceBasis"
  FieldTheory`: six hits in classification and algebraic embedding factorization;
  no match for the item.
- `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` for
  `lem-embedding-extension|IsWeilNumber|embedding_extension|embeddingExtension`:
  only the existing Weil predicate and unrelated generic-ideal stalk embedding lemmas.
  There is no upstream declaration for this node.

No statement dispute or source correction was needed. No new nodes were introduced.

## Dependency modules

`def-weil-numbers`: its recorded `Sheaf.Paper.WeilNumbers` declaration hard-coded
`α : AlgebraicClosure ℚ`. The dependency's text instead fixes a rational algebraic
closure, and the consumer explicitly allows any chosen closure. The old interface
therefore could not express the last clause on the same `Qbar` used by realizations
and the intrinsic-weight clause. The owning module is repaired in place by adding
an implicit `{Qbar : Type v}` and its field, rational algebra and algebraic-closure
instances to `IsWeilNumber`. Its data remains the identical conjunction of nonzeroness
and the universal norm equality on the singleton-adjoined simple field. This introduces
no second predicate and no arbitrary transport map. The dependency node changes only
in `lean`, including the required explanation in `lean.note`.

The shared-source search found no existing consumer of `IsWeilNumber` outside its
own definition. Canonical-closure calls still infer `Qbar := AlgebraicClosure ℚ` from
`α`; the main theorem checks its use on an arbitrary closure.

Validation: `scompile.py Q11 lem-embedding-extension` compiled both delivered modules
separately against the overlay, without errors or warnings. A separate scratch
`#check` consumer compiled through the same wrapper and confirmed both the original
canonical call type `FiniteFieldDatum → AlgebraicClosure ℚ → ℝ → Prop` and the
arbitrary-closure call type with independent universe `v`. The scratch probe is not
part of the delivery. The prescribed `deliver2.py --no-push` dry run passed server
preflight and per-file compilation.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
