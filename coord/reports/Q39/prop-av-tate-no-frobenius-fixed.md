## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.FrobeniusFixedTateModules` states
`AlgebraicGeometry.IsAbelianVariety.frobenius_fixed_tateModules_eq_zero`, with the
whole proof `by sorry`. It introduces no definitions, helper axioms or additional
theorems. The node copy changes only `lean`; its natural-language statement and
dependencies are unchanged.

The statement and proof were read in the current `main-20261015` blueprint at
`sec-algebraic-groups-lie-algebras/sk-p-tate/prop-av-tate-no-frobenius-fixed.md`
and the corresponding `.proof.md`. The current statement agrees with the DAG
text, whose source path refers to the older snapshot. The theorem docstring
includes the complete four-step DAG proof plan: the finite fixed field, the
affine-chart generator count, finiteness of the fixed subgroup, and the integral
and rational Tate-module argument for the automorphism and its inverse.

Hypotheses and objects, clause by clause:

- The finite base field is `(k₀ : Type u) [Field k₀] [Fintype k₀]`.
- The distinct primes of `d-ab-field` are `(p ℓ : ℕ) [Fact p.Prime]
  [Fact ℓ.Prime]` and `(hℓp : ℓ ≠ p)`. The characteristic is explicitly
  `[CharP k₀ p]`. This is the characteristic already determined by the
  finite-field cardinality in the source, not an additional restriction.
- The integer `a ≥ 1` and the size `q = p^a` are `(a : ℕ)`, `(ha : 1 ≤ a)`
  and `(hcard : Fintype.card k₀ = p ^ a)`. A separate symbol for `q` is
  unnecessary: the arithmetic Frobenius is the cardinality-power map, and
  `hcard` identifies that cardinality with `p^a`.
- The abelian variety over `k₀` is `(A₀ : Over (Spec (.of k₀))) [GrpObj A₀]
  [IsAbelianVariety A₀]`. The recorded definition `IsAbelianVariety` supplies
  properness, smoothness and connectedness. The existing `Basic` module derives
  geometric integralness, geometric connectedness and commutativity; finite type
  follows from properness. No extra assumption of commutativity, finiteness of
  rational points or finiteness of the Frobenius-fixed subgroup is imposed.
- The algebraic closure is the existing `AlgebraicClosure k₀`; its spectrum
  over the base is `Scheme.specAlgebraicClosure k₀`. Thus the additive group
  called `A` in the node is
  `Additive (Scheme.specAlgebraicClosure k₀ ⟶ A₀)`. Choosing Mathlib's standard
  algebraic closure represents the source's choice of an algebraic closure;
  it puts no algebraic condition on that choice. The single explicit universe
  `u` ranges over all sizes of the base field and variety, as in the upstream
  geometric-point API.
- `tateModule ℓ A₀` and `rationalTateModule ℓ A₀` are the existing upstream
  specializations of `AddCommGroup.tateModule` and
  `AddCommGroup.rationalTateModule` to exactly this geometric-point group.
  These definitions were read in full. The integral indexing includes `n = 0`,
  where the coordinate is forced to zero, so it is equivalent to the source's
  indexing by `n ≥ 1`. The rational module is the existing scalar extension
  `ℚ_[ℓ] ⊗[ℤ_[ℓ]] T`, representing `T[1/ℓ]`; the localization embedding and
  denominator-clearing argument are already present upstream.

Conclusions, in the exact order of the conjunction:

1. `(T_ℓ A)^σ = 0` is `∀ t : tateModule ℓ A₀,
   galoisRepresentation ℓ A₀ (FiniteField.frobeniusAlgEquivOfAlgebraic
   k₀ (AlgebraicClosure k₀)) t = t → t = 0`.
2. `(T_ℓ A)^F = 0` is the same assertion with
   `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`.
3. `(V_ℓ A)^σ = 0` is `∀ v : rationalTateModule ℓ A₀,
   AddCommGroup.rationalTateModule.map
   (geometricPointsAddEquiv (A := A₀) σ).toAddMonoidHom v = v → v = 0`,
   with the arithmetic Frobenius substituted explicitly for `σ` in the file.
4. `(V_ℓ A)^F = 0` is that same assertion for geometric Frobenius; this is
   also the opening displayed conclusion of the node.

Each fixed-submodule equality is written as the equivalent elementwise
assertion that every fixed element is zero. There is no added conclusion.
`geometricPointsAddEquiv` precomposes a point with `Spec σ`, so on an affine
chart it sends a coordinate map `φ` to `σ ∘ φ`. Its induced
`galoisRepresentation` acts coordinatewise. The rational map is its existing
scalar extension, hence acts on fractions as required. Geometric Frobenius
is definitionally the inverse of arithmetic Frobenius in the recorded
`d-ab-field` declaration.

Dependency declarations read and used:

- `d-ab-field`: `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`,
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`; the arithmetic version
  is `FiniteField.frobeniusAlgEquivOfAlgebraic` in Mathlib. Both are used in
  the signature. The finite-field, scheme and group-scheme parts of the datum
  use existing Mathlib structures, rather than a private bundled datum.
- `def-tate-module-abelian-group`: `WeilConjectures.GroupTheory.TateModule`,
  `AddCommGroup.tateModule`, `AddCommGroup.rationalTateModule`, and their
  `.map` operations. The abelian-variety specializations and coordinate action
  are reused from `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`.
- `def-sc-abelian-variety`: `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety` (imported through the Tate-module file).
- Proof dependency `lem-weil-unique-subfield-of-closure`:
  `Sheaf.FieldTheory.UniqueSubfieldOfClosure`,
  `FiniteField.exists_unique_subfield_of_closure`, imported without `public`.
- Proof dependency `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, already imported
  transitively and read at their definitions.
- Proof dependency `lem-tate-module-no-fixed`:
  `WeilConjectures.NumberTheory.TateModule`,
  `AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed` and its companion
  inverse/rational declarations. This proof dependency's module is already
  imported by the upstream abelian-variety Tate-module file.

Searches for existing statements and definitions:

- `msearch.py leanfinder`, query "The rational Tate module of an abelian
  variety over a finite field has no nonzero Frobenius fixed vector": eight
  hits on Witt-vector isocrystals and finite-field Frobenius, no match.
- `msearch.py loogle`, query `FiniteField.frobeniusAlgEquivOfAlgebraic`:
  seven hits giving the arithmetic Frobenius and its basic formulas, no
  Tate-module fixed-vector theorem.
- `msearch.py grep`, query `tateModule|rationalTateModule|TateModule`:
  no Mathlib hits.
- `msearch.py leansearch`, query "Frobenius fixed vectors of Tate modules
  of abelian varieties vanish": eight Witt-vector/Frobenius hits, no match.
- `rg` in `WeilConjectures/` for Frobenius and Tate-module names, and
  `grep -rn prop-av-tate-no-frobenius-fixed` there: found the existing
  `AbelianVariety/TateModule.lean` finiteness theorem and two geometric
  vanishing theorems. Read their full signatures, docstrings and bodies.
  `eq_zero_of_mem_tateModule_of_forall_geometricFrobenius_fixed` states the
  integral geometric clause and `eq_zero_of_map_geometricFrobenius_eq_self`
  states the rational geometric clause. Neither declaration alone, nor a
  declaration elsewhere found by the searches, states the node's four
  conclusions. Consequently this delivery states the full conjunction,
  reusing every existing construction; it does not redefine a Tate module
  or point action or restate either geometric clause as a separate theorem.
- `rg` in `lean/Sheaf` for the node id and Frobenius-fixed/Tate-module names:
  no existing statement of this conjunction. The upstream name index was
  also searched; its Tate-module entries point to the group-theoretic input.
- Exact-name search for `frobenius_fixed_tateModules_eq_zero` in Mathlib,
  `WeilConjectures/`, and `lean/Sheaf`: no pre-existing declaration.

Edge cases checked mathematically: dimension-zero abelian varieties and the
trivial geometric-point group give zero Tate modules; there is no positive
dimension assumption. The zero vectors satisfy each implication, so the
conclusions do not assert absence of all fixed vectors. The smallest finite
field and `a = 1` are admitted. `ℓ = p`, composite `ℓ`, and `a = 0` are excluded
exactly as in the source datum. The empty scheme is not an abelian variety
because it has no group identity section and is not connected in the recorded
definition. An integral coordinate at `n = 0` is forced to zero. No nonzero
denominator or nonzero vector assumption is hidden in the signature.

Validation: the first file-only `scompile.py` run found that the scoped
`CategoryTheory.MonObj` group structure on morphisms must be opened for
the rational maps. Added `open scoped CategoryTheory.MonObj`, using Mathlib's
existing instances, with no new local instance or hypothesis. All variables
and universes are explicitly bound, all lines are at most 100 characters,
and the `lean.statement` record is extracted verbatim from the declaration.
No statement dispute or statement correction is needed.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
