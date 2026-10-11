## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ZeroDimensionalBaseChangePoints.lean` states
`AlgebraicGeometry.zeroDimensional_baseChange_points`. It binds fields `k`, `k'`, an
algebraically closed `k`, an algebra structure `k → k'`, and a scheme `C` over `Spec k`.
The separated, locally finite type, and quasi-compact hypotheses are the stated finite-type
scheme conventions, and `hC` renders `dim C ≤ 0` as `topologicalKrullDim C ≤ 0`.

The first conclusion `Finite C ∧ DiscreteTopology C` renders finiteness and discreteness of
`|C|`. For each `c : C`, `c ∈ closedPoints C` renders closedness and
`IsIso ((C ↘ Spec (.of k)).residueFieldMap c)` renders the residue-field identification
`κ(c) = k` through the structure morphism. The next conjunct gives, for each `c`, a
unique point of the pullback whose projection is `c`, rendering the one-point fibre
`Spec (κ(c) ⊗ₖ k') = Spec k'`. The following conjunct is the dimension bound on the
base change. The final `IsHomeomorph` is the claimed homeomorphism induced by `π`.

The module imports `Sheaf.AlgebraicGeometry.BaseChangeConventions`, whose pullback and
projection declarations are used for `C_{k'}` and `π`. The dependency node's prior record
was not usable as a self-contained base-change notion, so its module and node copy are
included in this delivery; its `lean.note` records this reason. Mathlib leaves used are
`topologicalKrullDim`, `Scheme.residueField`, `closedPoints`, and `Spec`.

Edge cases checked include the empty scheme (finiteness and point clauses are vacuous),
the bound `topologicalKrullDim C = ⊥`, and arbitrary field extensions `k'` (no
algebraic-closedness assumption on `k'`).

Searches made:

- LeanFinder search for “base change of a zero-dimensional scheme ... points”: no exact
  declaration; only general base-change stability results.
- Loogle search for `topologicalKrullDim, IsHomeomorph, residueFieldMap`: no exact combined
  statement.
- Mathlib grep for `baseChange.*zero-dimensional|residueFieldMap`: individual declarations
  only, no combined lemma.
- `rg` over the source and project for `zeroDimensional_baseChange_points` and
  `base change.*zero-dimensional`: no existing declaration.

## Dependency modules

- `def-pc-base-change`: copied with `BaseChangeConventions.lean` and a `lean.note`
  explaining why its previous record was unusable for this dependency's full notion.

## Earlier second reading (a previous round; superseded)

I reread the node and signature. Every hypothesis is bound explicitly: field extension,
algebraic closedness, scheme-over-`k`, separatedness, finite type, quasi-compactness, and
dimension. The conjunctions correspond in order to finite/discrete points, closed points
and residue fields, singleton fibres, base-change dimension, and the homeomorphism induced
by `π`. The signature compiles with the copied dependency module using `scompile.py`.

## Second reading by Q1

I independently compared the node's objects, hypotheses, and conclusion with
`AlgebraicGeometry.zeroDimensional_baseChange_points`.

- The field extension is rendered by `(k k' : Type v) [Field k] [Field k'] [Algebra k k']`, with
  `[IsAlgClosed k]`; this is the stated algebraically closed base field and arbitrary extension.
- The scheme over `Spec k` is `(C : Scheme.{v}) [C.Over (Spec (.of k))]`.  The node's separated,
  finite-type hypotheses are rendered without strengthening by
  `[IsSeparated (C ↘ Spec (.of k))]`, `[LocallyOfFiniteType ...]`, and
  `[QuasiCompact ...]`.
- The dimension hypothesis is exactly `hC : topologicalKrullDim C ≤ 0`.
- Clause (1) is `Finite C ∧ DiscreteTopology C`; for every `c : C`, the closed-point and
  residue-field assertions are `c ∈ closedPoints C ∧ IsIso ((C ↘ Spec (.of k)).residueFieldMap c)`.
- Clause (2)'s one-point fibre is rendered as `∀ c : C, ∃! z : pullback ...,
  (pullback.fst ...).base z = c`; the pullback is precisely the node's `C ×_{Spec k} Spec k'`
  and its projection `π`.  The base-change dimension bound is the following
  `topologicalKrullDim (pullback ...) ≤ 0`, and the final clause is the required
  `IsHomeomorph (pullback.fst ...).base`.

The empty scheme is covered: `Finite`, discreteness, and both universal point clauses are
vacuous, while the dimension bound and homeomorphism retain their ordinary meanings.  The
empty-dimensional value `⊥`, arbitrary `k'` (including non-algebraically-closed extensions),
zero-dimensional `C`, and `n = 0`/characteristic edge cases introduce no omitted hypotheses.
Universes use one `v` consistently for fields, schemes, and the pullback.

I searched Mathlib, the source repository, and the project for zero-dimensional base-change
point statements and for combined residue-field/homeomorphism results; only the individual
ingredients (`topologicalKrullDim`, `closedPoints`, `residueFieldMap`, `Spec`, and pullback)
were found.  The dependency `def-pc-base-change` had an unusable prior record for the full
base-change convention, so its reviewed `BaseChangeConventions` module and node lean record
are included; no other mismatch was found and the item statement was unchanged.
