## Worker report

The module `lean/Sheaf/TraceFormula/ProperCurveImagePositiveFibreComponent.lean`
states `AlgebraicGeometry.properCurveImagePositiveFibreComponent`, with proof `sorry` as
required for stage 2.  It uses the common scheme universe `u`, a field `k`, schemes
`T`, `G`, and `Y` over `Spec (.of k)`, finite type hypotheses on all three structure
maps, proper `k`-morphisms `r : T ⟶ G` and `p : G ⟶ Y`, and surjectivity of `r`.

The Lean rendering of the hypotheses and conclusion is:

* `[Field k]` renders that `k` is a field.
* `[T.Over (Spec (.of k))]`, `[G.Over (Spec (.of k))]`, and
  `[Y.Over (Spec (.of k))]` introduce the three schemes over `k`.
* The six hypotheses
  `[LocallyOfFiniteType (T ↘ Spec (.of k))]`, `[QuasiCompact (T ↘ Spec (.of k))]`,
  and the corresponding pairs for `G` and `Y`, render finite type over `k`.
* `(r : T ⟶ G) [r.IsOver (Spec (.of k))] [IsProper r]` renders the proper
  `k`-morphism `r`; `(p : G ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]`
  does the same for `p`.
* `[Surjective r]` renders surjectivity of `r`.
* `hT : ∀ Z : Set (T : Type u), Z ∈ irreducibleComponents (T : Type u) →
  topologicalKrullDim Z = (1 : WithBot ℕ∞)` renders that every irreducible
  component of `T` has topological Krull dimension one.
* `(y : Y)` and `hy : 0 < topologicalKrullDim (p.fiber y)` render a point of `Y`
  whose scheme-theoretic fibre has positive dimension.
* The conclusion `y ∈ closedPoints (Y : Type u)` renders that `y` is closed.
* The existential `Z : Set (T : Type u)` with
  `Z ∈ irreducibleComponents (T : Type u)` renders an irreducible component of
  `T`.
* `((r ≫ p).base '' Z) = ({y} : Set Y)` renders `(p ∘ r)(Z) = {y}`.
* `topologicalKrullDim (r.base '' Z) = (1 : WithBot ℕ∞)` renders
  `dim r(Z) = 1`, with `r(Z)` as the image subset with its subspace topology.

The explanatory source clause that the image `r(Z)` is closed is represented by the
properness hypothesis on `r` and by using the image subset `r.base '' Z`; it is not a
separate stronger conclusion.  No separatedness, reducedness, or algebraic-closedness
hypothesis was added.

The statement follows the source place Stacks Project `varieties.tex`, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, parts (2)(b)--(d) and the associated
proper-image dimension argument.  The proof docstring records the five source proof
steps and cites the proof dependencies named by the DAG.

Dependencies used (all are imported through Mathlib declarations):

* `def-weil-field`: `Field`.
* `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`.
* `def-weil-irreducible-components`: `irreducibleComponents`.
* `def-kun-topological-krull-dimension`: `topologicalKrullDim`.
* `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`.
* `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over` and
  `CategoryTheory.Over`'s `IsOver` morphism class.
* `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`.
* `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`.
* `def-weil-closed-points`: `closedPoints`.

The full declarations were read in the pinned Mathlib sources:
`AlgebraicGeometry/Morphisms/FiniteType.lean`, `QuasiCompact.lean`, `Proper.lean`,
`UnderlyingMap.lean`, `Fiber.lean`, `Topology/Irreducible.lean`,
`Topology/KrullDimension.lean`, `Topology/JacobsonSpace.lean`, and
`AlgebraicGeometry/Over.lean`.

Edge cases checked:

* The common universe `u` permits arbitrary finite-type schemes and keeps the point,
  fibre, image, and dimension expressions in compatible universes.
* Empty `T` cannot satisfy the surjectivity and positive-fibre assumptions; no
  nonemptiness assumption was added.
* The fibre dimension inequality is strict positivity in `WithBot ℕ∞`, so the zero-
  dimensional and empty-fibre cases are excluded exactly as the node states.
* Components are quantified as arbitrary members of `irreducibleComponents`, so no
  reducedness or algebraic-closedness assumption is silently imposed.
* The field `k` is arbitrary; no characteristic or algebraic-closure condition was
  introduced.

Searches made:

* `msearch.py ... leanfinder "proper surjective morphism one dimensional scheme
  positive dimensional fibre irreducible component"`: eight hits, all generic
  dominance/surjectivity/fibre declarations; no matching theorem.
* `msearch.py ... loogle "IsProper Surjective topologicalKrullDim fiber
  irreducibleComponents"`: zero hits (the query also reported `IsProper` as unknown
  to that Loogle endpoint).
* `msearch.py ... grep "proper.*surjective|positive.*fiber|irreducibleComponents.*fiber"
  Mathlib/AlgebraicGeometry`: zero matching theorem hits.
* `rg` over `WeilConjectures/` and the existing `lean/Sheaf/` tree for the theorem
  name and the proper positive-fibre component formulation: no existing declaration.
* The node's recorded Mathlib searches (LeanSearch, Loogle, LeanFinder, and grep)
  were also read; they report no exact match.

No new definition node or dependency module was needed, and no statement correction or
`STATEMENT-DISPUTED` flag applies.

## Returned-delivery repair

The immutable-head return (919fc9d3c0ff) identified an artifact-name issue only. I
retained the theorem statement and all hypotheses verbatim, refreshed the `lean.date`
field to the current UTC date, and added the corresponding repair note to the module
docstring. The packet was rerun through `deliver2.py --no-push` and passed compilation
and preflight.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
