## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound` states
`AlgebraicGeometry.finiteType_noetherianCover_dimension_geometricFibres`.
Its single theorem has the whole proof `by sorry`; no definitions or additional
proof obligations are introduced. The node copy changes only `lean`.
No statement correction, disputed statement, new node, or dependency repair is needed.
The proof docstring supplies all nine steps of the DAG argument with their dependencies.

Clause-by-clause reading:

- Schemes T and Y and their morphism p: `{T Y : Scheme.{u}} (p : T ⟶ Y)`.
- Finite type: `[LocallyOfFiniteType p] [QuasiCompact p]`, exactly the conjunction
  specified by `def-weil-finite-type-morphism`. No separatedness is assumed.
- Finite Noetherian affine cover of Y: `hYCover` is the existence of
  `n : ℕ` and `U : Fin n → Y.affineOpens` with `(⨆ i, (U i).1) = ⊤`
  and `∀ i, IsNoetherianRing Γ(Y, (U i).1)`. `Y.affineOpens` consists of
  open subschemes which are affine. Each is canonically isomorphic to the spectrum
  of its section ring. Conversely any finite cover as in the node may be indexed
  by `Fin n`, so no finiteness or covering condition is altered.
- Finite topological dimension of Y: `hYDim : ∃ d : ℕ,
  topologicalKrullDim Y ≤ (d : WithBot ℕ∞)`. This is equivalent to dimension
  different from positive infinity and includes dimension negative infinity.
- The same finite Noetherian affine cover property of T is the first conjunct,
  with precisely the same expression as `hYCover` with T substituted for Y.
- Finite topological dimension of T is the second conjunct, an existential
  natural bound on `topologicalKrullDim T`.
- A common nonnegative integer e is `∃ e : ℕ`, outside the quantification over
  fields and geometric points. This is exactly an integer in Z_{≥0}.
- Every algebraically closed field and every indicated point:
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (h : Spec (.of Ω) ⟶ Y)`.
  The field universe equals the scheme universe; it is not an independent smaller
  universe. The theorem is universe polymorphic. All geometric points in the
  ambient category of schemes are included, with no fixed closure or residue field.
- The dimension bound is `topologicalKrullDim (↑(pullback p h) : Type u)
  ≤ (e : WithBot ℕ∞)`. This is the topological space of the scheme fibre
  product, not the set of lifts of a point. The explicit sort coercion ensures
  Lean chooses the scheme pullback.
- All integers and the local-unit implication form the last conjunct:
  `∀ N : ℤ, (∀ y : Y, IsUnit (N : Y.presheaf.stalk y)) →
  ∀ t : T, IsUnit (N : T.presheaf.stalk t)`. This does not restrict N to be
  positive, prime, or nonzero; the stalks are the local rings in the node.

Recorded statement dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`; these supply schemes,
  their locally ringed space morphisms and affine spectra.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, which the finite-type node also records.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; `Mathlib.AlgebraicGeometry.Pullbacks`
  supplies its existence for schemes.

Supporting existing notions are `Scheme.affineOpens` and `IsAffineOpen`
(from `Mathlib.AlgebraicGeometry.AffineScheme`, read through the imports) and
`IsAlgClosed` (`Mathlib.FieldTheory.IsAlgClosed.Basic`). None is redefined.
The full signatures and docstrings of all six statement dependencies were read
in the source files. The finite-cover formulation was also checked against
`isNoetherian_iff_of_finite_iSup_eq_top` in `Mathlib.AlgebraicGeometry.Noetherian`.

Proof-plan imports retain the modules of the stated proof dependencies:
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType` and its Noetherianity theorem),
`Mathlib.RingTheory.Spectrum.Prime.Topology` (spectrum/ring dimension comparison),
`Mathlib.RingTheory.KrullDimension.Polynomial` (Noetherian polynomial dimension),
`Mathlib.RingTheory.KrullDimension.Basic` (`ringKrullDim`),
`WeilConjectures.Mathlib.Topology.KrullDimension`
(`topologicalKrullDim_le_of_iSup_eq_top`, whose declaration and docstring were read),
`Mathlib.AlgebraicGeometry.Properties` (scheme sobriety),
`Mathlib.RingTheory.TensorProduct.Basic` and `.Maps` (tensor ring and universal
property), `Mathlib.LinearAlgebra.TensorProduct.Tower` (module base change), and
`Mathlib.Algebra.MvPolynomial.Basic` (polynomial rings).
The proof's open-subspace inequality is in the public KrullDimension import;
its affine/open fibre-product comparisons are in the public Pullbacks import.

Edge cases checked before drafting:

- `n = 0` is permitted for either affine cover; its supremum is the bottom open,
  equal to top exactly on an empty scheme. No nonempty index type is imposed.
- Empty Y forces empty T for any p, and both dimensions are bottom. The fibre
  quantification is vacuous where no field-valued point exists.
- Empty T over nonempty Y is allowed. Its fibres are empty and e = 0 works.
- Empty affine charts correspond to the zero ring, which is Noetherian.
- Zero-dimensional bases and e = 0 are included, as are positive-dimensional
  fibres when e is larger. A Noetherian scheme of infinite Krull dimension is
  correctly excluded by hYDim, rather than by any extra ring hypothesis.
- No characteristic constraint is imposed. The final implication includes zero
  and negative integers; on a nonempty scheme 0 is not a unit, while on an empty
  scheme the universal stalk assertion is vacuous.
- The field quantifier ranges over the same universe as schemes, so it does not
  become vacuous from choosing a smaller field universe.

Sources read: local Stacks `morphisms.tex`,
`lemma-morphism-finite-type-bounded-dimension` (Tag 0A3V), which states the ordinary
fibre bound over a quasi-compact base; the node explicitly extracts the stronger
geometric/source conclusions by the finite affine polynomial-presentation argument.
The Noetherian polynomial dimension declaration was read in
`Mathlib/RingTheory/KrullDimension/Polynomial.lean`. The current blueprint
`main-20261015` proof of `thm-cbc-finite-extension` was read for context.
The theorem follows the node's extracted geometry, not a mistaken assertion that
0A3V alone states every conclusion.

Searches for an existing complete statement (msearch.py, group NN, this item):

- `leansearch`: "A finite type scheme over a finite dimensional noetherian scheme
  has finite Krull dimension and uniformly bounded geometric fibre dimension".
  Eight hits, including `Order.krullDim_ne_top_of_finiteDimensionalOrder`,
  `AlgebraicGeometry.IsNoetherian.noetherianSpace` and finite/proper-morphism
  properties. No hit states the combined result.
- `leanfinder`: "A finite type morphism over a finite dimensional noetherian scheme
  has finite dimensional noetherian source and uniformly bounded geometric fiber
  dimensions". Eight hits, including `AlgebraicGeometry.IsFinite`,
  `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and finite-fibre
  properties. No match for the statement.
- `loogle`: `AlgebraicGeometry.LocallyOfFiniteType, topologicalKrullDim`.
  Zero hits.
- Mathlib grep via msearch: `finiteType.*(krullDim|dim)|krullDim.*finiteType|
  topologicalKrullDim.*(finite|lt_top)` in `AlgebraicGeometry`. Zero hits.
- Direct rg of `lean/Sheaf` and `WeilConjectures` for finite Noetherian affine
  covers and combinations of `IsNoetherian` with `topologicalKrullDim` found
  category-domain hypotheses, finite-type finiteness proofs, and local
  Noetherianity results, not this combined theorem. The matching finite-extension
  domain definition just collects input assumptions and does not assert preservation
  or a uniform fibre bound.
- Direct source grep for the node id returned no occurrence. Direct rg for the
  chosen declaration name and related candidate names in Mathlib, upstream source,
  side source, and the upstream names index returned no collision.

Validation uses only the prescribed `scompile.py`, followed by `deliver2.py`
preflight/dry run and delivery. Initial elaboration identified a missing explicit
QuasiCompact import and an ambiguous sort coercion on the pullback; both were
repaired without changing the mathematical statement.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
