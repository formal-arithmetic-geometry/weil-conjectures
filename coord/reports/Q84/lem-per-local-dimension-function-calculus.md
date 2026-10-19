## Worker report

The module `Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus` states
`AlgebraicGeometry.local_dimension_function_calculus`, with `sorry` as its only proof.
It uses the existing predicate `AlgebraicGeometry.Scheme.IsGeometricDimensionFunction`
from `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`, recorded by the landed node
`def-per-geometric-dimension-function`. No new definition or dependency module is delivered.

Each hypothesis and clause is rendered as follows:

- `T : Scheme.{u}` and `[IsNoetherian T]` render the Noetherian scheme hypothesis.
  `hcat : ∀ U : T.affineOpens, IsUniversallyCatenary Γ(T, U)` renders universal
  catenarity on every affine chart, including the bounded saturated-chain condition
  and Noetherian coordinate rings from `def-exc-excellent-ring`.
- `∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ δ : U.toScheme → ℤ,
  Scheme.IsGeometricDimensionFunction U.toScheme δ` gives a dimension function on
  an open neighbourhood of every point.
- `(∃ (R : CommRingCat.{u}) (_ : IsLocalRing R), Nonempty (T ≅ Spec R)) →
  ∃ δ : T → ℤ, Scheme.IsGeometricDimensionFunction T δ` gives one on the whole
  scheme when it is the spectrum of a local ring, up to scheme isomorphism.
- `∀ (δ : T → ℤ), Scheme.IsGeometricDimensionFunction T δ →
  ∀ (p q : StrictGeometricPoint T) (a : p ⟶ q), ∃ n : ℕ,
  StrictGeometricPoint.codimension a = (n : WithBot ℕ∞) ∧
  δ p.underlying - δ q.underlying = (n : ℤ)` gives the formula for every
  dimension function and every geometric specialization. The common natural number
  expresses finiteness and compares the extended-natural codimension with the integer
  difference without an ill-typed equality between them.
- `∀ p, StrictGeometricPoint.codimension (𝟙 p) = 0` and
  `∀ p q (e : p ≅ q), StrictGeometricPoint.codimension e.hom = 0` explicitly
  give zero codimension for identity specializations and geometric isomorphisms.

The reused dimension-function predicate quantifies over geometric points of a strict
localization, asks that the topological Krull dimension of their image closure be one,
and concludes that the value at the source image equals the value at the target plus
one. This is precisely the item's difference-one condition. It is the definition itself,
not a private copy or a new assumption on arrows.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`:
  `AlgebraicGeometry.Scheme.IsGeometricDimensionFunction`.
- `Sheaf.AlgebraicGeometry.GeometricSpecializationCategory`:
  `AlgebraicGeometry.StrictGeometricPoint`, `StrictGeometricPoint.underlying`,
  `StrictGeometricPoint.codimension` (closure dimension in the target strict localization),
  and the induced category of strict localizations over the base.
- `Sheaf.RingTheory.ExcellentRing`: `IsUniversallyCatenary`, `IsCatenaryRing`,
  and the bounded prime-chain predicates.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`, and
  `Scheme.strictHenselization_properties`.
- Mathlib's `Scheme.SpecToEquivOfField` and `IsAlgClosed` describe the geometric points;
  `ringKrullDim` and the topological dimension interface give the closure dimension.

The module retains the recorded proof-dependency imports and the seven-step natural-language
proof in its theorem docstring: catenary chain lengths; deleting finitely many components;
gluing the componentwise functions; geometric immediacy and the local-scheme case;
strict-local comparison; pulling back the dimension function along strict localization;
and telescoping a maximal saturated chain to compute codimension. Every variable and
universe is explicitly bound, with `set_option autoImplicit false`.

Edge cases checked: empty schemes (local existence is vacuous); zero-dimensional local
schemes; a one-dimensional trait (difference one); identities and geometric isomorphisms
(zero); and a reducible union of components of different dimensions (the proof uses
componentwise gluing). The local-ring existential does not exclude the empty scheme
from the other clauses. All three dimension-function clauses use the same landed predicate.

Search record: the saved packet's `msearch.py ... leanfinder` query for dimension functions
on universally catenary Noetherian schemes returned unrelated Krull-dimension hits;
`msearch.py ... loogle 'dimensionFunction'` returned zero hits. The earlier `rg` searches
of Mathlib, `WeilConjectures`, and `lean/Sheaf`, and the `tools/blueprint_refs.py search
 dimension-function` search, were incomplete: their claimed absence of a DAG notion was
incorrect. The repair directly read the existing node `def-per-geometric-dimension-function`
and its recorded module, and the specialization-category node and module. They supply the
required notions, so the duplicate node and module have been removed.

No `STATEMENT-DISPUTED` flag or statement correction is needed. On the review's advisory:
Mathlib's `IsNoetherian` includes quasi-compactness, whereas `IsLocallyNoetherian` means
Noetherian affine rings. The node explicitly starts with “Noetherian universally catenary
scheme”; this repair retains the reviewed `[IsNoetherian T]` hypothesis and records the
advisory rather than silently changing that hypothesis.

## Repair of return at 3ee08f3b8df1

H12/H4: removed `def-dl-a1-dimension-function.json` and `DimensionFunction.lean`.
Replaced the duplicate id in `stmt_deps` by `def-per-geometric-dimension-function`.
The module now imports `Sheaf.AlgebraicGeometry.GeometricDimensionFunction` and uses
`Scheme.IsGeometricDimensionFunction` in the local-existence, local-scheme, and
codimension-formula clauses. It imports the specialization category explicitly for the
arrows and codimensions. All other theorem clauses and the mathematical node statement
are retained. The saved packet differs from the current shared base only in the item's
`lean` record and its two additional statement dependencies; the delivery wrapper rebases
onto current `newtargets-dag`.

The first required dry run of the saved packet passed mechanically at `92d232e46a`.
That packet still contained the reviewed duplicate, so this repair was applied before
repeating compilation and preflight.

## Second reading by Q84

Reopened the current base item, its saved node, the revised theorem, the landed geometric
dimension-function definition and the specialization-category definition. Matched the
Noetherian and affine universal-catenarity hypotheses; the point, open and membership
quantifiers; existence on an entire local scheme; the arbitrary dimension function and
arbitrary geometric arrow; the common finite natural number; and both zero-codimension
clauses. The original mismatch was the second definition of the dimension-function
notion; it is removed and all three uses now reference the landed declaration. The
predicate's equation `δ(source) = δ(target) + 1` is exactly the stated difference-one
condition. The specialization category supplies the same geometric arrows and closure
codimension as before. No further mismatch was found. This rereading was performed in
this worker session; the dispatcher's prohibition on starting other agents was respected.
