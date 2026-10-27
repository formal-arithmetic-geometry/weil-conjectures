## Worker report

The module `Sheaf.AlgebraicGeometry.FlatMaximalDominanceBaseChange` states
`AlgebraicGeometry.flat_maximalDominance_and_baseChange`, with one `sorry` and no
new definitions. The node is unchanged except for its `lean` attachment.

I read ILO, Travaux de Gabber, Exposé II, printed p. 23 (PDF p. 29), including
1.1.1, Definition 1.1.2, Example 1.1.3 and Proposition 1.1.5. These explicitly
state the two assertions without finiteness hypotheses. The single conjunction
keeps the first assertion independent of maximal dominance of `f`.

Hypothesis and clause correspondence:

- Schemes `X`, `Y`, `Y'`: `{X Y Y' : Scheme.{u}}`, with the universe explicitly
  declared and `autoImplicit false`.
- Scheme morphisms `f : X → Y` and `h : Y' → Y`: the corresponding morphism
  binders `(f : X ⟶ Y) (h : Y' ⟶ Y)`.
- Flatness of `h`: `[Flat h]`. Mathlib's `Flat.iff_flat_stalkMap` identifies this
  affine-local class with the stalkwise condition of the dependency node.
- A component-generic point of a scheme `T`: a set `C` satisfying
  `C ∈ irreducibleComponents T`, a point `η : T`, and `IsGenericPoint η C`.
  This uses precisely the dependency definitions, with no chosen generic point.
- Maximal dominance of `h`: the first conjunct universally quantifies those
  components and points in `Y'`, and concludes
  `∃ D ∈ irreducibleComponents Y, IsGenericPoint (h η) D`.
- The conditional hypothesis that `f` is maximally dominant: the antecedent of
  the second conjunct repeats the same predicate on `X`, `Y` and `f`.
- The base-changed source `X ×_Y Y'`: `pullback f h`. The projection to `Y'` is
  `pullback.snd f h`, so the consequent of the second conjunct requires
  `IsGenericPoint (pullback.snd f h η) D` for some component `D` of `Y'`, for
  every component-generic point `η` of that pullback.
- There are no finite-type, surjectivity, reducedness or Noetherian binders.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`; morphisms are locally ringed-space maps.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and its `iff_flat_stalkMap` equivalence.
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents`, the maximal irreducible subsets.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, defined
  by `closure {η} = C`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.snd`, with scheme pullbacks
  supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.

Every statement dependency is publicly imported. Plain proof imports provide
all recorded proof dependencies: component containment/cover from
`Mathlib.Topology.Irreducible`; scheme sobriety from
`Mathlib.AlgebraicGeometry.Properties`; `Flat.generalizingMap` from
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`; flat base-change instances
and `Flat.SpecMap_iff` from `Mathlib.AlgebraicGeometry.Morphisms.Flat`; fibres and
`Scheme.Hom.fiberHomeo` from `Mathlib.AlgebraicGeometry.Fiber`; residue fields
and `Scheme.Hom.residueFieldMap` from
`Mathlib.AlgebraicGeometry.ResidueField`; and `RingHom.Flat.of_isField` from
`Mathlib.RingTheory.RingHom.Flat`. The theorem docstring contains all five
proof steps, including the canonical two-fibre comparison and the subspace
specialization argument.

Edge cases checked before writing:

- An empty source has no component-generic points, so maximal dominance is
  vacuous, as in the source definition. Empty `Y'` also gives an empty pullback;
  both clauses remain meaningful. A morphism into an empty target forces its
  source empty.
- Disconnected and reducible schemes are covered by quantifying over every
  component, rather than assuming `IrreducibleSpace` or using `Set.univ`.
- Nilpotents and non-Noetherian schemes impose no restriction on any binder.
- Identity base change returns the original maximal-dominance condition up to
  the canonical pullback isomorphism. Neither clause requires flatness of `f`.
- A flat open immersion need not be surjective; its generic-point assertion is
  still exactly the first conjunct. Infinite component sets are allowed.

Searches for an existing statement (2026-10-24):

- `msearch.py`, LeanFinder: "Flat morphisms preserve generic points of
  irreducible components and maximal dominance survives flat base change".
  Eight hits, including `Flat.generalizingMap`, `Flat.isStableUnderBaseChange`,
  `RingHom.Flat.generalizingMap_comap` and `Algebra.HasGoingDown.of_flat`.
  None states the conjunction or its second clause.
- `msearch.py`, Loogle: `AlgebraicGeometry.Flat, GeneralizingMap`. One hit,
  `AlgebraicGeometry.Flat.generalizingMap`; this is a proof ingredient.
- `msearch.py`, grep: `maximally.?dominant|MaximallyDominant|generalizingMap`
  in Mathlib `AlgebraicGeometry`. Twelve hits concern generalizing maps;
  there is no maximal-dominance predicate or complete theorem.
- `msearch.py`, LeanSearch: "A flat morphism sends generic points of irreducible
  components to generic points and maximal dominance is preserved by flat base
  change". Eight hits, including `Flat.generalizingMap`,
  `Flat.isStableUnderBaseChange`, `Module.Flat.isBaseChange`, and
  `RingHom.Flat.isStableUnderBaseChange`; no complete match.
- `rg` in project `WeilConjectures` and `Sheaf` for generic-point/component
  expressions and case-insensitive maximal dominance; `grep -rn` for this node
  id in `WeilConjectures`. No existing statement of this lemma. The alteration
  category `AlgebraicGeometry.PrimeToEllAlteration.Alt` encodes maximal dominance
  inline alongside finite type, reducedness and finite generic residue fields;
  it is not a predicate applicable to these unrestricted morphisms. Its module
  was read. This delivery likewise uses the basic predicates inline and creates
  no duplicate definition.

There are no disputed statements, missing notions, dependency repairs, or new
nodes. Only the named theorem is postponed. Server compilation through
`scompile.py` succeeded for both sandbox and final library module names, with no
errors or unexpected warnings. Delivery preflight results are recorded below.

The required `deliver2.py --no-push` dry run printed OK: the packet passes
the server preflight and compiles (dry-run commit `7bb55c8663d`).

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
