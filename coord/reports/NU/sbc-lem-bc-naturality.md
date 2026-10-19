# Stage-2 report: `sbc-lem-bc-naturality`

## Worker report

The item keeps the unbounded naturality statement from
`literature/blueprint/master/blueprint/sec-smooth-base-change/sk-def-bc/sbc-lem-bc-naturality.md`,
node order 1369.  The proof expands the base-change composite into the unit,
two canonical composition identifications, and the counit; naturality of each
factor and associativity give the displayed square.  The only delivered module
is `lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeNaturality.lean`, declaring
`AlgebraicGeometry.Etale.derivedBaseChangeMap_naturality`; its proof is `sorry`
as required for a stage-2 statement.  Searches found no exact existing
unbounded lemma; the bounded-below lemma is not an exact attachment.

## Second reading by NU

The node statement, source place, and both statement dependencies were read.
The Lean theorem has the same objects, hypotheses, quantifier order, and
conclusion: a commutative naturality square for every morphism `v : K ⟶ K'` in
the unbounded derived category of étale `Λ`-modules.  Its coefficient universe
is `Λ : Type (u + 1)` and its schemes are `Scheme.{u}`, with no properness,
finiteness, characteristic, or boundedness assumptions.  The two sides are
exactly the maps of `Lf*Rg*` and `Rh*Le*`, and the base-change component is the
recorded `derivedBaseChangeMap` on `sq.toCommSq.flip`.

The source proof's four steps are rendered by the declaration docstring:
unit naturality, naturality of both canonical identifications, counit
naturality, and associativity.  The dependency `sbc-def-base-change-map`
defines the same unbounded map and the dependency `sbc-def-base-change-square`
supplies the chosen Cartesian square; no private replacement or arbitrary map
is introduced.  The module and declaration docstrings name the source and
`(blueprint: sbc-lem-bc-naturality)`.  The empty/identity square, zero object,
zero morphism, arbitrary characteristic, and empty or zero complexes are all
covered because the assertion is ordinary naturality with no extra hypotheses.

Mathlib/project searches were checked against the recorded searches and by
searching the source and group clone for `derivedBaseChangeMap` and
`baseChangeMap_naturality`; only bounded-below or unrelated proper-base-change
results occur.  Server-only `scompile.py` compilation of the delivered module
completed successfully.  No lake build, live Lean write, repository mutation,
or branch-head change was performed.
