## What changed

Replaced `AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_stalk` by a Lean proof
combining the residue-field calculation, comparison of geometric lifts, and an explicit
Frobenius-module conjugacy. Its signature is unchanged. The residue exponent is the finrank
of the actual residue-field embedding and is independent of the sheaf. Injectivity of
powers of the finite base-field cardinality proves the required degree relation.

The existing source `charpoly_frobeniusEnd_stalkAt_of_dvd` handles the change from the
transported geometric lift to the canonical lift. A proved private `transport_comm_square`
pastes two `globalSectionsTransport` squares, including their different algebraic closures.
The proof applies it to the iterated Weil-map square and converts the resulting stalk
isomorphism to `FrobeniusModule.Equiv`. A proved private `stalk_charpoly_of_square`
keeps the two sheaf objects abstract during this conversion. Applying the raw transport
square directly to the concrete powered sheaf caused expensive kernel conversion;
the abstract API reduces the complete item's compile to 7.5 seconds without changing
any definition or compiler limit. This explicitly supplies the conjugacy argument;
it does not leave that argument in a new stalk-comparison theorem.

Added `Sheaf.DeligneLaumon.PoweredGeometricPullbackIterate`: the canonical carrier
isomorphism constructed from the proved carrier equation,
and the remaining point-free iterated Weil-map square. The power-intertwining lemma is
a proved private helper in the item. Only this last equality remains
unproved. It is a strictly smaller part of the source argument: it concerns morphisms
of sheaves and no points, residue fields, Frobenius modules, or characteristic polynomials.
It applies to the same explicit functor; it does not choose new functor data.

Added private proof imports of the new module, `StalkCharpoly`, `BaseChangeField.Geometric`, and `Evaluation`.
No existing definitions, theorem statements, source-library modules, or consumers changed.

Validation: `lcompile.py` accepted the complete item (7.5 seconds). The new iterate module
was also accepted in the sandbox's import-order compile. Profiling options and diagnostic
code were removed before delivery. The original signature is preserved verbatim, and
both Lean files have lines of at most 100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_stalk`
(node `lem-zl-powered-geometric-pullback-stalk`) by a Lean combination.
The item has zero remaining holes, down from one.

Added one hole in
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_frobeniusPowStr`
(node `lem-zl-powered-geometric-pullback-iterate`). Its docstring states the base cases,
the induction, the source block-composition law and the canonical coherence maps.
This is a decomposition of one hole into one smaller hole, not a net hole closure.
The power-intertwining lemma, canonical carrier isomorphism, arithmetic argument,
projection/lift calculation and stalk-conjugacy glue are proved.

## No longer needed

No original imports, nodes, or modules are removed or withdrawn. The new iterate module
imports only `StalkFrobenius` for its structure-map statement; `StalkCharpoly` is a private
proof import of the item where its comparison theorem is used. Both original declared
proof dependencies remain used. No curve-model, diagram, lissity, irreducibility,
semisimplicity, or common-stage comparison is imported for the local argument.
The unit's route and all parent consumers remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned residue-field arithmetic and geometric-lift independence already have proved
source/Mathlib APIs; neither needs another split. The missing source API is precisely the
iterated Weil-map square for the new powered functor. Ordinary same-field pullback's
stalk theorem does not directly apply to this functor and its two algebraic closures.

The stronger projection and base-compatibility hypotheses of the original signature are
preserved. As in `GeometricConstituentOrbit`, the unused-variable linter is disabled
only for this theorem because its original signature retains those redundant hypotheses.
The proof needs the projection square `hup`, Frobenius commutation `hu`, and
finite-field cardinality `hcard`; the remaining compatibility data are not needed once
one compares arbitrary lifts by the existing source stalk theorem.

Edge cases checked mathematically: zero sheaves; arbitrary nonsemisimple Weil maps;
coincident image points; residue exponent one; powers zero in the new identity (identity
Weil maps and pullback units). The target theorem retains its positive extension exponent.

## New nodes

`lem-zl-powered-geometric-pullback-iterate` records the remaining equality of actual
underlying pro-etale sheaf maps. Its proof is induction and coherence of the explicit
`powFunctor`/`mapOfNatIso` construction, before evaluating any stalk. It inherits the
original chapter and unit and cites paragraphs 1--3 of the same blueprint proof.
Searches with `msearch.py` (LeanSearch, LeanFinder and Mathlib grep), source-library search,
and a whole-blueprint duplicate search found no statement of this powered inverse-image
identity. No change record is required because all existing signatures and definitions
are unchanged.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
