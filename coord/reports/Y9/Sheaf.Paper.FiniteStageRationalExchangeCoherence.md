## What changed

The original data declarations move verbatim to FiniteStageRationalExchangeData,
publicly reexported by the item, so the operation and square proofs can import them
without a cycle. The original theorem first propagates invertibility through the
three stalk maps, then combines four operation witnesses with the square theorem.

StageSystemKaroubi proves the generic cocycle, morphism and transformation coherence
by the fully faithful restriction to identity projectors. FiniteStageKaroubiExtension
identifies the actual coefficient systems with their generic supported extensions,
then transports the explicit morphisms and compatible transformations with their
component formulas and units. RationalOperationCoherence and
RationalSquareExchangeCoherence assemble these from the raw results.

## Proved and sorry left

The proof closes the original hole
AlgebraicGeometry.Scheme.FiniteStageRationalExchange.finiteStageRationalExchangeCoherence,
with a complete assembly term, to two independent raw results. This is a decomposition, not a net
hole reduction: one original hole closed in the item; two lower holes added.

Remaining holes, each exactly a named public theorem with a source and full proof plan:

- AlgebraicGeometry.Scheme.FiniteStageRationalExchange.rationalRawOperationCoherence
  (lem-sbc-raw-operation-coherence): integral and raw scalar comparison construction
  for one scheme morphism, including identity and tower normalization.
- AlgebraicGeometry.Scheme.FiniteStageRationalExchange.rationalRawSquareExchangeCoherence
  (lem-sbc-rational-raw-square-exchange-coherence): the raw composite comparisons and
  compatibility of the canonical geometric exchange.

The Karoubi system, morphism, Hom, additivity and unit extension proofs contain no
sorry. Neither retained assembly theorem contains a sorry. All eight modules compile together through lcompile.py, including
the unchanged original statement (36.8 seconds) and the square assembly (31.8
seconds), with no warnings. No data is chosen from an undetermined existence
theorem, and no definition contains a sorry.

## No longer needed

The generic supported extension proves all finite-stage Karoubi tower, naturality,
additivity and unit clauses directly from Mathlib's functorExtension₂ and fully
faithful restriction. No extra geometric or constructibility lemma is used for them.
The original public imports now reside in the publicly reexported Data module;
none is removed from the public API. The two new proof-only imports of the item
are RationalOperationCoherence and RationalSquareExchangeCoherence.
No original dependency is withdrawn: the raw results still need the original scalar,
localization, reflector and completed-exchange arguments. No source-library module
or declaration is removed. The actual system is identified with its generic supported extension by the
isomorphism identity-composition law; transport lemmas preserve the displayed
object and comparison formulas.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The unchanged predicates package a long
integral/raw construction and a generic Karoubi extension together. Separating them
permits actual Lean proofs of the supported extension and the final assembly.
At equal coefficient fields the raw transition is literally identity but the
integral tensor unit remains; both raw obligations explicitly retain that branch.
The actual Karoubi associator includes an identity composition adapter; it must be
removed by the isomorphism unit law before applying the generic cocycle proof.

The downstream search reports zero Lean importers of the item, but its blueprint
parent is unfinished and still needs it; no withdrawal is inferred.

## New nodes

lem-sbc-raw-operation-coherence is the strictly smaller integral/raw operation
construction before Karoubi extension. lem-sbc-rational-raw-square-exchange-coherence
is the strictly smaller raw composite-exchange argument, given all four operation
packages. Both preserve the source's ambient hypotheses and exact normalization.

lem-sbc-stage-system-karoubi-extension records the proved generic supported system,
morphism and compatible transformation constructions. lem-sbc-finite-stage-karoubi-extension
records their specialization to the actual coefficient systems, with units.
lem-sbc-rational-operation-coherence and lem-sbc-rational-square-exchange-coherence
record the proved assembly of the raw and supported clauses.

Change record: coord/changes/Y9-finite-stage-coherence-data.md. The data move preserves
the four existing declarations verbatim and publicly reexports them. The added
HasRawOperationCoherence is exactly the integral/raw prefix of the old predicate.

def-sbc-finite-stage-rational-exchange-data records the verbatim data move and the
raw-prefix predicate; the original node retains the two previously proved formula
theorems and the final coherence theorem.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
