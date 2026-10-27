## What changed

Proved WeilConjectures.LocalFrobeniusLarge.pointFibre_existsUnique from the scalar tower
coherence equation using the existing StageSystem.descFunctor. Object and representative
formulas are definitional; uniqueness uses Functor.hext and PairCategory.hom_induction.
The quotient descent, category laws and independence of representatives use the existing
proved StageSystem implementation, rather than another existence assumption.

Extracted one strictly smaller local coherence theorem, stageScalar_tower, in its own module.
It asserts equality of two scalar comparison composites at one object and three finite
coefficient stages; it does not assert any functor on the quotient. Moved the five existing
public scalar declarations and their proved private helpers verbatim into the publicly
reexported LocalFrobeniusLargeScalarTower to avoid a dependency cycle. No data, signature or
existing public import changes. Updated the node route and module attachments.

Server compilation of both delivered modules passed. The final item also enables
respectTransparency for the new quotient proof and subsequent declarations.

## Proved and sorry left

Closed: WeilConjectures.LocalFrobeniusLarge.pointFibre_existsUnique (the only original hole;
node def-weil-local-frobenius-trace). Its proof and uniqueness now contain no sorry.

Added and left: WeilConjectures.LocalFrobeniusLarge.stageScalar_tower (one hole;
node lem-weil-large-point-scalar-tower). This is a decomposition, not a net hole reduction:
one original hole closed, one strictly smaller local coherence hole added, zero holes in
the item module and one in the delivered set. The relocated scalar prerequisite block
has zero holes;
its stageScalar_existsUnique proof is unchanged.

The remaining lemma combines the prescribed sections/scalar coherence with the existing
fieldDerivedHomologyIso_tower and the tensor-generator normalization. A related existing
PointRealizationScalarCoherence records ambient derived scalar coherence, but neither
its literal stage-system transports nor its large-closure tensor flattening matches this
local equation directly. No new arbitrary data is chosen from an existence theorem.

## No longer needed

No modules or DAG nodes are withdrawn or pruned. No previous public import is removed.
The original node's other proof dependencies still serve its existing finite-stage and
local-trace constructions, so they are retained. StageSystem.Const is the only additional
proof implementation import. The tower theorem shares the publicly imported scalar
prerequisite module.
The unchanged finite-stage block is relocated solely to make this dependency acyclic.

## Where the brief, the DAG or earlier work was wrong

The DAG's latest scalar-comparison proof explicitly left pointFibre_existsUnique unchanged
and provided no stated large-coefficient cocone equation. Existing quotient descent already
handles all categorical work once that equation is supplied. The remaining local equation
is now separately stated, sourced and assigned a node. The unit route is unchanged.

Edge cases checked in the local statement: E=L, L=M, all three fields equal, identity
inclusions, zero complex, and arbitrary rational representatives. No strict inclusion,
faithfulness, injectivity of transition maps, separatedness or extra bounds are assumed.
The source associator is retained in its actual direction.

## New nodes

lem-weil-large-point-scalar-tower: local tower coherence of the normalized scalar comparison.
It is strictly the coherence step preceding common-stage quotient descent. Its module is
Sheaf.Paper.LocalFrobeniusLargeScalarTower. The docstring and node give the sections tower,
H^0 tower and tensor-generation argument. Mathlib searches found only generic tensor tower
ingredients; the existing scalar and cohomology declarations were read before extracting it.
The generic StageSystem.descFunctor is used as a proved library tool for the quotient.

Change record: coord/changes/T8-large-point-scalar-relocation.md.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
