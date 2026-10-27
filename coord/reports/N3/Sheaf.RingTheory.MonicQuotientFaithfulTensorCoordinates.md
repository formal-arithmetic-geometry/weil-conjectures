## What changed

Proved `AdjoinRoot.exists_monicQuotient_faithful_tensor_coordinates` in
`Sheaf.RingTheory.MonicQuotientFaithfulTensorCoordinates`, without changing its signature,
public imports, or definitions. The power basis is constructed separately over nontrivial
and subsingleton rings. Mathlib supplies the concrete tensor coordinate formulas; tensor
induction proves naturality. Transferring faithful flatness from the nonempty finitely
supported free module along the basis representation proves faithful flatness and the
exactness equivalence. Updated the item node's proof and proof origin to match this route.

## Proved and sorry left

Closed the sole original hole:
`AdjoinRoot.exists_monicQuotient_faithful_tensor_coordinates`
(node `lem-sfb-monic-quotient-faithful-tensor-coordinates`).
One of one holes proved; zero holes added; zero holes remain; zero split-off statements.

## No longer needed

No modules, imports, or dependency nodes are pruned. All six declared dependency nodes
remain used, as Mathlib definitions or the monic-quotient power-basis leaf. The explicit
construction of the tensor isomorphisms and coordinate-zero reflection argument are
replaced by existing Mathlib equivalences and faithful-flat exactness lemmas. No public
imports changed.

## Where the brief, the DAG or earlier work was wrong

The statement is correct, including the zero ring and d = 1. The earlier plan is longer
than needed: Mathlib's `Module.FaithfullyFlat.finsupp` only requires a nonempty index type,
so transferring along `e.repr` covers the zero ring as well. The nontrivial-free-module
instance mentioned by earlier search reports is unnecessary. The zero-composite assumption
can remain unused because Mathlib's exactness equivalence holds for arbitrary pairs.
The unit route is unchanged. No shared interfaces or other existing modules changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
