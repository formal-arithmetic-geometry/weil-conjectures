## What changed

Kept all existing Brown-hypotheses constructions and proofs unchanged. Added the
strictly smaller `CategoryTheory.brownHypotheses_arbitraryField_compactness_witness`
obligation and assembled `CategoryTheory.brownHypotheses` from it using the existing Brown
criterion. The witness is explicitly marked `STATEMENT-DISPUTED`; no definition was
changed and all imports remain in use.

## Proved and sorry left

All declarations preceding `CategoryTheory.brownHypotheses` remain proved and unchanged.
The original `CategoryTheory.brownHypotheses` sorry is closed by the Brown criterion
using the compactness witness below. One new sorry remains:
`CategoryTheory.brownHypotheses_arbitraryField_compactness_witness`, node
`new-sfb-brown-arbitrary-field-compactness-witness`. This is a strict compactness clause,
not a restatement of the Brown bundle, and is marked `STATEMENT-DISPUTED` because the
unrestricted arbitrary-field compactness assertion is false. The net result is a
decomposition: one hole closed and one smaller disputed obligation added.

## No longer needed

None. Every existing import is still used by the proved declarations in this module, and
no proof dependency or node can be pruned from this delivery.

## Where the brief, the DAG or earlier work was wrong

The final theorem assembles the Brown bundle from the existing criterion and the new
compactness witness. The witness is the unresolved part: available geometric compactness
theorems require a `FiniteFieldDatum`, while these hypotheses give only an arbitrary field
with `CharP`; there is no construction of the required finite base field or
algebraic-closure structure. The module records the obstruction: for
`k = algebraicClosure(F₃)(t₁,t₂,…)`, `ell = 2`, `X = Spec k`, and the constant finite
coefficient ring, arbitrarily high Kummer cup classes contradict the compactness consequence
of the Brown bundle. Therefore the theorem cannot be proved without correcting its statement
(for example by restricting to the finite-field datum or adding a genuine Ext-bound
hypothesis). The supported theorem `brownHypotheses_of_finiteFieldDatum` is proved above
and does not imply this arbitrary-field claim.

## New nodes

`new-sfb-brown-arbitrary-field-compactness-witness` is the strictly smaller compactness obligation used by the final Brown assembly. It has a matching declaration in this module, a source and proof plan, and is explicitly marked `STATEMENT-DISPUTED` because the arbitrary-field Kummer obstruction applies.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
