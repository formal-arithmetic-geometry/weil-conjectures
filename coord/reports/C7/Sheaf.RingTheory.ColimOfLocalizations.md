## What changed

Proved `RingTheory.colim_of_localizations` in
`lean/Sheaf/RingTheory/ColimOfLocalizations.lean`, with its exact existing signature.
All new helpers are private and fully proved. The private map and colimit
constructions are irreducible, with proved equations preventing expensive
repeated unfolding. No imports were added or removed.

Change record:
`coord/changes/C7-colim-of-localizations-private-construction.md`.
Preflight conservatively classifies the added local section commands as an
interface change. The record lists all five consumers and explains why the
private helper contexts and attributes leave their public interface identical.

The proof implements the five existing DAG steps: localization lifts construct the
embeddings and transition maps; localization extensionality proves uniqueness and
compatibility; transport of units proves transitivity; localization at the product
of two denominators gives a common upper bound; fraction representations and the
covering hypothesis prove coverage. A choice of stage representatives
constructs the underlying function out of any cocone. A common upper stage and
injectivity prove independence of representatives. Computing binary operations
at a common stage makes this function a ring homomorphism. The ring factorization
preserves scalars because its composite with any cocone leg does, giving the
commutative-algebra colimit as well.

Searched the library and Mathlib, including the source library's
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`: its diagrams use
fixed-ring localizations or subalgebras, rather than the specified varying
subalgebra/denominator pairs. The existing general localization lift and
filtered-colimit APIs suffice, without importing additional Sheaf declarations.
The existing DAG proof and dependencies still describe the implemented argument;
no route or node edit is necessary. The unit record has no realized statement or
steps to bypass.

Validation: the final complete module compiles through `lcompile.py` with no
errors or warnings in 14.0 seconds. Earlier delivery attempts hit the unchanged
60-second limit. The repair gives the ring-map construction an irreducible
private definition and a proved evaluation equation, and uses the DAG's direct
representative-gluing argument. This prevents repeated expansion of large local
colimit constructions. The delivery preflight independently checks axioms.
Edge cases covered by the construction include zero numerators, denominator one,
and repeated or equal subalgebras; no antisymmetry of the pair relation is assumed.
The index and scalar universes retain their original independent parameters.

## Proved and sorry left

Closed 1 hole: `RingTheory.colim_of_localizations`
(node `lem-kun-colim-of-localizations`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module, including its helpers.
This is a proof, not a decomposition.

## No longer needed

None. No existing imports, nodes, or modules were removed. Both declared proof
dependencies remain used through their Mathlib interfaces:
`def-weil-ring-localization-away` and `def-weil-pbc-category-colimit`.
The finite-type hypothesis is not required by the argument, but the existing
statement and binder are preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The current blueprint statement was read
at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/` under
`sk-prop-sf-kunneth-ordinary/lem-kun-colim-of-localizations.md`; the DAG's expanded
preorder and colimit formulation is the one proved. No existing definitions, public
signatures, consumers, or target statements changed. The first resumed static
preflight required a change record for local commands; that record is included.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
