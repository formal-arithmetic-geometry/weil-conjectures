## What changed

Constructed `RingedTensorSquare.derivedComparison_existsUnique` by localization on
flat K-flat objects, using the equivalence already supplied by tensor descent.
Proved a generic tensor/mate calculation and the simultaneous naturality equation.
The final coherence theorem is reduced to the tensor calculation on two flat K-flat
representatives; extension to arbitrary derived objects is proved by injectivity
of two-variable restriction. All existing signatures and definitions are unchanged.

Added `Sheaf.Paper.RingedSquareTensorCompatibility` for that representative calculation.
Added proof-only imports for K-flat preservation and the tensor-right flatness bridge.
They are needed because the construction theorem has no tensor models among its
parameters, so the preservation clause of the canonical derived tensor theorem
cannot be instantiated there.
Updated the parent DAG proof to describe the actual construction and reduction.

Validation: `lcompile.py --all` compiled both delivered modules without warnings
(8.6 s and 24.3 s). All eight original public signatures and all six original
definition bodies match the original text.
The overlaid DAG has no dependency cycle, and proof dependencies equal the union
of the recorded uses.

## Proved and sorry left

Original holes closed: `SheafOfModules.RingedTensorSquare.derivedComparison_existsUnique`
and `SheafOfModules.ringedExchangeTensorCoherence`.
The first is proved from existing declarations. The second is a decomposition:
its mate argument, descent extension, and naturality are complete, while the
representative tensor calculation remains open below it.

One hole added, and the only explicit sorry in the delivery:
`SheafOfModules.ringedSquareTensorCompatibility`, node
`lem-weil-pbc-ringed-square-tensor-compatibility`.
It still needs the generalized-section/pure-tensor verification of the ordinary
module square, its total-complex equality, and substitution of the four canonical
derived tensor representative equations. The proof in words and exact signature
are in the new module, including the exact pre/postcomposition that reduces
derived transport to the ordinary total-complex square. There is no hole in any definition or private helper.
Thus this delivery proves one original obligation and decomposes the other,
with two original holes closed and one new hole added (net one).

## No longer needed

The direct proof-dependency import `Sheaf.Algebra.Homology.KFlatResolution` is removed:
individual resolutions are unnecessary because tensor descent already gives the
resolving localization. Accordingly the direct dependency and old tool-use entry
`lem-pc-kflat-resolution` are removed from the parent node. Resolution theory remains
transitively needed by descent; this does not claim to prune its whole module.

Removed the redundant direct proof imports
`Sheaf.CategoryTheory.ModulePullbackTensorIso`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`. The presentation
already exposes the canonical comparison, and K-flat predicate conversion is available
through its public dependencies. None of these removals claims a whole module is
absent from the transitive target closure.

The old direct dependency on the ordinary module tensor theorem moves to the new
representative lemma. The parent uses the new lemma rather than repeating that
calculation. The canonical derived tensor theorem likewise remains a statement
dependency of the parent and a proof dependency of the representative lemma.
The unit's own statements and realized proof steps are retained.

## Where the brief, the DAG or earlier work was wrong

The five-step mathematical plan is retained. Step 2 requires an explicit square
compatibility calculation; the available edge tensor theorem does not itself
state it. The new statement records exactly its representative part, rather than
repackaging projection/exchange coherence. Empty and zero modules, identity edges,
nonflat structural ring maps, and unbounded complexes introduce no additional
hypotheses in that calculation. Arbitrary specified representative identifications
are allowed: the intermediate corner identifications cancel, and naturality handles
the source and target identifications.

A broader DAG entry, `lem-sfb-ringed-derived-monoidal-comparisons`, was inspected,
but its recorded Lean source file was absent from this checkout and is not used.
The first dry run identified ambient generic `variable` commands as an interface
change. Their binders now occur only in private theorem signatures; the interface
checker reports no change to the existing module.
The prescribed compile server intermittently returned no answer; successful retries
provided actual compiler diagnostics. No launcher or project scripts were changed.

## New nodes

`lem-weil-pbc-ringed-square-tensor-compatibility` is the representative-only part of
Step 2, in `Sheaf.Paper.RingedSquareTensorCompatibility`. It has no projection map,
exchange map, mate, naturality conclusion, or assertion on arbitrary derived inputs.
The parent proves the missing extension and categorical argument itself. Its source
is Stacks Tags 07A4, 0D6D, and the verification omitted at 0E48; the node records the
actual Mathlib searches. No definition or statement repair, change record, or forced
adaptation is needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
