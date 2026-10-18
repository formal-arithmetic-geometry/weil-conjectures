## What changed

Proved `HomogeneousLocalization.exists_away_scalarExtension_equiv` in
`Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`, with its original signature and
fraction formula unchanged. The two existing public imports are retained and used; no imports
were added.

The proof constructs the graded inclusion into the tensor algebra, its induced map on
homogeneous localizations, and the scalar extension of that algebra map. Private linear maps
send a homogeneous numerator to its fraction and multiply numerators by powers of the
denominator. Tensor induction proves the transition identity and represents every source
tensor over a common denominator. Surjectivity uses the base-change presentation of each
graded piece. Injectivity uses the localization zero criterion and
`DirectSum.toBaseChange_injective`, then moves a tensor to a later denominator where its
numerator vanishes. `AlgEquiv.ofBijective` completes the proof.

Added `coord/changes/K9-homogeneous-localization-proof-context.md` for the construction
section and its private local scalar-tower instances, as requested by the static context
checker. These instances are confined to the private construction section.

Updated the existing node's proof and proof origin to describe this argument. Its statement,
dependencies, and unit route are unchanged. The cited Stacks proofs of
`lemma-base-change-map-proj` (01N2) and `lemma-standard-open` (01M4) were read locally.

## Proved and sorry left

Closed 1 of 1 holes:
`HomogeneousLocalization.exists_away_scalarExtension_equiv`
(node `lem-nagata-homogeneous-localization-scalar-extension`).

Holes added: 0. Split off: 0. No `sorry` remains in the delivered module, and every private
helper is proved. No existing definition or statement was changed.

The complete proof compiled through `lcompile.py`. The final delivery gate also checks
compilation and axioms.

## No longer needed

No imports removed; no nodes or modules pruned. The sole stated dependency,
`def-nagata-homogeneous-localization-degree-zero`, is used throughout.

An inverse defined directly on quotient representatives, and the associated general
common-later-denominator equivalence, are unnecessary for this proof: the source tensor's
common-denominator presentation and the localization zero criterion establish bijectivity
directly. These were steps of the previous proof plan, not separate modules or nodes.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition was found. The DAG's planned explicit inverse is valid
but unnecessary. Its construction is replaced by a kernel argument using Mathlib's existing
graded-piece base-change injectivity. This requires neither flatness nor cancellation and
also handles zero rings and nilpotent or zero denominators. The positive-degree hypothesis
is retained exactly, although the proof works for degree zero as well.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
