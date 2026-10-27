## What changed

Proved `WeilConjectures.normalizedRationalEvaluation_naturality` in
`Sheaf.Paper.NormalizedRationalEvaluationNaturality`, keeping its statement and public import.
Private proved helpers derive ambient counit naturality, transport inverse transposition
through the actual completion unit, and establish integral evaluation naturality. The
rational proof uses the defining object and pure-tensor normalizations of tensor, internal
Hom and inverse transpose, followed by induction in both localized arrows.
The integral helpers reproduce the relevant argument already present privately in the
parent `CompletedTensorHomTranspose`; importing that parent would make an import cycle.
The node proof now records these three parts of the argument. The localization
calculation is a private lemma over an arbitrary linear category, specialized to
the given coefficient category to avoid unfolding its large definitions.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.normalizedRationalEvaluation_naturality`
(node `lem-coef-normalized-rational-evaluation-naturality`).
No holes remain in the item; no holes or split statements were added.
The proof uses the existing stated normalization theorems, whose own proofs remain
separate project obligations. The required single-file server compile passed without
errors or warnings (57.6 seconds).

## No longer needed

None. The existing public import is needed for the statement and the proof uses all
four recorded dependency nodes. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The partial closed record supplies only parameter naturality; pair naturality cannot
be projected directly from it. The planned normalization argument resolves this using
the ambient closed record and the actual completion unit. No statement repair is needed.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
