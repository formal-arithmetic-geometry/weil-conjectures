## What changed

Proved all three theorems in `Sheaf.Paper.DerivedNormalizationArrows` without changing
any existing signature or definition. Added three proof-only imports:
`WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering`,
`Mathlib.CategoryTheory.Sites.Adjunction`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.

`normalizationCoefficientExactness` uses exactness of constants and the two scalar
restriction adjunctions, lifting restriction/coextension to sheaves.
`normalizationModuleRestrictExactness` uses the ordinary module adjunctions.
`normalizationPullbackMate_isIso` identifies the specified mate with the conjugate of
the identity coextension/direct-image square. The intermediate restriction square is
identified sectionwise by the adjunction triangle identity. Mathlib's iterated-mates
and conjugate-isomorphism theorems finish the proof. This avoids constructing separate
comma-colimit comparisons while retaining exactly the specified canonical arrow.

Updated the existing node's proof description to record these applications of existing
APIs. No new modules, declarations, definitions, hypotheses, or mathematical obligations.
The local unused-section-variable linter setting preserves the existing essentially-small
instance binders of `normalizationPullbackMate_isIso`; none is removed from its signature.

The retained module was checked against the current sources on 2026-10-19 and compiled
through `lcompile.py` in 6.2 seconds without diagnostics. An earlier compile-server
request received no answer; the required retry succeeded.
Searches retained from the interrupted attempt cover LeanFinder, Loogle, and grep;
reading the source APIs confirmed the adjunction and mates route. Import-direction checks
passed for both added source-library modules.

## Proved and sorry left

Closed 3 of 3 holes, all attached to
`def-weil-pbc-derived-normalization-arrows`:

- `CategoryTheory.normalizationCoefficientExactness`.
- `CategoryTheory.normalizationModuleRestrictExactness`.
- `CategoryTheory.normalizationPullbackMate_isIso`.

Added 0 holes. There are no remaining `sorry` declarations in the delivered module.
No split-offs or decomposition.

## No longer needed

None. No imports removed, no DAG dependencies pruned, and no modules withdrawn.
The definition node originally had no stated proof dependencies. All pre-existing public
imports remain; the three added proof-only imports supply APIs used in these proofs.
No separate inverse-image comma-colimit comparison lemma or total derived tensor model
is needed for this argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The retained sandbox's first two candidate proofs
were complete, but its final mate proof needed a sectionwise triangle identity and explicit
adjunction arguments. Replacing a large definitional conversion by unfolding only
`normalizationPullbackMate` made the final proof compile well within the per-file limit.
The exactness theorem holds for arbitrary coefficient homomorphisms; no flatness assumption
is introduced. The inverse-image comparison requires only the existing continuity
hypothesis, with no left-exactness assumption on inverse image.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
