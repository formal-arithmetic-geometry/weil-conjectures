## What changed

Completed `AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences` with its
signature unchanged. The first equivalence uses a pullback of sheaves, evaluation
of its universal property in types, local surjectivity of the original epi, and a
splitting of the pullback projection. The second equivalence uses Mathlib's sheaf
ulift-Yoneda equivalence in both directions. The affine assertion uses clause 1 of
`AlgebraicGeometry.Scheme.proetale_wContractible_projective`.

Added proof imports for sheaf limits, preservation of pullbacks, and pullbacks of
types. Updated the item's DAG proof and dependencies to match these APIs. All
existing public imports, statements, definitions and visibility are unchanged.
The argument applies equally to empty and disconnected objects and to the zero ring:
it makes no nonemptiness, connectedness or nonzero-ring assumption.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proetale_weakContractible_equivalences`
(node `det-pe-weak-contractible-equivalences`). One of one holes proved, zero holes
added, zero split-offs, zero holes remaining in the delivered module. The affine
clause still uses the existing stated theorem
`AlgebraicGeometry.Scheme.proetale_wContractible_projective`; its pre-existing hole
is outside this delivery.

Validation on 2026-10-19: the retained complete proof compiled again through
`lcompile.py` against the current server build with exit code 0 in 2.1 seconds,
without warnings. The current library module still has the original hole and the
same signature; the sandbox proof and node changes remain applicable. The delivery
dry run and its axiom/preflight checks are run through `deliver3.py` before pushing.

## No longer needed

Removed the proof import
`Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`: Mathlib already supplies
`(ProEt.topology X).Subcanonical`, while sheaf limits and sheafification are
available directly. Node `det-pe-topos-functoriality-site` is therefore no longer
a proof dependency of this item; its statement-dependency record stays unchanged.
Removed the redundant direct proof import `Mathlib.CategoryTheory.Yoneda` because
`Mathlib.AlgebraicGeometry.Sites.Proetale` already publicly imports the sheaf Yoneda
API. The Yoneda dependency `lem-galois-yoneda-hom-bijection` is still used.

Removed `def-weil-pbc-sites-and-cohomology` from the proof dependencies: its general
site-covering predicate is not used in the proof. Mathlib's sheaf-limits API carries
out the planned construction of the pullback sheaf. Its original public import
`Sheaf.CategoryTheory.SiteCoveringAxioms` is retained to preserve importer visibility.
No blueprint unit statement or proof step is bypassed; the planned Yoneda, pullback,
local-surjectivity, section-composition and affine steps are all realized.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's planned explicit construction and sheaf
verification of the pullback can be replaced by Mathlib's existing sheaf limits.
The broader site-properties theorem is unnecessary here because subcanonicality
is already an instance in Mathlib's pro-etale site module. No statement repair or
consumer adaptation is needed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
