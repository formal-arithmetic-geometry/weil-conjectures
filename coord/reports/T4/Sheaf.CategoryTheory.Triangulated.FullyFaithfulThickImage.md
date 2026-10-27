## What changed

Filled the proof of `CategoryTheory.Functor.essImage_thick_eq_triangEnvelope` in
`Sheaf.CategoryTheory.Triangulated.FullyFaithfulThickImage`. The statement, public imports,
and definitions are unchanged. Mathlib's triangulated essential-image instance supplies
steps 1–2 of the plan. For step 3, transport a retract to an image object, lift its
projector by fullness, verify idempotence by faithfulness, split it in the source, and
construct the image isomorphism with both inverse equations. For steps 4–5, pull the target
thick envelope back along the functor; its retract closure follows by mapping retracts,
and its triangulated structure is Mathlib's inverse-image instance. Envelope minimality
and the source generation hypothesis give one containment; thickness of the essential
image gives the reverse containment.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.essImage_thick_eq_triangEnvelope`
(node `lem-sfb-fully-faithful-thick-image`). One of one holes proved; zero holes added,
zero split off, and zero holes remain. The proof uses only Mathlib results and the stated
hypotheses, including idempotent completeness only for the source category.
The final `lcompile.py` check passed in 6.5 seconds without errors or warnings.

## No longer needed

None. Both original public imports remain needed. There were no proof imports to remove.
The existing DAG dependencies remain appropriate: triangulated-category interfaces and
the triangle-isomorphism lemma are used through Mathlib's triangulated essential-image
instance. No module or node is withdrawn. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Mathlib already implements the triangulated
essential-image and inverse-image portions of the plan, so they need no new lemmas.
The unit record still describes the older smooth-purity flat-model lemma; this historical
mismatch is already documented in the node's split report. The current blueprint under
`literature/blueprint/latest/` was read. The categorical statement and all five argument
steps are retained. Adjoining zero ensures the target seed is nonempty, including when
`G` is empty; no smallness or target idempotent-completeness assumption is used.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
