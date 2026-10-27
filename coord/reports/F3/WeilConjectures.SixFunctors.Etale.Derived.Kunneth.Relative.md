## What changed

Filled `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
in `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` from the existing
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap` (node `lem-kun-0f1n`, Stacks 0F1N).
The two pullback squares are obtained by flipping the standard fibre-product squares.
Tensor symmetry puts the inputs in the order required by tensor base change; the
pullback composition comparison identifies the auxiliary factor after pullback;
a final tensor symmetry gives the stated external product. Added its proof-only
import `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`.

All current signatures, declaration attributes, docstrings, definitions and public
imports are preserved. The proof was already present in the source snapshot read
at session start; the shared repository refreshed during this session and restored
this theorem to a hole. The packet is based on the refreshed source and restores
that existing argument. It is a substantive proof change against the current source.

Searches through the prescribed msearch wrapper: LeanFinder for relative Kunneth,
Loogle for externalProduct, grep for compact-support base change/composition, and
LeanSearch for proper base change with Grothendieck abelian coefficients. The
Mathlib hits were generic external products or unrelated compact-support results;
none replaces the existing scheme-etale tensor-base-change theorem.

## Proved and sorry left

Closed one of the current module's two holes:
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
(nodes `sk-lem-sf-kunneth-star`, `lem-trf-ordinary-kunneth`). This is proved from an
existing declared dependency; that dependency's own proof remains upstream work.

One existing hole remains unchanged:
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
(node `sk-thm-sf-kunneth-relative`). It is for an arbitrary concrete monoidal
Grothendieck abelian coefficient category with finite finitely generated objects.
The finite-ring four-step assembly already in this module cannot discharge it:
composition and compact-support base change are available for `ModuleCat` of a
finite ring, while the generic assembly additionally requires pullback-flatness
and forgetful-functor compatibility assumptions absent from this theorem.

Holes added: zero. Split-off statements: zero. No definitions are changed.

## No longer needed

No existing imports removed and no modules withdrawn. The new import is used by
`isIso_tensorBaseChangeMap`. For the ordinary etale theorem, no separate local
coefficient filtration, flat-model construction, or site-comparison argument is
needed here: the general finite-ring result `lem-kun-0f1n` already states the needed
tensor-base-change isomorphism. Dependencies needed inside that cited result or
by the broader pro-etale blueprint statement remain needed; this packet makes
no global withdrawal claim.

## Where the brief, the DAG or earlier work was wrong

At session start the source module had only the generic relative-product hole;
during work a shared upstream refresh restored the ordinary-product hole and
removed its proof import. The final packet uses the refreshed module. Its two
holes are the denominator reported above. The node records for these sketch
statements currently have no lean attachment, despite the blueprint labels in
the source docstrings; this proof uses the already attached `lem-kun-0f1n`.
The broad coefficient-stage blueprint assertions are not identified with this
single etale existence-of-an-isomorphism theorem.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
