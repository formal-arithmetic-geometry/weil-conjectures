## What changed

Filled `WeilConjectures.PurStrictScalar.strictScalarOpenUnit` in
`Sheaf.Paper.StrictScalarOpenUnit`, keeping its statement and the published maps unchanged.
Added proved private helpers for the ordinary pullback square, its geometric mate,
normalized derived mate compatibility, and the scalar/open unit calculation.
Proof imports expose existing private exact-localization coherence lemmas; no shared
module or public definition is changed. Updated the item's DAG proof to this route.
The clean final file passed the remote single-file compiler without warnings in
15.6 seconds. Delivery runs the required preflight and proof probes.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurStrictScalar.strictScalarOpenUnit`
(node `lem-pur-strict-scalar-open-unit`).
Added zero holes and zero split-off statements. No `sorry` remains in the item.
The proof uses existing, named adjunction and exact-localization declarations.

## No longer needed

The planned dependency `lem-sf-open-tensor-normalization` and its module
`Sheaf.SixFunctors.OpenTensorNormalization` are unnecessary for this proof and
are not imported. Its tensor models, support assertions and simultaneous system
comparisons are avoided: the ordinary coefficient-restriction square already
specifies the required open mate, and scalar Hom-equivalence injectivity transfers
its unit equation. This prunes that dependency from this node's route; it makes
no assertion about its other consumers. No original public import is removed.
No other declared dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan suggested computing elementary tensors and identifying
several descended geometric models. Those constructions are unnecessary here.
The existing inverse-mate definitions and normalized derived-square counit lemma
supply a direct categorical proof on whole strict towers. The statement needs
no repair. The argument applies equally to identity and empty open immersions,
zero objects and the identity coefficient extension; it never cancels the open
unit or assumes a support or compactness condition.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
