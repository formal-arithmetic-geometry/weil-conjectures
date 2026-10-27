## What changed

Prove `SheafOfModules.exists_signedLinePullbackNormalized` with its statement unchanged.
Construct the tensor pullback comparison from the two adjunction units and the tensor
universal property. Prove it invertible when its right factor is a line, by restriction
to the given trivializing cover, the normalized tensor-restriction comparison and
pullback localization. Construct positive comparisons recursively and negative comparisons
using `finite_free_dual_pullback` followed by precomposition with the inverse positive
comparison. All helper constructions are explicit; no object is chosen from an unproved
mere-existence result. The chosen tensor-restriction comparison is uniquely determined
by its pure-tensor formula. Add proof imports for tensor restriction, pullback localization,
binary scalar/tensor coherence, local detection of isomorphisms, and slice finite-limit
instances. Update the node to describe this specialized proof.

## Proved and sorry left

Closed: `SheafOfModules.exists_signedLinePullbackNormalized`
(`lem-pur-normalized-signed-line-pullback-exists`), the item's one original hole.
Added holes: none. Remaining holes in delivered modules: none.

## No longer needed

The proof does not use `lem-weil-pbc-left-exact-site-inverse-image-tensor`
(`Sheaf.CategoryTheory.SiteInverseImageTensor`) or
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`
(`Sheaf.CategoryTheory.ModulePullbackTensorIso`). Their generic geometric-inverse-image
and scalar-extension presentation is unnecessary: the needed comparison is constructed
from the actual module adjunction and checked on rank-one charts.
No original public imports or declarations are removed. Neither unused dependency module
is withdrawn, since it has other consumers. No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The old node's steps discuss two coefficient rings and four lines, although this node
constructs the family for one ringed-site map and one line. The revised proof records
only the data this statement uses. The generic tensor theorem's equal-universe
ringed-topos interface does not directly give the mixed-universe module-adjunction
comparison appearing here; the explicit construction avoids that transport.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
