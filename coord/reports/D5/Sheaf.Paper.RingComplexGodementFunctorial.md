## What changed

Proved `AlgebraicGeometry.ringComplex_godement_functorial` in
`Sheaf.Paper.RingComplexGodementFunctorial`, preserving its statement and the concrete
Godement construction. The proof uses the proved private resolution-map construction
and equations in `RingComplexGodementModelMaps`, through a private `import all`.

Private helpers construct the structure-module map, evaluate the resolution maps on
global sections, prove compatibility with the coefficient ring maps, and form the
commutative square of augmented section complexes after restricting scalars. The
mapping-cone comparison for an additive functor then gives the map on the actual
mapping fibres. Its two projection formulas prove strict identity and composition;
the inverse-rotation sign calculation identifies the augmentation with the first
projection. The cochain equation gives compatibility with every differential.

Added proof-only Mathlib imports for the structure-module map and scalar restriction.
The existing public import and every existing signature are unchanged. Local
irreducibility attributes keep the chosen Godement model and resolution folded during
elaboration. No definition or statement repair, new public declaration, or new node.
The added scope commands and local attributes are documented in
`coord/changes/D5-ringComplex-godement-functorial-proof-scope.md`; the consumer scan
finds no downstream module requiring adaptation.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ringComplex_godement_functorial`
(node `lem-weil-pbc-ring-complex-godement-functorial`). Added zero holes.
There are no remaining `sorry`s in the delivered module, including its private helpers.
This is a proof, not a decomposition.

The construction and equations quantify over arbitrary rings, arbitrary ideal-extension
witnesses and all integer degrees. The zero terms of the single complex handle degrees
other than zero. Empty open complements, zero rings and the zero/unit ideals require
no additional hypothesis or nonemptiness assumption. Proof irrelevance handles all
supplied equalities of ideal extensions.

## No longer needed

Removed the redundant direct proof import `Sheaf.Paper.RingComplexCechData`: the
unchanged public construction import already publicly imports that interface.
No DAG dependency, node or module is pruned: all three declared dependencies remain
used. The cosimplicial formulas need not be reconstructed here; the already proved
resolution-map equations supply their consequences on sections.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The stated three-step route is followed.
Generic cone calculations are performed before specialization to module sheaves to
avoid unfolding the large chosen Godement model. The actual named private `resmap`,
`resmap_aug`, `resmap_id` and `resmap_comp` underlying the public model-map theorem
are used directly; no new choice of maps or unproved intermediate result is introduced.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
