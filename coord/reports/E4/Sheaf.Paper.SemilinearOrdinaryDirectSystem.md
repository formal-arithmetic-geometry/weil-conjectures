## What changed

Repaired `Sheaf.Paper.SemilinearOrdinaryDirectSystem` internally. The geometric
core now records the local mate condition for two component maps at indices
n ≤ m. The previous core did not constrain horizontal maps and therefore did
not justify its Hom-data lemma.

Proved the repaired `ordinaryDirectSystem_homData_exists`: assemble compatible
component module-sheaf maps at each product-site object, prove naturality by
factoring a site arrow into a vertical and a horizontal arrow, transpose the
families in both directions, and prove both global inverse laws by evaluation.
The component formula is proved by evaluation and cancellation of the component
isomorphism. All new helpers are private and proved.

No additional module or import was added. The public main existence theorem
and `OrdinaryDirectSystem` retain their exact signatures and meaning. The only
direct importer is checked against the changed item and is not delivered as
an unchanged copy. Change record:
`coord/changes/E4-ordinary-direct-system-local-mates.md`.

## Proved and sorry left

The original item had two textual holes. The repaired local-to-global theorem
`WeilConjectures.SemilinearSections.ordinaryDirectSystem_homData_exists`
(node `lem-coef-ordinary-direct-system-hom-data`) is now completely proved.
Its old unrestricted statement was false; this is a documented interface repair
and a proof from the corrected local mate condition, not a proof of the false
unrestricted version.

One hole remains:
`WeilConjectures.SemilinearSections.ordinaryDirectSystem_core_exists`
(node `lem-coef-ordinary-direct-system-core`). Its conclusion now includes the
local transition mate condition required by its caller. Its docstring describes
the geometric construction and the local adjunct-square argument. This hole
is retained and strengthened, not counted as proved. No new sorry is added and
none is split into a new theorem or node.

`WeilConjectures.SemilinearSections.ordinaryDirectSystem_exists`
(node `lem-coef-ordinary-direct-system`) remains a complete proof combining the
core and Hom data, with its statement unchanged.

The final item compiles cleanly through lcompile.py in 55.0 seconds, under the
60-second file limit. Its sole direct importer,
`Sheaf.Paper.GeometricOrdinaryRealization`, compiles unchanged against the repair
in 22.5 seconds. The temporary importer copy was removed after this check.
All profiler/debug options were removed. The delivery tool performs the required
compile, axiom and sorry probes before pushing.

## No longer needed

No imports or modules are removed. For the Hom-data node, the proof no longer
needs `lem-coef-normalized-module-adjunction` as a proof dependency: the level
adjunctions are supplied and the core records their local transition law.
`lem-coef-ordinary-inverse-system` remains a statement dependency for P but is
not used as an existence theorem in the Hom-data proof. The actual local-to-global
proof uses only the core node and `def-coef-semilinear-system-models`.

No global pruning of these modules is claimed: the retained geometric core
still uses the normalized module adjunction and ordinary inverse-system data.
The sequence-site equivalence of `lem-pur-system-ringed-sequence-site` was read;
its extra category identification is unnecessary for the explicit morphism
assembly proof, but it remains in the retained geometric core's planned route.

## Where the brief, the DAG or earlier work was wrong

The old Hom-data lemma was false, not merely missing a proof. On a constant
nonzero ring tower over the one-object site, take identity inverse image and
identity level adjunctions. Zero every nonidentity horizontal transition of the
push system while keeping component modules and maps. This meets all old core
fields. Transposing the identity of a constant nonzero identity-transition
system would force identity component maps into a zero-transition system,
which violate the horizontal square.

The repair adds the source construction's missing local mate law to the core.
It concerns two arbitrary component maps and a single horizontal square; it
contains no global system Hom equivalence. All assembly and inverse-law work
is done in Lean in this delivery. The main geometric existence statement is
unchanged. Both changed auxiliary nodes have statement_change records, with
their sole citing node (the unchanged main statement) audited and its caller
updated. No unit route is bypassed; the unit record has no additional realized
step affected by this internal repair.

Searched through the required msearch services (Lean Finder, Loogle, grep),
read Mathlib's presheaf/sheaf module Hom constructors and adjunction naturality,
and searched the adopted source and Sheaf trees. No declaration directly proves
the generic strict-system construction. The existing sequence-site equivalence
was read before writing the direct product-site morphism assembly.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
