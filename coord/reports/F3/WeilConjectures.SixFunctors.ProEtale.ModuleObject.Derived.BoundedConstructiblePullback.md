## What changed

Restored the assigned module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback`
from its quarantine archive, byte for byte, to its original library path. The rework row
records removal after a cluster restore. Both public imports, both identity-isomorphism
constructions, and all coherence, cocycle, transport and commutation proofs are preserved.
The quarantined source remains intact.

Single-file compilation through lcompile.py succeeded without errors or warnings in
11.9 seconds. The definitions restrict the ambient identity and composition isomorphisms
through the fully faithful inclusion; the coherence proofs reduce to the existing ambient
coherence laws. The generic transport proofs use naturality and the supplied unit and
associativity hypotheses, and handle equality transports by substitution.

Change record: `coord/changes/F3-bounded-constructible-pullback-restoration.md`.

## Proved and sorry left

This is a zero-hole rework restoration. The archived item has zero sorries, the restored
item has zero sorries, zero holes are closed, and zero holes are added or split off.
All existing proofs are retained; no newly proved theorem is claimed.

In particular, the retained proofs cover `boundedConstructibleUpperStarId_hom_app_hom`,
`boundedConstructibleUpperStarComp_hom_app_hom`,
`boundedConstructibleUpperStarComp_assoc_app`,
`boundedConstructibleUpperStarComp_id_left_app`,
`boundedConstructibleUpperStarComp_id_right_app`,
`boundedConstructibleUpperStarComp_cocycle_aux`,
`boundedConstructibleUpperStarComp_id_aux`,
`boundedConstructibleUpperStarComp_id_right_aux`, and the `CategoryTheory.PullbackFamily`
transport, equality-transport, and commutation lemmas.

## No longer needed

None. No imports, declarations, nodes or modules are removed. Both archived public imports
are needed for the restricted functors and their ambient coherence API. Quarantined parents
and the eight live downstream modules retain their dependencies.

## Where the brief, the DAG or earlier work was wrong

The assigned source is absent from lean/, but coord/rework.tsv identifies its quarantine
archive. Its assignment is restoration rather than filling a sorry. The only node found
by the module-name substring is `lem-weil-pbc-pullback-preserves-bounded-constructible`;
its actual Lean attachment is `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`, not
this source module. Its statement, proof route, dependencies and Lean attachment remain
unchanged. No node is repointed to a different mathematical statement.

Mathlib searches were run through msearch.py: Loogle for
`Functor.FullyFaithful.preimageIso` returned an unknown-identifier result; Lean Finder for
restriction of pullback composition coherence returned generic full-subcategory composition
and Over pullback results, not a replacement for the archived API; grep for
`preimageIso|whiskeringRight_preimage_app` confirmed the standard fully faithful restriction
pattern. The existing complete source proof is therefore retained.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
