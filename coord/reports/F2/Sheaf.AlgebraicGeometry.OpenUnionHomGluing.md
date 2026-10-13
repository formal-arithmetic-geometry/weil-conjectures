## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_open_union_hom` with a complete
Lean proof from `scheme_derived_hom_gluing` and a strictly smaller restriction-transport
statement. The original public signature and docstring are unchanged. The proof constructs
the inverse-image opens, proves their cover equation, transports the local maps using
full-faithful preimages, applies covering Hom gluing, and proves both requested restriction
equations by naturality and cancellation. The private, fully proved generic helper
`transported_morphism_eq` handles transport of a restriction equation.

Added `Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport`, containing one theorem and
one sorry, for the first step of the existing DAG plan. This statement constructs no glued
morphism and invokes no Hom exactness assertion. Updated the item's proof dependencies and
proof narrative to match the Lean reduction. No definition or existing statement changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.exists_open_union_hom`
(node `lem-sc-open-union-hom-gluing`); no sorry remains in the item.
Added exactly one hole: `AlgebraicGeometry.Scheme.open_union_restriction_transport`
(node `lem-sc-open-union-restriction-transport`). This is a decomposition, not a net
hole reduction: one upper hole closed and one strictly smaller transport hole added.
The final gluing argument, cover proof, and generic cancellation helper are proved.
Both modules compiled locally without warnings; deliver3.py runs the final static and
axiom probes.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.DerivedOpenLocalization` and
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction` from the item: its proof now
uses the transport theorem to obtain the required localizations. These two nodes remain
proof dependencies of the new transport node; they are not claimed globally pruned.
Kept `DerivedOpenRestrictionMaps` as a public statement import and
`SchemeDerivedHomGluing` as a private proof import. No module is established to be removed
from the targets' import closure, and no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's first step contains substantial canonical
restriction-coherence work; the existing named dependencies supply localization sizes but
do not state that overlap comparison. This missing interface is now the new node.
The covering Hom theorem is already proved and is used unchanged. Mathlib searches found
underived comparisons but no exact derived diagram theorem; LeanSearch returned an
Internal Server Error and is recorded as unavailable.

The new theorem was checked conceptually on empty W or V, disjoint W and V, an empty
union, W=V, and W contained in V: inverse-image scheme identifications and the comparison
triangles hold in each case. No nonemptiness, compactness, or boundedness is needed.
The proof source read was Stacks Tag 08BW; underived comparison signatures in
Mathlib.AlgebraicGeometry.Modules.Sheaf and the proved factorization-law argument in
SchemeDerivedHomRestrictionTransport were also read. The new lemma is an agent-written
expansion of the transport in the original plan. Witnesses are eliminated only inside
proofs; no definition chooses arbitrary data from the remaining hole.

## New nodes

`lem-sc-open-union-restriction-transport` in
`dag/nodes/sec-picard-framework/lem-sc-open-union-restriction-transport.json`:
canonical derived restriction comparisons and compatibility on the inverse-image opens
of the union. Its module is `Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport`.
It is strictly smaller than Hom gluing: it gives no morphism on the union. The item
combines it with the existing covering gluing theorem in a complete Lean proof.
Blueprint searches for "open union" and "canonical restriction" found no matching
statement; the nearest original ancestor follows the item's existing
`blueprint.from.node = lem-sc-finite-duality`. No change record is needed.

## Second reading by F2

1. Compared both delivered modules with the repository: the sole existing public
   declaration, `AlgebraicGeometry.Scheme.exists_open_union_hom`, has a byte-for-byte
   identical signature and docstring. Only its proof, private helper, options and
   private imports changed. No existing definition or target changed; no change
   record is required. Verdict: pass.
2. Independently compiled both modules in import order without warnings. The item
   contains no sorry; the new module contains exactly the reported named transport
   theorem with `:= by sorry`. No forbidden declaration or hollow definition occurs.
   The generic helper is a naturality/map-preimage/cancellation proof; the main
   proof uses the transport witnesses only inside a proposition proof, never to
   define data. Axiom probes are included in the final delivery checks. Verdict:
   pass subject to those final checks; the result still depends on sorryAx.
3. Read the transport statement, its node and its complete docstring argument.
   Its canonical open-scheme identifications, exact derived equivalences and
   overlap comparison are valid also for empty W, empty V, disjoint opens, empty
   union, W=V and nested opens. The witnesses can be chosen compatibly by deriving
   the underived restriction diagram. It supplies no glued morphism and is
   strictly smaller than the original item. Independent leanfinder, loogle and
   grep searches used different queries (recorded in searches.jsonl); rg in both
   library roots found SchemeIsoDerivedEquivalence and
   SchemeIsoDerivedRestrictionSquare. These provide components but not the
   relative-open overlap pasting identity. No duplicate or short complete proof
   was found. Read Stacks Tag 08BW, confirming the covering Hom exactness step.
   Verdict: pass; the transport hole remains a substantial coherence task.
4. Checked the top-down reduction: preimage_sup and ι_preimage_self give the cover,
   scheme_derived_hom_gluing gives alpha, and transported_morphism_eq converts its
   two restrictions using qW/qV naturality, followed by kW/kV cancellation.
   Existing public imports are needed for signatures; added proof imports are
   private. The two removed original dependencies are explicitly listed under
   No longer needed, and now belong to the transport node. The unit
   sk-thm-picard-duality has empty realized fields in the repository; this work
   changes no unit record and bypasses no unit step. No global pruning or net
   hole reduction is claimed. Verdict: pass.
5. Compared the node signatures with the Lean text verbatim, and checked the
   existing node's only changed fields are proof, proof_deps and proof_origin.
   Its two dependencies are exactly the transport and covering-gluing theorems.
   The new node includes source, complete steps, searches, creation metadata,
   blueprint ancestry, unit/chapter, and Lean record. Verdict: pass after the
   import repair below.

Second reading changed: added private imports of DerivedOpenLocalization and
OpenDerivedLocalizationAdjunction to OpenUnionRestrictionTransport, matching its
DAG proof dependencies and making those planned prerequisites available to its
next prover; appended this independent review. No mathematical proof or statement
was rewritten. The delivery is a one-for-one decomposition (net zero holes),
with no module established globally pruned.
