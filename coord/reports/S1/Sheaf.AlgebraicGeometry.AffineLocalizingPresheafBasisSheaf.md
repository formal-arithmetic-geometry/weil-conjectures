## What changed

Proved AlgebraicGeometry.Scheme.Modules.isSheaf_affineBasis_of_localizing with its
signature unchanged. Added the proof-only import
Sheaf.AlgebraicGeometry.LocalizingPrincipalCoverGluing and its fully proved
isSheafFor_principalCover_of_localizing. The latter compares localizations with
Mathlib's associated module sheaf on Spec Gamma(T,W), proves naturality for
both overlap restrictions, and transfers unique gluing. The item explicitly
constructs principal refinements, proves separatedness and the generated-sieve
covering condition, and applies isSheafFor_subsieve_aux. Updated the item's DAG
proof and dependencies to match this code. No statement or definition changed.

Validation: both modules compile together without warnings using lcompile.py.
Checked arbitrary schemes (no separatedness assumption), arbitrary modules,
infinite covers, empty covers and the zero ring. The proof uses no nonempty or
finite-index assumption: the empty principal cover implies the zero ring by
the span criterion, and unique gluing in the associated sheaf applies unchanged.
The unit's realized statement and steps are empty; its coherence route is kept.

## Proved and sorry left

Closed the item's sole hole:
AlgebraicGeometry.Scheme.Modules.isSheaf_affineBasis_of_localizing
(lem-pc-affine-localizing-presheaf-basis-sheaf).
Also fully proved the new theorem
AlgebraicGeometry.Scheme.Modules.isSheafFor_principalCover_of_localizing
(lem-pc-localizing-principal-cover-gluing).
No sorry remains in either delivered module; no holes were added. This is a
proof, not a decomposition. The dependency proofs use only Mathlib.

## No longer needed

No existing imports were removed and no planned mathematical node was
bypassed. The second reading removed the redundant proof-only import
Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing from the new module;
StructureSheaf already imports it through LocalPredicate. No module was pruned. The original lem-weil-pbc-spec-module-tilde-sections dependency is
now used through the fully proved principal-gluing node; the concrete Lean
implementation uses Mathlib.AlgebraicGeometry.StructureSheaf directly.
No affine-intersection or separate basis-extension theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The original plan marked affine-sieve refinement elementary, but the Lean
implementation requires a substantive refinement and separatedness argument;
these are now fully proved, with the gluing extension supplied by Mathlib.
blueprint_refs.py ancestor prints None because these recently created stage-3
nodes have module names in created.item. The new node follows the explicit
existing blueprint.from chain to lem-pc-finite-support-hi instead.
LeanSearch returned Internal Server Error; recorded as unavailable, not as a
negative mathematical search result. Loogle, LeanFinder and grep were run.

## New nodes

lem-pc-localizing-principal-cover-gluing, in
lean/Sheaf/AlgebraicGeometry/LocalizingPrincipalCoverGluing.lean, is the strictly
local principal-cover portion of the argument. It is fully proved; it assumes
localization only on one fixed affine open and makes no claim about the induced
affine-site topology or arbitrary covering sieves. Its source is Tag 01HV,
lemma-spec-sheaves (2),(4),(5). No change records or forced adaptations.


## Second reading by S1

1. Compared the delivered item with the repository by diff. The existing
   theorem signature is byte for byte unchanged, as is its docstring. Only
   private proved helpers, its proof, and one proof-only import were added.
   No definitions or target statements changed; no change record is needed.
2. Compiled both modules in import order with lcompile.py, without errors or
   warnings. Scanned both for sorry, axioms, unsafe/opaque declarations and
   implementation overrides: none. A scratch #print axioms check of both public
   theorems reports exactly propext, Classical.choice and Quot.sound. All
   constructed data comes from proved localization and gluing theorems.
3. There are no split-off holes. Read the new principal-cover theorem and its
   localization comparison, including naturality for both overlap maps and
   the global-section uniqueness argument. The local hypothesis at one W is
   sufficient; no finite cover, nonzero ring, separated scheme or nonempty
   cover assumption enters. In particular an empty cover of W makes Gamma(W)
   the zero ring, and a module over it is zero. Searches with a different
   LeanFinder query (unique amalgamation of localized modules), Loogle and
   grep, plus repository searches, found localization and gluing tools but
   no existing theorem providing this principal-cover assertion. Loogle's
   query reported an unknown identifier, so that query is inconclusive.
4. Read the refinement and separatedness arguments from the top down. The
   extension uses Mathlib's subsieve lemma, with separatedness on all covering
   pullbacks; it needs no affine-intersection hypothesis. Mathlib provides the
   associated sheaf and localization universal properties, but not this full
   module-presheaf criterion. Removed one redundant proof-only import from the
   new module and recompiled both successfully. The original mathematical
   dependency remains through the new principal-cover node; the unit record
   sk-thm-picard-coherence has empty realized statement/step lists, and its
   coherence route is preserved. No existing module is pruned.
5. Read both node records and the old dependency node. Existing JSON changes
   are confined to proof, proof_deps and proof_origin. The proof_deps union
   matches the written steps. The old associated-sheaf dependency is a Mathlib
   leaf; StructureSheaf is the underlying construction used instead of its
   tilde wrapper. The new node has its source, searches, blueprint ancestry,
   chapter/unit, creation record, and matching Lean signature. Its assertion
   is strictly the principal-cover part, and it is fully proved.

Changed only the redundant UniqueGluing import and this report. Verdict: pass;
one original hole closed, zero holes added, no statement or definition change.
