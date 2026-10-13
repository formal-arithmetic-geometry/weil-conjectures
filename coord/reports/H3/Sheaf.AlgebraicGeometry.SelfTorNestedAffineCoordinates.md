## What changed

Replaced the sorry in `AlgebraicGeometry.exists_nested_affine_selfTor_coordinates`
with a complete Lean reduction. Its signature and all original public imports
are unchanged. Added a proof-only import of
`Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates` and a proof-only import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

The new module states only the affine coordinate construction and agreement
locally on pure wedges. The parent supplies the extension to arbitrary
sheafified exterior sections. Its proved private helper
`AlgebraicGeometry.exterior_over_component_ext` works with arbitrary module
sheaves and over-site maps: local surjectivity of the exterior sheafification
unit gives a covering image sieve; naturality transports the maps to members
of the sieve; span induction extends agreement from pure wedges to every
presheaf section; target separatedness first identifies the wedge values and
then descends equality through the sieve. Finally component extensionality
proves the required nested top-component equation.

Factoring this argument through abstract module maps also avoids repeatedly
unfolding the derived tensor construction. The final parent compiles without
warnings in 12.5 seconds. A scoped heartbeat option is explained in the source;
the 60-second wall-clock compilation limit has not been changed.

Updated the parent node's proof, proof_deps and proof_origin to match the Lean
argument. Added the new statement node and its Lean record. No definition,
existing statement, visibility, or target signature changed; no forced
adaptations or change records are needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_nested_affine_selfTor_coordinates`
(node `new-e1-self-tor-nested-affine-coordinates`). Its proof is complete from
the named local-wedge theorem, and the private general-section extension
helper is proved without sorry.

Added one hole:
`AlgebraicGeometry.exists_local_wedge_selfTor_coordinates`
(node `new-h3-self-tor-local-wedge-coordinates`, module
`Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates`). Its proof is exactly
`:= by sorry`. Its docstring contains the source and full proof in words,
including coordinate construction, denominator clearing, localization of
Koszul augmentation comparisons, and the degree-zero and empty cases.

This is a decomposition: one hole closed and one hole added, net zero.
It does not claim an axiom-free proof of the mathematical result. The new
statement does not assert equality on arbitrary exterior-sheaf sections or
component maps; that extension is the real Lean proof delivered in the parent.
There are no other sorries in the delivered files, none in definitions, and
none in private declarations.

## No longer needed

None. No original imports are removed and no original prerequisite is pruned
from the combined argument. The original parent proof dependencies
`lem-sc-affine-open-kernel-conormal-sections`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-exterior-sheaf-restrict-iso`, and
`new-r4-self-tor-conormal-comparison` now occur in the local-wedge node's proof
rather than as immediate dependencies of the parent. They are still needed.
The parent's only immediate proof dependency is the new local-wedge node.

An exploratory `Mathlib.CategoryTheory.Sites.Abelian` import was removed after
checking that the proof compiles without it; it was not an original import and
is not claimed as pruning.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan contains substantive unstated glue
between the available resolution/conormal lemmas and affine compatibility.
The existing sheafified-resolution theorem gives a quasi-isomorphism but not
the fixed-derived-tensor homology coordinate or its compatibility with
localization. The conormal sections theorem gives a unit-normalized section
equivalence, not an exterior sheaf coordinate with localization compatibility.
These remaining constructions are explicitly retained in the local-wedge
statement, rather than silently assumed from stronger conclusions of those
lemmas.

The Stacks pages for 09PQ, 01R3, and 06YH were read. Tag 09PQ establishes
resolution-independent Tor products, while 06YH defines the derived tensor
and refers to its K-flat comparison construction; neither page directly states
the new affine-chart theorem. The new proof_origin is marked as an agent
expansion of the parent plan, with the same sources. In particular, arbitrary
K-flat resolutions need not admit a direct comparison map; comparisons of the
fixed derived tensor are made through a common K-flat refinement.

The unit record `sk-thm-picard-duality` has no realized node for this descendant,
and its statement and route are untouched. Blueprint searches for `self Tor`
and `conormal` found no duplicate of the local-wedge theorem. Searches in the
Lean roots found no shorter existing theorem. Logged LeanFinder searches gave
only localization and flatness facts, not the required comparison. LeanSearch
returned Internal Server Error and is recorded as unavailable, not no match.
The focused Mathlib grep for Tor/conormal localization in AlgebraicGeometry
found no match.

The new theorem was checked on n=0 (empty wedge and quotient unit), empty
opens (the pointwise hypothesis is vacuous), the identity immersion/zero
ideal (positive exterior degree of the zero conormal is zero), the empty
closed scheme/unit ideal (all module sheaves on it are zero), and nonregular
ideals (the comparison need not be an isomorphism; only coordinate changes
are isomorphisms). No regularity, finiteness, or nonemptiness assumptions
were added.

## New nodes

`new-h3-self-tor-local-wedge-coordinates`, in
`dag/nodes/sec-picard-framework/`, states existence of the affine coordinates
with local agreement only on pure wedges on subopens of nested affine charts.
Its module is `Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates` and its
one public theorem is `AlgebraicGeometry.exists_local_wedge_selfTor_coordinates`.
It inherits the parent's chapter and unit. It retains all four original proof
dependencies and records the logged searches. This isolates the remaining
local Koszul calculation; the parent proves passage from wedges to general
sheafified sections and to the asserted component equality.


## Second reading by H3

1. **Statements and interfaces.** I compared both delivered Lean modules against the repository versions. The existing public theorem `AlgebraicGeometry.exists_nested_affine_selfTor_coordinates` has the same signature byte for byte; its definitions, hypotheses, affine-open quantifiers, and terminal component equality are unchanged. The new local-wedge theorem has the node's stated weaker conclusion: agreement is only local and only on pure wedges. No target statement or existing visibility changed. Verdict: pass.

2. **Proof and trust basis.** Both modules compile with `lcompile.py --all`. The parent proof contains no `sorry`; the only remaining `sorry` is the explicitly named `AlgebraicGeometry.exists_local_wedge_selfTor_coordinates`, exactly as listed with its node. There are no axioms, unsafe/opaque/extern declarations, or hollow definitions. The private extension helper uses sheafification local surjectivity, separatedness, and span induction, and the parent reduces the target to the local-wedge theorem without altering its statement. Verdict: pass.

3. **Split statement and searches.** I read the new node and its docstring proof. It is strictly smaller than the parent: it supplies only pure-wedge local agreement, while the parent proves extension to arbitrary sheaf sections and component equality. Its four proof dependencies are recorded and match the local-wedge docstring. The recorded LeanFinder, grep, and unavailable LeanSearch searches were checked; no duplicate declaration was found in the Lean roots. Edge cases named in the report (degree zero, empty opens, zero ideal/quotient, and nonregular ideals) remain covered. Verdict: pass.

4. **Pruning and imports.** The original public imports of the parent are unchanged. The two added imports are plain proof-only imports: `SelfTorLocalWedgeCoordinates` supplies the split theorem and `Presheaf.Sheafification` supplies the local-surjectivity API. The local-wedge module's public imports are exactly those needed by its statement and recorded dependencies. The parent node's immediate `proof_deps` is the local-wedge node, while that node retains the four lower dependencies used by its proof. No stale proof dependency or unit route was removed. Verdict: pass.

5. **DAG and unit consistency.** The parent and split node Lean records match the declarations and files, and their `proof`, `proof_deps`, and `proof_origin` describe the implemented route. The split node keeps chapter `sec-picard-framework` and unit `sk-thm-picard-duality`; no realized unit statement or route was changed. Verdict: pass.

I changed only this second-reading report section. No Lean source, declaration signature, node statement, or import was repaired.
