## What changed

Proved `AlgebraicGeometry.koszulOpenHom_chain_class_naturality` in
`Sheaf.AlgebraicGeometry.KoszulOpenHomChainClassNaturality`, preserving its statement,
universes, visibility, and public import. Added only private, proved local helpers:
`homPostcomp`, `homChainClass_postcomp`, `stageClass_postcomp`,
`stageComparison_postcomp`, and `cechDerivedComparison_naturality`.

The proof constructs postcomposition on the module Hom complex, checks its action on
cycles and homology, transposes through the affine adjunction, and transports through
the specified stage isomorphisms. Naturality of the localization cocone follows by
cancelling the denominator on each principal intersection, with restrictions and the
integer sign respected. The existing resolution characterization determines the
chosen Cech comparison as the component of an explicitly constructed natural roof.
Applying Q and H^0 combines these equalities.

Updated the node's proof, proof dependencies, and proof origin to record the actual
argument, including direct use of `def-sc-principal-open-alternating-total`.
No new module, statement, definition interface, or public import was added.
Sources read: Stacks Tags 08D1, 08DD, and 08D2. Local compilation is clean.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.koszulOpenHom_chain_class_naturality`
(node `lem-sc-koszul-open-hom-chain-class-naturality`).
There are no sorries left in the delivered module and no holes added or split off.
All private helper theorems are proved; `homPostcomp` is a real chain-map construction.
This is a proof from existing dependencies, not a new decomposition. In particular,
the resolution argument uses the existing
`AlgebraicGeometry.principalCechAugmentation_quasiIso`; its remaining proof obligation
belongs to the existing node `def-sc-principal-open-alternating-total` and is untouched.

## No longer needed

No imports removed and no dependency modules or DAG nodes pruned. Both original
proof dependencies remain needed for their definitions. The quasi-coherent
`koszulOpenHom_chain_representatives` theorem is not used; only the actual chain-class,
transpose, and stage-class constructions from its module are used. Consequently this
proof requires neither quasi-coherence nor a choice of chain representatives for
arbitrary derived arrows. This does not prune that module because its definitions
remain necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement errors found. The plan was correct, but its second step
needed the explicit coefficient action and K-injective-resolution characterization
from `def-sc-principal-open-alternating-total`, which is now named in proof_deps.
The route of the unit is unchanged; its realized table has no designated node or step
that this argument bypasses.

Searches ran through msearch: LeanFinder for Hom-class postcomposition naturality,
Loogle for `Adjunction.homEquiv_naturality_right`, and grep for Hom-complex
postcomposition and cycles/homology map compatibility. These returned generic
homology and adjunction ingredients, which the proof uses, rather than a duplicate
Koszul-class theorem. Repository searches likewise found no existing full theorem.
The proof is uniform for r=0, zero rings, zero coefficient maps, and zero complexes:
no nonempty-cover, nonzero-ring, or quasi-coherence hypothesis is introduced.

## Second reading by J1

1. Compared the delivered Lean module with the repository version. The theorem statement, universes, visibility, and public import are unchanged; only the proof and private helpers were added.

2. Compiled the module with `lcompile.py`; it is clean. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. The helper `homPostcomp` is an explicit chain-map construction, and the proof uses only existing approved dependencies.

3. Checked the proof route and searched the repository and Mathlib-oriented search results for duplicates. The private helper results are genuine intermediate facts, and the target statement is unchanged and fully proved. The edge cases mentioned in the report introduce no extra hypotheses.

4. Checked pruning and imports. The public import remains required for the definitions used by the target; no imported module or node can be removed. The quasi-coherent representative theorem is unused in the proof, but its module still supplies required definitions, so it is not pruned.

5. Checked the DAG node against the Lean proof. The proof steps, `proof_deps`, and `proof_origin` record the actual Hom-complex, localized cocone, and K-injective-resolution route, including `def-sc-principal-open-alternating-total`; the unit route is preserved.

Changed: added this second-reading record only; no Lean statements, definitions, imports, or additional holes were changed.
