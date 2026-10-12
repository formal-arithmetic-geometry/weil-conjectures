## What changed

Added the proof of `AlgebraicGeometry.Etale.sourceStageSectionsIso_naturality` in
`SourceStageSectionsNaturality.lean`. The degreewise chain-map argument is complete and
uses naturality of `objectSections_naturality`, followed by cancellation of the
composition isomorphism. Added `ObjectSectionsNaturality.lean` as a decomposition node;
its pointwise object-sections theorem remains a named `sorry`.

## Proved and sorry left

The original target `sourceStageSectionsIso_naturality` is proved. The only remaining
sorry is `AlgebraicGeometry.Etale.objectSections_naturality`, node
`lem-weil-pbc-object-sections-naturality`.

## No longer needed

The diagonal pullback helper and its proof are no longer needed after splitting the
pointwise object-sections equality into its own node. No other imports were removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the pointwise object-sections calculation into the target.
It is a strictly simpler intermediate equality, so it was split into a separate node to
keep the delivered target proof compiling within the per-file limit. No statement was
weakened.

## New nodes

`lem-weil-pbc-object-sections-naturality` is stated in
`lean/Sheaf/AlgebraicGeometry/ObjectSectionsNaturality.lean`; its proof is the explicit
adjunction-unit and pullback-hom-ext calculation described in the node.

## Earlier second reading (a previous round; superseded)

The second reader should compile `ObjectSectionsNaturality.lean` and inspect the
pointwise statement against node `lem-weil-pbc-object-sections-naturality`; the target
module compiles and applies that statement without changing its original signature.

## Second reading by U2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; the proof only fills the target and adds the separately declared pointwise theorem.

2. Compiled `ObjectSectionsNaturality.lean` and `SourceStageSectionsNaturality.lean` with `lcompile.py`. Both compile cleanly. The target has no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration; the only remaining `sorry` is `AlgebraicGeometry.Etale.objectSections_naturality`, with its matching node and source proof description.

3. Checked the split statement against its use in the target. `objectSections_naturality` is a genuine pointwise naturality equality, strictly simpler than the chain-level target and exactly sufficient for the degreewise reduction. It duplicates no existing declaration found in the imported library.

4. Checked the proof route and pruning. The proof uses the pointwise node and the explicit `sectionsPullbackNat` naturality calculation. I removed four unused private helper calculations (`restriction_unit`, `composition_unit`, `objectSections_unit`, and `globalSections_eval`) and retained only `sectionsPullbackNat_app`, which is used by the target. The unit route remains represented by the target's existing construction and the pointwise node.

5. Updated the target DAG node's `proof` and `proof_deps` to match the actual degreewise proof and its use of `lem-weil-pbc-object-sections-naturality`; the unit and chapter fields remain unchanged.

Changed in this reading: removed unused private helpers, updated the target node proof dependencies, and recorded this review.
