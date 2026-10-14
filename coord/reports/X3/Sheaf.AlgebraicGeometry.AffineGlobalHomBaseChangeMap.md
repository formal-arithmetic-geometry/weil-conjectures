## What changed

Verified the three existing existence proofs in the assigned module. Removed the
redundant direct public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings:
the retained public ExtensionKFlatQuasiIso import already publicly imports it.
Every declaration signature and body is unchanged. The public import closure is
identical, so no caller requires adaptation.
Change record: coord/changes/affine-global-hom-redundant-change-of-rings-import-X3.md.

## Proved and sorry left

Holes closed: none. Holes added: none. The current module already has zero local
sorries. AlgebraicGeometry.exists_affineDerivedExtension,
AlgebraicGeometry.exists_canonicalTensorHomAdjunction and
AlgebraicGeometry.exists_globalHomPullbackComparison remain proved, with node
 def-pc-affine-global-hom-base-change-map. No new theorem or split is introduced.
This is import pruning and validation of an already proved item, not a net
reduction in holes or a completed pullback-counit data repair.

## No longer needed

Direct import removed: Mathlib.Algebra.Category.ModuleCat.ChangeOfRings.
Its declarations remain publicly available through ExtensionKFlatQuasiIso.
No mathematical dependencies are removed, no nodes become unneeded, and no
modules become unreachable. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief says the module still contains sorry, but its current source contains
none. Q1's concrete scalar repair landed while this worker was inspecting the
old version. The sandbox was refreshed from the new version, preserving its
scalar construction, public imports and elaboration settings. The redundant
ChangeOfRings direct import was exposed by that new public preservation module.
The remaining REPAIR marker concerns canonicalPullbackAdjunction's use of the
composition theorem's newly selected counit. It requires coordinated normalization
with schemeHomPullbackAdjunction and shared composition data; the existing
DerivedPushforwardSquareMateUnit.canonical_adjoint_eq uses rfl to identify the
adjunction definitions. This delivery does not close that separate data repair.
The existing DAG proof and dependencies still exactly describe the Lean argument,
so no node change is needed.

## Earlier second reading (a previous round; superseded)

1. Interface: compared the entire delivered module with the repository version.
   The sole diff removes the direct public ChangeOfRings import. All sixteen
   declaration signatures and bodies, section instances, options, and visibility
   are byte for byte unchanged. ExtensionKFlatQuasiIso publicly imports
   ChangeOfRings, so the public import closure is unchanged. The change record
   accurately describes this redundant import removal; no adaptation is needed.
2. Proof: compiled the delivered module locally with lcompile.py, cleanly in
   29.8 seconds. A scratch-copy #print axioms probe compiled in 30.1 seconds:
   all sixteen declarations use only propext, Classical.choice and Quot.sound,
   with no sorryAx. There are no local sorry, axiom, unsafe, opaque, implemented_by,
   extern, or kernel-check bypasses. Read all three existence proofs: scalar
   extension uses the concrete left derived functor and specified descended
   adjunction; the tensor-Hom proof specializes canonical naturality to build
   Adjunction.CoreHomEquiv and identifies its counit; the global comparison
   assembles the normalized evaluation mate and scalar-compatible sections
   comparison, including every displayed equation. The existing REPAIR marker
   remains honest: this import-only delivery does not repair the shared pullback
   counit. Choice of tensor-Hom data is characterized by the canonical predicate
   (whose uniqueness theorem was read); the mate and sections comparisons are
   characterized by their evaluation and derived-unit equations, not unrestricted
   mere existence.
3. Splits: no new declaration, node, or hole is introduced, and none is split
   off. Hence there is no new statement needing edge-case or duplicate searches.
   The scalar construction permits non-flat maps and zero rings; the global
   construction preserves every original qcqs, perfectness, QCoh and instance
   hypothesis even though its two normalization lemmas require fewer hypotheses.
4. Route and pruning: read NormalizedInternalHomPullbackComparison,
   AffineSectionsPushforwardNormalization, ExtensionKFlatQuasiIso and the canonical
   tensor-Hom and pullback characterizations. These supply the actual argument,
   with no replacement of a unit step. The unit sk-thm-picard-duality and its
   realized record are unchanged. No old proof dependency is unused: canonical
   tensor-Hom, K-flat extension preservation, normalized internal-Hom mate and
   affine sections normalization all occur in the proof. No module is pruned
   from the targets' closure; No longer needed correctly distinguishes removing
   a redundant direct import from pruning a mathematical dependency.
5. DAG: read def-pc-affine-global-hom-base-change-map in full. Its three proof
   steps match the three existence proofs, its four proof_deps are precisely the
   canonical tensor-Hom, extension preservation and two normalization nodes,
   and its Q1 proof_origin accurately records the existing partial data repair.
   No node edit is required for removing a duplicate import edge.

Second reading changed no Lean or DAG content. Added this independent review;
zero holes closed and zero holes added. This delivery is validation and removal
of a redundant direct import, not a new proof or completion of the data repair.

## Second reading by X3

1. Interface: `diff` against the repository shows the sole Lean change is
   removal of the redundant public `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
   import; all declaration signatures and bodies are unchanged.
2. Proof: `lcompile.py` compiles the module successfully. The source contains no
   `sorry`, forbidden declarations, or hollow definitions; existing proofs retain
   their stated hypotheses and conclusions.
3. Splits: no statements were split off, so there are no new nodes or duplicate
   theorem concerns. The three existence proofs remain substantive.
4. Route and pruning: all four recorded proof dependencies are used. The direct
   import is redundant because the retained extension module exports ChangeOfRings;
   the unit route and mathematical dependencies are unchanged.
5. DAG: the node's statement, proof steps, proof dependencies, and proof origin
   agree with the Lean source; no node edit is required.

Changed only the redundant import and this report. No holes were closed or added,
and no further pruning was found.
