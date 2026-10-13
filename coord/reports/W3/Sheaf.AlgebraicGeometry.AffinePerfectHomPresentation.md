## What changed

Reduced `AlgebraicGeometry.exists_affinePerfectHomPresentation` to the affine comparison on chain-map representatives in the new module `Sheaf.AlgebraicGeometry.AffinePerfectChainHomPresentation`. The original signature and visibility are unchanged. The completed proof establishes K-projectivity after scalar extension by preservation of projectives under the extension/restriction adjunction and preservation of the bounded-above zero terms. Mathlib's K-projective localization bijection and the homotopy quotient's surjectivity then represent every derived morphism by a chain map. Applying the chain-level comparison extends both geometric transport equations to all elements of H. The two private proved helpers follow the already proved helpers in `AffinePerfectHomColimit`; no descent theorem is used.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_affinePerfectHomPresentation` (one original hole). Added: `AlgebraicGeometry.exists_affinePerfectChainHomPresentation` (one named hole, node `lem-pc-affine-perfect-chain-hom-presentation`). This is a decomposition, with net zero holes: the new obligation requires geometric compatibility only on chain-map representatives, and the parent proves the nontrivial passage to arbitrary derived morphisms. No sorry remains in the item's module. Both private helpers are proved using Mathlib alone.

## No longer needed

Removed proof imports from the parent: `Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`, `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, and `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`. These are needed by the remaining chain-level construction and retained there; consequently they are not pruned from the overall closure. The parent's DAG proof dependencies now consist of the chain-level comparison node; all its earlier affine construction dependencies move to that new node. No mathematical construction node or module is pruned from the total closure.

## Where the brief, the DAG or earlier work was wrong

No statement or interface correction is made. The original affine construction remains a substantial named obligation. An exploratory draft asserting compatibility for arbitrary unrelated E and K was rejected during edge-case review and removed; it is not part of this delivery. The delivered new statement restricts the original valid construction to chain representatives and retains all model and naturality requirements. Zero rings and zero complexes introduce no exceptions; bounded-above support, not nonzero terms or ring-map flatness, is the hypothesis used for K-projectivity. The initial tail remains inhabited. The unit record has no realized nodes for this item, and no unit route is bypassed.

## New nodes

`lem-pc-affine-perfect-chain-hom-presentation` in `dag/nodes/sec-picard-framework/` records the original affine construction with the final two geometric equations restricted to chain maps. Source: Stacks Project, Tag 09RE, using Tags 08EB, 06Z0 and 08DW. The proof plan retains all original affine, scheme-isomorphism and naturality dependencies. Searches through LeanFinder, Loogle and Mathlib grep found K-projective localization for the parent but no existing combined affine comparison. The new node's Lean record gives the full verbatim statement. No definition data is chosen from an unproved existence theorem: both interfaces are propositions and the parent only eliminates existence within its proof.

## Second reading by W3

1. Compared the delivered parent module with the repository version. The theorem signature and visibility are byte-for-byte unchanged; only proof imports, private helpers, and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The parent has no local `sorry`; the only remaining `sorry` is the explicitly named chain-level theorem. Axioms of the parent are limited to the permitted axioms plus `sorryAx` from that split theorem. Verdict: pass.
3. Read the split-off chain-level statement and node. It is a strict restriction of the two geometric equations to chain-map representatives, is needed by the parent reduction, and has a source, proof description, and matching Lean declaration. No duplicate library declaration was found. Verdict: pass.
4. The proof first uses the chain-level result, then proves K-projectivity of scalar extensions from bounded-above projective terms and lifts derived morphisms through `Qh_map_bijective` and homotopy-quotient surjectivity. Removed proof-only imports are listed above; no unit route is bypassed. Verdict: pass.
5. The parent and new node DAG `proof`, `proof_deps`, and `proof_origin` match the Lean route. The unit record is unchanged and no realized unit step is bypassed. Verdict: pass.

Changed only the report: recorded this second reading and its checks. No theorem statements or definitions were changed.
