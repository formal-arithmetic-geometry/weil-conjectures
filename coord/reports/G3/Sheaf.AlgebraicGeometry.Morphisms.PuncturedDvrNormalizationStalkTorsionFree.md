## What changed

Added the torsion-free proof in the target module. It introduces two strictly simpler intermediate statements, in separate modules: the normalization stalk is a domain, and the stalk map is injective. The target follows from `Module.isTorsionFree_iff_algebraMap_injective`.

## Proved and sorry left

The target declaration `punctured_dvr_normalization_stalk_torsionFree` is proved. The intermediate declarations `punctured_dvr_normalization_stalk_isDomain` and `punctured_dvr_normalization_stalkMap_injective` remain as documented `sorry`s.

## No longer needed

No imports or stated proof dependencies were pruned; `NormalizationStalkBaseChange` remains imported by the intermediate modules.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the domain instance required by Mathlib's algebra-map characterization of torsion-freeness. This was split into a separate intermediate statement.

## New nodes

`lem-sbc-punctured-dvr-normalization-stalk-domain` and `lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective` add the two intermediate statements and their modules.

## Second reading by G3

1. The target module compiles, and its declaration has the same signature as the repository version; the proof applies the algebra-map characterization with the required domain instance and the injectivity theorem.
2. The two split statements are strictly simpler reductions (domain and injectivity), retain all original hypotheses, and have documented sources and nodes; neither weakens the target.
3. The target proof has no new `sorry`; the only remaining holes are the two named intermediate theorems, each explicitly documented.
4. The imports remain necessary for the public signatures and the normalization base-change dependency; no unused import was found after compilation.
5. The unit and chapter route are unchanged: the target remains in `sk-prop-input-spreading` and the split nodes use `lem-sbc-normalization-stalk-base-change`.

Changed during second reading: updated the target node's proof and `proof_deps` to match the Lean reduction, and recorded this review.
