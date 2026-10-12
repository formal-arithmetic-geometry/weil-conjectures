## What changed

Replaced the planned finite-intersection argument with the existing proved theorem
`exists_specializes_of_isClosed_constructibleTopology_of_mem_closure` from
`WeilConjectures.Topology.SpectralSpace.Constructible`. The proof shows that the
intersection of the constructible sets is closed in the constructible topology,
then converts specialization to closure of a singleton. Added the proof-only import
of that source module and removed the Sheaf finite-intersection import.

## Proved and sorry left

`Topology.exists_mem_iInter_closure_singleton` is proved. No `sorry` remains.

## No longer needed

The import `Sheaf.Topology.SpectralConstructibleFiniteIntersection` and the DAG
nodes `lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`,
`def-weil-constructible-subset`, `def-weil-spectral-space`, and
`lem-weil-pbc-spectral-constructible-finite-intersection` are not used by this
proof. The two definition nodes remain statement dependencies; this removes only
the old explicit proof edges, not the spectral or constructibility assumptions.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was valid but unnecessarily long here: the source library
already contains the closed-constructible-topology specialization theorem that
packages the needed compactness argument.

## New nodes

## Second reading by S2

1. Compared the only delivered Lean module with the repository version and checked
   the existing theorem signature byte for byte: unchanged. There are no definitions,
   new declarations, target changes, or change records. Both public Mathlib imports
   support the statement; the added source import is proof-only. Verdict: pass.
2. Compiled the final module locally without errors or warnings. Compiled a scratch
   copy with `#print axioms Topology.exists_mem_iInter_closure_singleton`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Inspected for
   forbidden declarations and attributes; no sorry or hollow definition occurs.
   Read the applied source theorem and constructible-clopen lemma. Verdict: pass.
3. No statements were split off or added. Checked the reduction's edge cases:
   an empty index type gives the closed whole space, an empty intersection makes
   the closure hypothesis impossible, and an empty space has no point `x`.
   No finiteness or nonemptiness hypothesis is introduced. Verdict: pass.
4. Searched the upstream and Sheaf topology sources for existential specialization
   lemmas, and Mathlib's spectral constructible-topology module for closure and
   specialization results. The existing proved upstream Stacks 0903 (1) theorem
   is the direct route; no new lemma is needed. Checked `dag/units/sk-thm-p1.json`:
   this node and all four removed proof dependencies are below its `realized`
   statement and steps, so no unit route is bypassed. The report lists every old
   proof dependency removed. Verdict after import repair: pass.
5. Compared both node records as JSON: only proof-route fields differ; the Lean
   statement record is unchanged. The proof text describes closedness of the
   intersection, the existing specialization theorem, and closure conversion;
   `proof_origin` identifies that proved declaration, and the empty `proof_deps`
   agrees with the empty union of node citations. No new nodes. Verdict: pass.

Changed on second reading: removed the unused
`Sheaf.Topology.SpectralConstructibleFiniteIntersection` import, which the first
report claimed had already been removed; replaced the old finite-intersection
proof docstring with the actual upstream-theorem reduction; clarified that the
pruned definition proof edges remain statement dependencies. Kept the valid proof
term and node proof route unchanged.
