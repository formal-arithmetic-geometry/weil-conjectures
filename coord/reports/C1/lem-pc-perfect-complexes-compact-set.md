1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-complexes-compact-set.json`: repaired statement node, now with affine, Mayer–Vietoris, and qcqs-induction steps.
- `dag/nodes/sec-picard-framework/lem-pc-derived-mayer-vietoris-triangle.json`: new statement-only Stacks 08BV node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every dependency used by every step.

2. Attachments: none.

3. WANTED: none. The imported Stacks source is `literature/stacks-project/derived-categories-of-schemes.tex`; the full source checkout is not included here, so the proof follows the cited Stacks tags and the local definitions.

4. What was wrong in the prior delivery: its finite-chain-map encoding was false because perfectness gives derived-category isomorphisms (roofs), and derived objects do not glue as a stack from chain-level overlap data. I removed that argument. The repaired proof uses the affine equivalence plus Tags 08CM/08EB for the affine base; the new 08BV derived Mayer–Vietoris triangle for the two-open gluing step; and the existing 08DR qcqs induction node. It does not cite the downstream compact-generation node, so there is no cycle.

5. What I could not finish: no Lean declaration states the item. The LeanSearch service was unavailable; LeanFinder, Loogle, and Mathlib grep were run and recorded.

## Not duplicates

lem-pc-derived-mayer-vietoris-triangle vs lem-sc-open-restriction-support-triangle: the existing node is a single-open restriction triangle with a cone supported on the complement; the new node is the two-open Mayer–Vietoris triangle with two pushforwards and their overlap difference.
lem-pc-derived-mayer-vietoris-triangle vs lem-sc-mayer-vietoris-open-cover: the existing node is a long exact sequence for ordinary sheaf cohomology; the new node is a distinguished triangle in the quasi-coherent derived category.

## Review by C1

I reread the item, `def-pc-perfect-complex`, `lem-pc-affine-qcoh-derived-equivalence`, and `lem-sc-invert-s-cohomology-induction`, together with the returned review and the Stacks places 08CM, 08EB, 08DR, and 08BV named there. Step 1 now uses the affine equivalence exactly for objects of `D_QCoh` and takes from the perfect-complex definition only the affine-local bounded finite-projective description; finite strings of modules and maps are set-sized, so this really gives a set of affine isomorphism classes. Step 2 uses the new node's exact triangle, including its restriction and difference maps, and the induction node's precise hypothesis that P(U), P(V), and P(U intersect V) imply P(U union V). For chosen representatives of the three restrictions, derived Hom-sets are sets; TR3 and the five-lemma identify cones up to isomorphism, so the possible global objects are set-sized. I checked the affine one-open case, the zero complex, and a cover with U intersect V empty. I explicitly removed the earlier chain-level gluing claim and removed the downstream compact-generation dependency. Every quote in `citations.json` was compared with the cited node statement; the new Mayer–Vietoris node has its own LeanFinder, Loogle, grep, and unavailable LeanSearch records.

## Second reading by C1

- Item statement: unchanged and still matches the set-of-representatives clause.
- Step 1: checked that 08CM/08EB supplies bounded finite-projective models only after passing through the affine derived equivalence; no derived roofs are treated as chain maps.
- Step 2: checked that 08BV supplies the actual derived triangle and that the 08DR node states the required qcqs induction hypotheses and conclusion. The set argument ranges over Hom-sets and cones of fixed morphisms, rather than nonexistent gluing data.
- New node: checked against the 08BV triangle and searched for duplicates and Mathlib matches; the two existing nodes listed above concern different statements.
- Citations: all four quotes are verbatim portions of their node statements.

## Source error

The first worker cited Tag 08JL for the derived Mayer–Vietoris triangle.  The current Stacks tag page identifies 08JL as Lemma 75.13.6 on pseudo-coherent objects, so that citation was false.  I replaced it with the correct source, `cohomology.tex`, Lemma `cohomology-lemma-exact-sequence-j-star`, Tag 08BV, whose ringed-space triangle specializes to the node's qcqs-scheme statement (with the existing quasi-coherent derived direct-image preservation infrastructure).  The item proof and the citation quote were otherwise unchanged.
