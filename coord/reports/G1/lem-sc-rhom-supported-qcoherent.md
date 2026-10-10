Files written:

- `dag/nodes/sec-picard-framework/lem-sc-rhom-supported-qcoherent.json` (item, split; no new nodes)
- `citations.json` (step-to-node verbatim citations)

Attachments: none.

WANTED: none.

What was wrong in the node or blueprint: the imported item had no proof and omitted all proof dependencies. The statement combines the two quasi-coherence cases of Stacks Tag 0A6H with the support observation in Tag 0A9C; the existing DAG nodes cover the affine calculation, perfect tensor-Hom comparison, tensor preservation of quasi-coherence, and restriction of derived internal Hom. No new lemma was needed, and no statement was changed.

What I could not finish: nothing.

## Not duplicates

`lem-sc-rhom-supported-qcoherent` vs `lem-sc-pseudo-coherent-rhom-qcoherent`: the existing node is Noetherian and has a pseudo-coherent quasi-coherent algebra as first argument; this item handles arbitrary pseudo-coherent complexes, the perfect case, and support.
`lem-sc-rhom-supported-qcoherent` vs `lem-sc-affine-pseudo-coherent-rhom-qcoherent`: the existing node is an affine calculation; this item is the global local-to-global theorem with both alternatives and support.
`lem-sc-rhom-supported-qcoherent` vs `lem-pc-perfect-rhom-tensor-comparison`: the existing node gives the tensor-Hom comparison for the perfect case, while this item also contains the pseudo-coherent case and support conclusion.

## Review by G1

I read the item against Stacks Project `perfect.tex`, Tag 0A6H (clauses (1) and (2), with the affine calculation in clause (3)(a)) and the support argument in Tag 0A9C. The statement's pseudo-coherent and perfect alternatives, local bounded-below conclusion, and support-on-a-closed-subset conclusion agree with those source clauses. I also read the statements of every cited DAG node. Step 1 uses the definition of pseudo-coherence for a local bounded-above finite-free model, the definition of `D_QCoh` for the target category, and `lem-sc-affine-pseudo-coherent-rhom-qcoherent`, whose hypotheses exactly provide the affine bounded-above/bounded-below representatives and whose conclusion gives quasi-coherent cohomology with a lower bound. Step 2 uses `lem-pc-perfect-rhom-tensor-comparison` for the global tensor-Hom isomorphism and perfect quasi-coherent dual, then `lem-pc-derived-pullback-tensor-qcoh` for closure of derived tensor under quasi-coherence. Step 3 uses `lem-sc-derived-internal-hom-restrict-open`; on an open disjoint from the support, the restricted target is zero, so the restricted RHom is zero. Step 4 is the elementary local-to-global passage for quasi-coherence, local boundedness, and support.

I checked the hypotheses at each use: the affine calculation is applied only after restricting to an affine neighbourhood supplied by pseudo-coherence and the affine quasi-coherent derived equivalence; the perfect comparison is applied to a perfect object in `D_QCoh`; the tensor closure node is applied to two quasi-coherent objects; and the restriction node is applied to the open complement of the support. Small edge cases are consistent: if the support is empty then the target and RHom vanish, while if the closed subset is all of X the support assertion is vacuous. The Mathlib searches recorded in the item were run through the required msearch commands; LeanSearch was unavailable, while LeanFinder, Loogle, and grep found no scheme-level theorem. No new node was created, so there are no new Mathlib leaves or attachment declarations to review.

## Second reading by G1

Step 1 checked against Stacks Tag 0A6H(1),(3)(a), the affine equivalence node 06Z0, and the affine RHom node; verdict: sound after adding the missing affine-equivalence citation.
Step 2 checked against Tag 0A6H(2) and the tensor-Hom and quasi-coherent tensor statements; verdict: hypotheses and conclusion match.
Step 3 checked against Tag 0A9C and the restriction-to-open node; verdict: restriction argument gives support on the stated closed subset.
Step 4 checked against locality of quasi-coherence and local boundedness; verdict: elementary local-to-global assembly.
No new nodes: B1--B7 and duplicate checks are vacuous; all reused nodes were searched in `dag/nodes`, and Mathlib searches are recorded in `searches.jsonl`.

Changes: added `lem-pc-affine-qcoh-derived-equivalence` to Step 1 and `proof_deps`, made “supported on T” explicit as vanishing on `X\\setminus T`, and added its verbatim citation. Tested the zero/empty-support and whole-support cases, and checked the field and affine cases against the cited statements.
