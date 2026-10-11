1. files written:
- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-jump-loci.json`: split target.
- `dag/nodes/sec-abelian-varieties/lem-sc-finite-free-complex-homology-upper-semicontinuous.json`: statement-only auxiliary node, no Mathlib match.
- `citations.json`: verbatim citations for every step.

2. attachments: none.

3. WANTED: none.

4. The target was unsplit and not stated by a sorry-free project declaration. I read the target's Stacks source (Tag 0BDI), the existing finite-free residue model (Tag 0BCD), and the existing termwise derived pullback node (Tag 06YD). The only new non-elementary fact is the affine finite-free complex homology upper-semicontinuity lemma; searches found no Mathlib declaration. The target proof now has a local finite-free model step, an explicit citation of the new upper-semicontinuity statement, and an elementary base-change/level-set step.

## Review by G1
I checked the target statement against Tag 0BDI and preserved all three clauses: arbitrary base change, upper semicontinuity, and locally constructible level sets. Step 1 cites the existing finite-free residue model and termwise derived pullback nodes, whose statements provide exactly the local model and fibre computation used. Step 2 cites the new auxiliary node, whose statement is precisely the finite-free homology upper-semicontinuity fact. Step 3 uses only the cited pullback statement plus the displayed set identity; this is elementary. I checked the new node's statement on zero and one-term complexes and recorded the three required Mathlib searches. No duplicate node or sorry-free attachment was found.

## Not duplicates
lem-sc-finite-free-complex-homology-upper-semicontinuous vs lem-sc-perfect-jump-loci: the new node concerns a bounded complex of finite free modules over an affine ring and only proves upper semicontinuity; the item concerns derived fibres of a pseudo-coherent complex on an arbitrary scheme and additionally asserts arbitrary base-change compatibility and local constructibility.

5. what I could not finish, and why: the new auxiliary node remains unsplit for a later worker; its statement is complete and has no proof sketch.

## Second reading by G1

- Item statement: checked against Stacks Project `perfect.tex`, Tag 0BDI (`lemma-jump-loci`); corrected the hypothesis to pseudo-coherent in `D(\\mathcal O_X)`, with perfect as an example, matching the source hypothesis by hypothesis.
- Step 1: checked against Tag 0BDI's affine reduction and truncation paragraph; repaired the invalid perfect-only residue-model citation by using the local bounded-above finite-free characterization in `def-pur-pseudo-coherent-complex`, explicitly truncating to a bounded complex, and retaining the termwise derived-pullback citation.
- Step 2: checked against Tag 0BDI's finite-free affine argument; the cited auxiliary statement gives exactly upper semicontinuity for the truncated finite-free complex.
- Step 3: checked against Tag 0BDI's base-change and locally constructible level-set clauses; the termwise pullback citation supports the fibre calculation and the displayed difference of open sublevel sets gives local constructibility.
- New node `lem-sc-finite-free-complex-homology-upper-semicontinuous`: checked statement against Tag 0BDI's finite-free matrix argument and tested on the zero complex and one-term finite-free complexes; statement-only form, definitions, source tag, blueprint metadata, and recorded Mathlib searches are present.

Changes made: fixed the reversed pseudo-coherent/perfect implication, added the missing pseudo-coherent definition dependency, replaced the perfect-only local-model step with the definition-level bounded-above model and explicit truncation, and updated `proof_deps` and `citations.json` accordingly.
