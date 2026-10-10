1. Files written:

- `lem-sc-qc-open-derived-lift.json` — statement, split; no new nodes.
- `citations.json` — verbatim citations for both proof steps.

2. Attachments: none.

3. WANTED: none.

4. The item was unsplit and has no exact declaration in either Lean source checkout. I found no declaration carrying the blueprint tag, and the statement is not present in Mathlib. The source is Stacks Project `perfect.tex`, Tag 08EE, which invokes `lemma-lift-quasi-coherent`: for a quasi-compact open immersion, derived pushforward gives the lift and its restriction is the original object. The existing DAG nodes `lem-pc-derived-direct-image-preserves-qcoh` (Tag 08D5(1)) and `lem-pc-restrict-derived-direct-image-open` (Tag 08FE) already state the two required non-elementary facts, so I created no duplicate children. The item's `blueprint.from.place` already identifies the Tag 08EE lifting clause and `same_as` remains empty.

5. I could not finish any Lean proof because stage 1 writes only the natural-language DAG; no Lean edits are required.

## Review by K1

I read the complete Tag 08EE lifting section in `/home/ubuntu/c1-stacks-review/perfect.tex`, including the statement and proof of `lemma-lift-quasi-coherent`. Step 1 takes `E' = Rj_*E`; I opened `lem-pc-derived-direct-image-preserves-qcoh.json` and verified that its statement applies to the quasi-compact, separated open immersion `j`, with source in `D_QCoh(O_U)` and conclusion in `D_QCoh(O_X)`. Step 2 uses the canonical restriction comparison; I opened `lem-pc-restrict-derived-direct-image-open.json` and verified that its statement specializes to `f = j`, target open `V = X`, source open `U`, giving `(Rj_*E)|_U ≅ E`. The hypotheses and object variance match the item exactly. I also checked the zero object and the case `U = X`: the construction gives `Rj_*0 = 0` and the identity restriction respectively. The earlier imported proof had no steps, so I added these two source-backed steps and their exact citation quotes.

Mathlib searches run for the item: LeanFinder `derived pushforward along quasi-compact open immersion preserves quasi-coherent complexes` (general sheaf pushforward declarations only; no match), Loogle `DerivedCategory, quasi-coherent, pushforward` (no match), grep `quasi.?coherent.*direct.?image` in `Mathlib/` (no match), LeanSearch `quasi-coherent derived category restriction to quasi-compact open is essentially surjective` (unavailable). Additional item searches already recorded in the copied node were retained.

## Second reading by K1

- Item statement: checked against Stacks `perfect.tex`, Tag 08EE (`lemma-lift-quasi-coherent`); the affine, quasi-compact-open specialization has exactly the stated hypotheses and conclusion. Tested `E=0`, `U=X`, a field affine scheme, and the empty open; all give the expected zero/identity restrictions (no `n` parameter occurs).
- Step 1: checked against Tag 08EE's `Rj_*` construction and node `lem-pc-derived-direct-image-preserves-qcoh`; the open immersion is quasi-compact and separated, hence quasi-separated, so the cited theorem supplies the required target category.
- Step 2: checked against Tag 08EE's right-inverse argument and node `lem-pc-restrict-derived-direct-image-open`; the comparison is correctly instantiated with target open `V=U`, whose inverse image is `U` and whose induced map is `id_U`.
- New nodes: none; existing nodes were searched and cited, so B1-B7 do not introduce additional statements.

Changes: corrected Step 2's mistaken `V=X` instantiation to `V=U` and recorded the corresponding source location; appended this independent source, dependency, hypothesis, and edge-case audit.
