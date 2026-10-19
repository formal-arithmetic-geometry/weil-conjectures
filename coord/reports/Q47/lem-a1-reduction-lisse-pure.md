# Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-reduction-lisse-pure.json`: item split; one proof step, three cited nodes.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-map-lisse.json`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: verbatim citation quotes for the item step.

Attachments: none. The stale `lean_audit.slopmaster2` names were searched in the read-only source checkout; the audited module/declarations are absent from the current checkout, so no exact declaration attachment is claimed.

WANTED: none.

The imported proof was too broad: `lem-a1-finite-map-purity` states punctual purity only, while the proof also needs lissity of a finite étale pushforward. I added `lem-a1-finite-map-lisse` for that strictly smaller fact. The restriction of `g` over W being finite étale, the inverse image lying in C_0 after removing `g(C'_0\\setminus C_0)`, and the restriction identity for `j_!\\mathcal F` are elementary consequences of the definitions and are written in the item step. The current source checkout has `Upper.lean` with 97 lines and no declarations matching the stale audit entries at the recorded lines 269–458; this was recorded rather than treated as an attachment.

## Not duplicates

`lem-a1-finite-map-lisse` vs `lem-a1-finite-map-purity`: the new node asserts lissity of a finite étale pushforward, whereas the existing node asserts preservation of punctual purity and does not state lissity.

## Review by Q47

I read the item statement and proof in the current blueprint at `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-reduction-lisse-pure.md` and its proof file. I also read the existing `lem-a1-finite-map-purity` statement and the full `def-weil-punctual-weights` statement in the DAG. The new node is sourced from the proof sentence that asserts lissity; its statement introduces a finite étale map, a lisse Weil sheaf, and the lisse pushforward conclusion, with the scheme conventions as its statement dependency.

Step 1 uses exactly the new lissity statement for the lisse conclusion, the existing finite-map-purity statement for punctual purity, and the punctual-purity definition for the meaning of the weight assertion; the attached quotes in `citations.json` are copied verbatim. The finite étale restriction and the restriction of extension by zero are elementary from the definition of W and the open immersion. I checked that W removes both the branch locus and the image of the finite complement, so both hypotheses needed for the finite-map statements hold. I tested the edge case where the complement is empty (then the second removed set is empty) and where W is empty (the restricted assertion is vacuous). The Mathlib search was performed with LeanFinder, LeanSearch, Loogle, and a Mathlib source grep; all found only generic pushforward or étale declarations, so the new node remains unsplit.

## Source error

The imported proof's phrase “the lissity and the punctual purity ... follow from [lem-a1-finite-map-purity]” cites a purity-only node for lissity. The split repairs this by separating the lissity lemma; the mathematical route and item statement remain unchanged.

## What I could not finish

No Lean code or compiler was run, per the stage-1 restriction. The required delivery dry run remains to be run after this report is present.
