Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-proper-closed-image.json`: item, split; no new nodes; no Mathlib leaf.

Attachments:

- `AlgebraicGeometry.isProper_imageι_comp` belongs to `lem-weil-pbc-scheme-theoretic-image-proper`.

WANTED:

- None.

What was checked and changed:

- I read the item, its blueprint proof, the `sk-thm-br` unit record, the scheme-conventions node, `pqf-lem-proper-closed-map`, `pqf-lem-image-proper`, and `lem-weil-pbc-scheme-theoretic-image-proper`. The latter states the stronger result needed here: for a proper morphism over a separated locally finite type target, the scheme-theoretic image inclusion is proper and the factor to the image is surjective, and the image is closed.
- Step 1 specializes that statement with base `S=Y`, target map `g=id_Y`, and `h=f`. The identity is separated and locally of finite type, while its composite with `f` is the given proper morphism. The cited statement explicitly supplies the proper factor, surjectivity, and closed image; the identity-base specialization is elementary once this statement is available.
- I searched the DAG for scheme-theoretic image, proper image, closed image, and Stacks tag `0AH6`. `pqf-lem-proper-closed-map` only says that the whole proper morphism is a closed map, so it is not the same statement. `pqf-lem-image-proper` is a related finite-type-target theorem, while `lem-weil-pbc-scheme-theoretic-image-proper` is the stronger existing statement used here.
- I ran the required leanfinder, loogle, grep, and leansearch searches. Mathlib has only the component interfaces; the exact theorem is the project extension declaration attached to the existing node. LeanSearch was unavailable and is recorded as such.
- The item now has a complete one-step proof, exact `proof_deps`, filled blueprint metadata, a declared cross-unit tool use, and `citations.json` with a verbatim quote from the cited node.

## Review by F1

I checked the source statement against Morphisms Lemma 0AH6 (proper scheme-theoretic image) as represented by the existing node. Every hypothesis needed by the specialization is present: `f` is proper, `id_Y` is separated and locally of finite type, and its composite with `f` is `f`. The cited node's statement, read directly, says both that the factor to the image is proper and surjective and that the image is closed in `Y`; the citation quote is verbatim. The only elementary work is identifying the identity base and rewriting the composite. I also checked the empty-source edge case: the empty image is closed and the factor to it is vacuously surjective. No new node was created, so there are no new-node hypotheses or statements to audit. The existing `pqf-lem-proper-closed-map` was deliberately not cited because it lacks the scheme-theoretic-image factorization and properness conclusion.

## Second reading by F1

- Item statement: checked against the blueprint node and recorded Stacks Morphisms Lemma 0AH6; properness implies universally closed, hence the image is closed. Verdict: correct and unchanged.
- Step 1: checked against the full statement of `lem-weil-pbc-scheme-theoretic-image-proper`; the identity map on `Y` is separated and locally of finite type, and its composite with `f` is `f`. Verdict: the specialization supplies the cited closed-image conclusion; no uncited non-elementary fact remains.
- New nodes: none; there are no new statements to check under B1-B7 or searches for duplicates.
- Edge cases: the empty source gives the empty closed image; a field-valued source and identity morphism give the expected closed image; no extra hypotheses are introduced.
- Changes: none. The existing cross-unit theorem is retained as the sole dependency, and the citation quote was verified verbatim against its statement.
