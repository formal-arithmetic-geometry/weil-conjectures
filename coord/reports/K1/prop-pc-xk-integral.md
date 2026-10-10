Files written:
- `prop-pc-xk-integral`, statement, repaired split.
- `citations.json`, exact statement quotes for every cited node.

Attachments: none (the four Lean declarations are partial clauses, not exact statements of this item).
WANTED: none.

The returned split had three problems. The higher-direct-image nodes were deleted because neither step uses higher direct images: step 1 only needs the proper global-sections lemma, and step 2 gets both cohomology base-change identifications from `lem-pc-flat-base-change-cohom`; the dimension equality follows by extending a basis. The duplicate normal-connected-irreducible node was deleted and replaced by the existing `lem-sc-regular-connected-integral`, whose statement directly gives integrality from regularity, nonemptiness, and connectedness. The circular `lem-sc-smooth-regular` citation was removed; regularity is now obtained on affine opens from `lem-weil-pbc-smooth-over-field-regular-local`, with local Noetherianity supplied by finite type from properness.

## Review by K1

I reread the item source, `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-twist/prop-pc-xk-integral.md`, and the Lean declarations in `RiemannRoch.lean` lines 1628--1657 and `GlobalSectionsBijective.lean` lines 188--195. The four Lean declarations remain attachments for partial clauses; none is presented as an exact attachment for the whole item. I also reread the statements of every cited DAG node and checked the new citation quotes byte-for-byte in `citations.json`.

Step 1 uses `lem-pc-projective-proper` for projective implies proper, `def-pc-curve` for curve implies variety and integrality, and clause (1) of `lem-pc-h0-proper-variety` for finite field extension of global sections. The section argument from the rational point is elementary. The deleted direct-image nodes are no longer used.

Step 2 uses `lem-pc-flat-field` for flatness of the field base change, `lem-pc-projective-proper` for properness and quasi-compact/separated hypotheses, and the displayed cohomology tensor isomorphism in `lem-pc-flat-base-change-cohom`. The equality of dimensions is the elementary basis extension argument. `lem-pc-proper-base-change` supplies both smoothness and properness after base change. On affine opens, `lem-weil-pbc-smooth-over-field-regular-local` supplies regular local rings; properness includes finite type, so the scheme is locally Noetherian. The same argument after every field extension supplies geometric reducedness. `lem-pc-h0-geom-connected` supplies geometric connectedness from properness, geometric reducedness, and the computed global sections; the base-changed rational point supplies nonemptiness. The exact statement of `lem-sc-regular-connected-integral` then gives integrality. `lem-pc-dim-base-change` gives dimension one, `def-pc-curve` supplies the variety/curve definition, and `lem-pc-closed-imm-base-change` supplies projectivity after base change.

I checked the hypotheses at the points where they are used, including the affine-cover application of the smooth-algebra lemma, finite type and local Noetherianity, the geometric reducedness quantifier over all field extensions, and nonemptiness via `sigma_K`. I tested the repaired reasoning on the identity field extension and on projective-line base change. The cited-node statements now match every non-elementary fact in the two steps, and the removed nodes no longer occur in the proof, uses, dependencies, or citations.

What changed in this repair: three node files and their citations were removed; step 2 was rewritten to use the two established regularity/integrality lemmas; the proof dependency union and tool-use declaration were updated; and the review was rewritten to identify the exact statement supplied by each citation.
