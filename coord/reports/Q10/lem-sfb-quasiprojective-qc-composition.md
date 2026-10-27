# Worker report: lem-sfb-quasiprojective-qc-composition

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-quasiprojective-qc-composition.json`: statement, split; no Mathlib match for the whole statement. Five proof steps, all using existing nodes. The statement and its statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for each of the thirteen step/node citations.
- `searches.jsonl`: five searches run through the prescribed msearch command, retained as recorded; their exact queries and results are included in the item alongside its inherited searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the current `lean/WeilConjectures/` by item id, the blueprint docstring tag, quasi-projectivity and relative ampleness. No project declaration proves the full item. The project `IsQuasiProjective` notion found in ProjectiveSpace/QuasiProjective.lean concerns schemes over a field, not this arbitrary-base statement; mentions of relatively ample sheaves in other docstrings also do not establish this composition assertion. No Lean file was written and no compiler was run.

## Wanted literature

None. All source passages used are present locally.

## What needed correction or expansion

The item was statement-only. I expanded its Stacks 0C4M reference into the proof of 0C4K rather than creating a node restating the composition assertion. Whole-DAG searches found `lem-per-quasiprojective-qc-composition`, whose statement is byte-for-byte equal to this item's statement and whose existing five-step proof follows exactly this source route. I reused that proof and its existing dependencies, after checking each cited statement and the source again. This existing duplicate is reported for maintainer consolidation; I did not edit or merge either repository node. No statement dispute was found.

Blueprint searches over all imported chapters for `quasi-projective`, `relatively ample`, and `0C4M` found no imported node stating this arbitrary-base composition result: the curve statements have field bases. The item's existing ancestry is a created-node chain with `from.node = null`; `blueprint_refs.py ancestor` confirms None. I preserved that recorded ancestry and its already precise place, set `same_as` to [], and explained the five source steps in `split_report.blueprint`. This is the generic composition input to the projective-bundle composition helper on the recorded alteration-tower route, not a replacement of the unit proof. No unit realization record is due: this auxiliary node is not the unit's key statement.

## Not duplicates

No new nodes were created. The existing pair `lem-sfb-quasiprojective-qc-composition` vs `lem-per-quasiprojective-qc-composition` has identical statements and the same Stacks source; consolidation belongs to the maintainer. All smaller facts needed here already have nodes, so none is recreated.

## Review by Q10

I read Stacks `morphisms.tex`, lemma-composition-quasi-projective (0C4M), the complete statement and finite-affine-cover proof of lemma-ample-composition (0C4K), definition-relatively-ample (01VH), lemma-pullback-ample-tensor-relatively-ample (0892), lemma-characterize-relatively-ample (01VJ), and finite-type composition/base change (01T3, 01T4). I checked the tag-to-label mapping in `tags/tags`. These sources give the same arbitrary schemes and quasi-compact ultimate base as the item; neither separatedness nor a Noetherian base is added. There are no new nodes requiring further source review.

For step 1 I opened `lem-sfb-finite-type-composition-base-change` and `def-weil-finite-type-morphism`. The former's clause (1) gives finite type of the composite, and the latter explicitly includes quasi-compactness. Thus the quasi-compactness assumption needed by the final criterion is available from the outset.

For step 2 I read `def-pc-scheme`, `def-weil-pbc-quasi-compact-scheme`, `def-sc-invertible-module`, and again the finite-type definition and base-change lemma. A scheme has an affine open covering; quasi-compactness gives a finite subcover. The restriction of f is its base change along the open Y_i, so clause (2), with arbitrary base change allowed, applies. An affine open inside Y_i is an affine open of Y. This checks the relative-ampleness condition for L_i without assuming that arbitrary intersections of affine opens are affine. The ampleness of M_i is exactly the hypothesis on M applied to V_i. Restricting rank-one local trivializations proves invertibility of both restrictions.

For step 3 I read the complete statement of `lem-per-relative-ample-absolute-twist`. It asserts ampleness for every exponent beyond a bound, not only a sufficiently divisible subsequence; this is essential for taking a maximum. Its hypotheses are precisely quasi-compactness of f_i, ampleness of L_i over every affine open of Y_i, and absolute ampleness of M_i, all checked in step 2. The finite maximum includes 0, so it also makes sense for an empty covering.

For step 4 I read `def-pc-module-pullback`, `def-pur-sheaf-tensor-product`, `def-weil-pbc-ample-invertible-module`, and all clauses of `lem-weil-pbc-invertible-pullback-tensor`. They provide tensor powers including exponent zero, invertibility under tensor and pullback, and the tensor/composition isomorphisms. For inclusions j_i and k_i the equality f j_i = k_i f_i identifies the restricted twist with the locally ample twist of step 3. The proof explicitly supplies the unit comparison at exponent zero. Restriction is open-immersion pullback by the displayed module-pullback formula. Isomorphism invariance of the ampleness definition follows because the same sections correspond with identical nonvanishing loci; no uncited ampleness-locality assertion is hidden here.

For step 5 I opened `lem-trf-scheme-relative-ample-affine-cover`. Its statement assumes only a quasi-compact scheme morphism, an invertible module, and ampleness on inverse images of a specified affine open cover. These are exactly steps 1 and 4. It concludes ampleness over every affine open, which, with quasi-compactness, is the item's definition of relative ampleness. This node is used for its statement, not for its internal algebraic-space proof. The three off-unit statement tools (0892, monoidal pullback, 01VJ) are declared in `split_report.tool_uses`, with their generic purposes; no maintainer-owned `tool_uses` field was set.

I tested empty S (then Y and X are empty), empty X with nonempty S, identity morphisms, affine bases with trivial M, and exponent zero. No positive dimension or nonemptiness assumption is used. The common bound is taken over a finite cover only. No new helper restates a clause, no new node has an inline proof, and no source outside the authorized route or any SGA source is used. All five steps are non-elementary and cite the needed statements; the elementary restrictions and maximum calculation are written inside those steps. Each step is below 2000 characters and hides no additional standalone lemma. Every citation entry quotes the cited node's actual statement verbatim; all thirteen pairs were checked. The server dry run is the final mechanical check of missing nodes, cycles, route declarations, and delivery form.

## Unfinished work

None in the stage-1 split. The exact existing duplicate is reported above for the maintainer; no repository consolidation is part of this sandbox delivery.
