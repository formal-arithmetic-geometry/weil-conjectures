# Worker report: lem-trf-frobenius-open-square

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-frobenius-open-square.json`: retained the requested B3 dependency deletions and refreshed the repair summary. No new nodes and no new Mathlib leaves.
- `report.md`: refreshed this repair review and removed stale validation and second-reader signatures so the next reader can sign independently.
- `citations.json`: retained all eleven verbatim quotations and checked them against the current shared node statements; no change needed.

## Attachments

None. Read-only searches of slopmaster2 for the item tag and Frobenius/open-square notions found no declaration supplying the complete item. `AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap` at `WeilConjectures/AlgebraicGeometry/GeometricFrobenius.lean:639` gives a one-iterate Galois square. Its statement and proof do not supply the scheme-Frobenius squares, every iterate and both scalar formulas together. Upstream-master sorry declarations are not treated as finished proofs.

## WANTED

None. Both blueprint snapshots and the Stacks sources used in this repair are available locally.

## Return repair

The single returned finding B3 is repaired: `def-weil-relative-frobenius-geometric-fiber` and `def-weil-frobenius-detailed` are absent from `stmt_deps`. I opened both statements: their scheme maps assume finite-type models. This item's statement instead constructs its maps explicitly for arbitrary k_0-schemes, using the general absolute Frobenius, contravariant Spec and fibre products. It references neither removed definition. No statement, hypothesis, conclusion, proof step or proof dependency has changed.

The sandbox already contained these deletions on this retry; they are retained as the substantive repair relative to the returned/current shared version, rather than being undone and reapplied. A read-only JSON comparison with the current shared unsplit node confirms that its two surplus dependencies are the exact returned defect and that the retained mathematical statement and proof match. The retained correction to `proof_origin` records the available local Stacks sources in place of a stale claim that they were absent. The dedicated return in `coord/returns/Q44.md` confirms B3. The field-by-field comparison found no changes in the statement, proof, proof_deps, blueprint, inherited searches or maintainer-owned fields. The mandatory delivery tool rebases the retained repair onto current origin/newtargets-dag and preserves maintainer-owned fields; no git command is run in the shared repository.

## Review by Q44

I reread the standing brief, worker role, stage-1 rules, SETUP's three blueprint levels, delivery-errors B–E, GOAL.md and dag-sync.md. I read chapter sec-trace-formula and unit sk-d-weil-push. This item is a supporting open-square lemma, not the unit's defining statement, so no unit realization record changes. The current main-20261015 statement and separate proof agree with the original master statement and two proof paragraphs. The five retained steps realize that same restriction/open-pullback/base-change route, followed by the product automorphism and scalar projection calculation. No SGA source is used.

For the item I read Stacks `varieties.tex:7007–7054`, Tag 03SM (`definition-absolute-frobenius`), and `schemes.tex:3138–3232`, Tags 01JP (`definition-fibre-product`) and 01JR (`lemma-open-fibre-product`). There are no new nodes requiring additional sources or Mathlib searches. I read all ten distinct retained statement/proof dependency statements and both removed definitions.

The finite-field-datum node supplies the tuple (p,a,q,k_0,k). Its later finite-type geometric-fibre convention is not imported: this item explicitly constructs its own products through the unrestricted fibre-product/base-change definitions. The eight explicit definition references in the statement equal the eight retained statement dependencies exactly. Thus the two deleted edges remove unused restricted definitions without dropping a required notion.

1. Step 1 uses `def-weil-open-immersion` for the restricted structure sheaf, `def-weil-absolute-frobenius-scheme` for the identity space map and power map on sections, and `def-weil-frobenius-substitution` for c^q=c on k_0. Those statements explicitly supply each fact. The structure map gives characteristic p; restricting the power maps gives the stated restriction and commutation. Fixing k_0 makes the iterates maps over the base. No finiteness or reducedness is used.
2. Step 2 uses `lem-weil-pbc-open-preimage-fibre-product`, whose statement identifies the inverse-image open, with its inclusion and restriction maps, as the fibre product. Step 1 identifies those maps with the model Frobenius square, so it proves Cartesianity with the required arrows.
3. Step 3 uses `lem-weil-pbc-open-fibre-product` for the base-changed open immersion, `def-pc-fibre-product` for projections and the unique lift, and `def-pc-base-change` for the product construction. Each allows arbitrary schemes. The two projections prove commutation. Given the test maps, their scalar projections agree; step 2 supplies the unique model lift, compatible over the base by its inclusion equation. Pairing it with the scalar map gives the lift and uniqueness. No general base-change theorem is left implicit.
4. Step 4 uses `def-weil-frobenius-substitution` for the base-fixing automorphism and its inverse, `def-weil-affine-spectrum` for contravariant functoriality, and `def-pc-fibre-product` for product maps. Their statements supply the iterated product automorphisms and inverse maps. Projection comparison gives commutation. The explicit lift g_X^{-m}u satisfies both equations and is unique because g_X^m is invertible. This elementary inverse calculation requires no new theorem node.
5. Step 5 uses exactly the second-projection clause of `def-pc-fibre-product`. It gives both semilinear structure-map identities without asserting k-linearity.

For C1/C4 I opened every cited statement and checked the exact clause each step takes from it. Both substantive open-pullback facts are existing cited lemmas. The remaining restriction, iteration, inverse and projection calculations are written explicitly. All eleven quotations in citations.json are verbatim substrings of the current cited statements; their (step,node) pairs equal all proof uses, proof_deps is their union, and none of the cited nodes is merged.

Small cases: m=0 gives identities; m=1 gives the defining maps; the empty open and empty ambient scheme are allowed; an identity open immersion gives identity vertical maps. On Spec(k_0) the scheme Frobenius is the identity while the scalar automorphism remains. The section argument also works on Spec(k_0[e]/(e^2)) and on non-finite-type models, so it needs neither reducedness nor a finite-type hypothesis.

B1–B2 and B4–B10 require no new node, leaf or search claims here; the retained blueprint metadata and inherited search records are unchanged. B3 is repaired as above. For C1–C8, existing generic open-pullback leaves are used with their actual statements, and the route is unchanged. D1–D5: the steps carry the argument; no clause is moved into a new node. E1–E7: the maps, arbitrary-scheme hypotheses, scalar equations and edge cases checked above reveal no statement dispute or source error. The retained source-availability correction and this report refresh are the only changes besides the requested dependency repair and its summary.

## Not duplicates

None; no new node was created.

## Unfinished work and validation

A fresh second reader must review and deliver the repair. This worker performs only the managed stage-1 dry run with `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q44 lem-trf-frobenius-open-square --no-push`. The installed interface accepts two positional arguments, with no trailing dot. No Lean is written, no compiler/Lake/build command is run, and nothing is pushed.


The managed dry run on 2026-10-17 completed with exit 0: `OK (not pushed) deliver/Q44/lem-trf-frobenius-open-square at c63ec4e149: preflight passed`. This result is recorded before a final repeat of the same dry run so the report itself is checked. The sandbox is ready for the fresh second reader; no push has been performed. The inherited second-reader signature was removed; the next reader must provide its own review.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the current main-20261015/master blueprint text and the finite-field, fibre-product, Frobenius, and Galois definitions; verdict PASS, with all hypotheses and clauses preserved, including arbitrary schemes and the semilinear equalities.
- Step 1: checked against Stacks Tag 03SM and the statements of `def-weil-open-immersion`, `def-weil-absolute-frobenius-scheme`, and `def-weil-frobenius-substitution`; verdict PASS, including iteration and the $m=0$ case.
- Step 2: checked against Stacks Tag 01JR and `lem-weil-pbc-open-preimage-fibre-product`; verdict PASS, since the inverse-image open and restricted Frobenius are explicitly identified.
- Step 3: checked against Stacks Tag 01JR and the universal-property statements of `lem-weil-pbc-open-fibre-product`, `def-pc-fibre-product`, and `def-pc-base-change`; verdict PASS, with model and scalar projections supplying existence, commutation, and uniqueness.
- Step 4: checked against the statements of `def-weil-frobenius-substitution`, `def-weil-affine-spectrum`, and `def-pc-fibre-product`; verdict PASS, with explicit product inverses and the lift $g_X^{-m}u$ proving the Cartesian property.
- Step 5: checked against the projection clause of `def-pc-fibre-product`; verdict PASS, including the semilinear orientation and $m=0$.
- New nodes: none; no duplicate, elementary, restated, or Mathlib node was created, and the repaired item only removes the two unused finite-type-only dependencies.
- Citations and metadata: all eleven quotations were checked as verbatim substrings of their cited statements; proof dependencies equal the step uses, and blueprint/source metadata remain consistent.

### Changes made in this second reading

- Added this independent review record; retained the worker's B3 repair removing `def-weil-relative-frobenius-geometric-fiber` and `def-weil-frobenius-detailed` from `stmt_deps`.
- Made no mathematical or node-file changes after checking the repaired split.


## Second reading by Q44

Independent second reading on 2026-10-17; this reader did not write the split. Read delivery-errors B–E, GOAL.md, dag-sync.md, the worker/stage-1 contract, and the recorded chapter/unit route. Compared the current main-20261015 statement and separate proof with the older master text, the sandbox item, and the current shared node. The source statements agree; there is no blueprint-update field requiring a different route.

- Item statement: checked every hypothesis and conclusion against both blueprint snapshots and all eight retained definition statements; PASS. Only the tuple is taken from def-weil-finite-field-fiber; the products and maps are explicitly defined for arbitrary schemes, with no imported finite-type assumption. Both Cartesian squares and both semilinear equalities are retained.
- Step 1: checked against Stacks varieties.tex, Tag 03SM, label definition-absolute-frobenius, and the full statements of def-weil-open-immersion, def-weil-absolute-frobenius-scheme, and def-weil-frobenius-substitution; PASS. Restriction of the power maps, iteration, characteristic p, and fixing k_0 are elementary from these definitions. A ring homomorphism commutes with powers, so identifying an open immersion with its open image preserves this calculation.
- Step 2: checked against Stacks schemes.tex, Tag 01JR, label lemma-open-fibre-product, and the exact statement of lem-weil-pbc-open-preimage-fibre-product; PASS. Its inclusion and restriction maps are precisely j_0 and the iterated model Frobenius, so this is the required square, with no additional hypotheses.
- Step 3: checked against Stacks schemes.tex, Tags 01JP/01JR, labels definition-fibre-product/lemma-open-fibre-product, and the full statements of lem-weil-pbc-open-fibre-product, def-pc-fibre-product, and def-pc-base-change; PASS. Applying the open-product lemma with the other two opens whole proves openness. In the lift construction, j_0 w_0=v_0 makes w_0 compatible with t over S_0; the two projections prove the lift equations and uniqueness for arbitrary test schemes T. No finiteness or unmentioned base-change theorem is required.
- Step 4: checked against the second blueprint proof paragraph and the full statements of def-weil-frobenius-substitution, def-weil-affine-spectrum, and def-pc-fibre-product; PASS. Both composites in the commutativity assertion have model projection j_0 p_X and scalar projection g_s^m a_X. Product functoriality gives the inverse, and the written lift g_X^{-m}u satisfies both required equations and is unique. This is elementary, not an omitted restriction theorem.
- Step 5: checked against the final sentences of the second blueprint proof paragraph and the projection equations of def-pc-fibre-product; PASS. The second projection is g_s^m a_Z, giving both asserted equations in the stated orientation.
- New nodes: none; PASS. The sandbox contains only the existing item, so no elementary helper, duplicate, clause restatement, new Mathlib leaf, or unsearched new node needs removal or conversion. No new search claims are made.
- Citations: opened all eight distinct proof-cited node statements and checked all eleven quotations as verbatim substrings; PASS. Citation (step,node) pairs equal the proof uses exactly, and proof_deps is their union. The two substantive open-pullback statements are existing Mathlib leaves and impose no hypotheses missing here.
- Attachment check: searched slopmaster2 by the item id, theorem name and the Frobenius-square declaration, and read GeometricFrobenius.lean:610–646; PASS. isPullback_geometricGaloisFrobenius_geometricFiberMap at line 639 states only the one-iterate Galois square, not the whole item, and therefore does not close this item. No master sorry declaration is used as a proof.
- Edge cases: checked m=0, m=1, the empty open, empty ambient scheme, identity open immersion, Spec(k_0), and Spec(k_0[e]/(e^2)); PASS. The model Frobenius may fail to be an isomorphism on nilpotents, but step 2 uses its inverse-image open, never an inverse. The Galois maps remain automorphisms. The argument also permits non-finite-type models.
- B3 dependency repair: independently read both removed definition statements; PASS. They restrict the model schemes to finite type and are unused by this item's explicit constructions. The eight bracketed definition references equal the eight remaining stmt_deps exactly.

Changes made in this second reading:

- Appended this independent review, leaving the worker's sections, including ## Review by Q44, in place.
- Retained the worker's removal of the two unused finite-type-only definition dependencies and the corrected note that the Stacks sources are available locally. No mathematical statement, proof, citation, or metadata repair was necessary after the audit.
- The documented trailing dot is rejected by the installed deliver.py interface, which prints usage. Use its accepted two-positional-argument form for the required managed server preflight and delivery. No local DAG/preflight/review tool, Lean compiler, Lake, or build is run.

Validation after this independent second reading: the managed dry run returned exit 0 and `OK (not pushed) deliver/Q44/lem-trf-frobenius-open-square at 8e654a5b0f: preflight passed`. The server checks accepted the item and the appended second-reading record. Proceeding with the same installed interface for delivery; the delivery tool repeats preflight.
