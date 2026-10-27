## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-qs-affine-chart-point-fibres.json`: item, unchanged statement, status split, five proof steps; no Mathlib match.
- `citations.json`: 18 step/node pairs with verbatim statement quotations.
- `searches.jsonl`: five actual searches run by msearch.py, retained unchanged.

New nodes: none. Mathlib leaves: none. Attachments: none. WANTED: none. Unfinished mathematics: none.

The sandbox initially contained only launcher markers. I read AGENTS.md, SETUP.md (all three levels), GOAL.md, the chapter, unit and stage-1 rules, and delivery-errors B–E. No previous item split/report or repair note was present. No repository or launcher file was written, no Lean was written, and no compiler/build command was used.

## Source and route

I read `literature/stacks-project/decent-spaces.tex` Tag 03JV (`lemma-UR-finite-above-x`), particularly condition (1) and the field-pullback/product proof of (5) ⇒ (1). I read Tag 03JX (`lemma-bounded-fibres`) and `spaces-properties.tex` Tag 03W7 (`lemma-quasi-separated-quasi-compact-pieces`), including the affine-product diagonal test in (1) ⇒ (3). The final proof combines exactly these arguments: instead of assuming a globally quasi-compact field representative, it obtains the needed quasi-compactness of W×_X Spec F directly from the relative diagonal and the given affine base open. This works for arbitrary S and does not conflate relative and absolute quasi-separatedness.

I also read `morphisms.tex` Tags 02GL (`lemma-etale-over-field`), 02GO (`lemma-base-change-etale`), 02GN (`lemma-composition-etale`); `schemes.tex` Tag 03GI (`lemma-quasi-compact-permanence`), Tag 01K5 (`lemma-quasi-compact-preserved-base-change`), and `lemma-composition-quasi-compact`; and `spaces-properties.tex` Tag 03H4 (`lemma-points-cartesian`), including its common-field-extension proof. The source definitions of spectra, point representatives and open subschemes are supplied by the cited definition nodes. All cited DAG statements were read in full.

The historical blueprint chain is retained. `tools/blueprint_refs.py ancestor` returns None for the existing helper. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), and the latest chapter. This is a supporting geometry lemma down its historical alteration/specialization chain and replaces no unit step. Whole-blueprint searches for bounded fibres, finite point fibres, field monomorphism and etale chart found no equivalent blueprint statement. The two etale-chart matches concern purity/towers. DAG searches for Tags 03JV, 03JX, 03W7 and the relevant concepts found existing helpers; none is recreated. Generic off-unit tools are individually declared in split_report.tool_uses.

## Searches and attachment check

I searched `lean/WeilConjectures/` by the exact blueprint tag and algebraic-space terminology and checked the upstream-name mapping. No project declaration states the whole item. Scheme-only finite-fibre declarations and finite-orbit statements for descent cocycles do not cover these algebraic-space hypotheses and both conclusions. A sorry declaration would not count as an attachment.

Five fresh Mathlib searches ran and their actual results were read: LeanFinder in plain words, Loogle `"AlgebraicSpace"`, grep `[Aa]lgebraic.?[Ss]pace|finite.*[Ee]tale.*[Ff]ibre` in AlgebraicGeometry, LeanSearch with the relative-diagonal formulation, and a second LeanFinder phrasing about affine presentations and their relations. All services answered. Loogle and grep had zero hits; semantic hits concern scheme quasi-finiteness, finite morphisms, affine properties and scheme quasi-separatedness. I read the corresponding scheme-only interfaces in QuasiFinite.lean, QuasiSeparated.lean and Fiber.lean. None states fibres on point classes of arbitrary algebraic spaces. The item records the exact query texts and results, preserving its inherited searches. No search was invented or repeated after the repair: its statement and search question did not change.

## Review by Q46

The unchanged statement agrees with the source: S is arbitrary, the diagonal is relative, a is representable etale, W is affine and maps into an affine open V of S. The last hypothesis is actually used to make W×_S Spec F affine. Surjectivity, Noetherianity, finite type over S and an absolutely quasi-separated base are never assumed. There are no new nodes, no clauses moved into new nodes and no missing construction hidden in a definition.

Step 1 is elementary. Outside the image of W both fibres are empty because R→X factors through W. Otherwise choose w over x. `def-a1-algebraic-space-point-classes` explicitly supplies the residue-field representative Spec kappa(w)→W→X; `def-weil-affine-spectrum` states that a field spectrum has one point with that residue field. Its map to S factors through V by composition through W. No quasi-compactness or monomorphism of j:Spec F→X is taken for granted.

Step 2 first identifies W×_S T with W×_V T using the open-subscheme convention in `def-weil-open-immersion`: equality of the composites of two maps to the restricted locally ringed space forces their equality on points and structure-sheaf maps. `lem-weil-pbc-fibre-product-affine-spectra` then makes B affine, since W,V,T are affine, and `lem-weil-pbc-affine-scheme-qcqs` explicitly makes it quasi-compact. The assertion that P→B tests the relative diagonal is written out on sections as equality a(u)=j(v); `lem-trf-space-fibre-products-etale-covers` supplies the actual sheaf fibre products. The assumed diagonal quasi-compactness applies to the scheme B. Taking the inverse image of the whole B proves P quasi-compact. Finally, `def-trf-algebraic-space` genuinely defines representable etale by scheme tests, so the test T→X makes P a scheme etale over T. No uncited base-change theorem for algebraic-space morphism properties is needed: the quasi-compactness is a direct application of the item's hypothesis.

Step 3 uses `lem-weil-pbc-etale-fibre-discrete-separable-points` for exactly the discreteness it states. At the sole point of T the residue field is F, and identity base change gives P itself by `def-pc-fibre-product`. A quasi-compact discrete space is finite by the explicit open-singleton-cover argument. `lem-a1-space-point-open-calculus` states the point-image formula for arbitrary morphisms; since image(T)={x}, its image formula identifies the desired W-fibre with the image of |P|. This is only a surjection on points, never an asserted bijection of point pullbacks.

Step 4 verifies all hypotheses for Q=P×_T P. `lem-weil-pbc-affine-scheme-qcqs` gives T quasi-separated. Clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` requires only P quasi-compact and T quasi-separated to make p quasi-compact; clauses (3) and (2) then give q and Q quasi-compact. `lem-weil-pbc-etale-base-change-finite-limits` explicitly gives q etale; clause (2) of `lem-weil-pbc-etale-composition-cancellation` gives Q→T etale. The cited field-fibre decomposition plus the same singleton-cover argument makes |Q| finite. No affineness or separatedness of P is assumed.

Step 5 identifies Q and R×_X T by the section triples (w_1,w_2,t), with both inverse maps and their projection to R written explicitly. This is an elementary calculation with the sheaf fibre product of `lem-trf-space-fibre-products-etale-covers`. The non-elementary point-image formula is explicitly supplied by `lem-a1-space-point-open-calculus`. It identifies the desired R-fibre as the image of finite |Q|. Each uses entry has a verbatim statement quotation in citations.json. The step lengths are 615, 914, 565, 654, 725 characters; no long step hides an auxiliary lemma.

Small cases checked: X empty; W empty/zero-ring affine; x outside the image of W; the identity chart of an affine scheme; finite separable components of etale charts over a field. Q can have more points than the product of |P| with itself, which is why Q has its own quasi-compact-etale argument. The affine-open factorization makes the proof valid even when S is not quasi-separated. No SGA source is used. All final proof dependencies were traversed on the current read clone and none reaches the item.

## Concurrent dependency repair

An initial dry run passed at 4ab83e31019 with a proof using the existing `lem-sfb-qs-space-field-monomorphism`, which was then unsplit and had no proof dependencies. Before the push check a concurrent live delivery split that helper using this item. Push preflight correctly rejected the resulting two-node cycle and pushed nothing. I read the changed helper and removed the dependence completely. The final Steps 1–2 now choose a residue-field representative through w and test the relative diagonal over the affine product B. This both uses the affine-open hypothesis explicitly and makes the field-monomorphism helper independently downstream of the item. All citation numbers and quotations were regenerated for the five-step proof; the original five search log records are retained. This is a proof repair, with no statement correction.

## Not duplicates

No new nodes. The final proof reuses the scheme affine-product, etale and quasi-compactness tools and the general point-image formula.

## Validation

The first dry run passed, and the subsequent push check detected a newly introduced live cycle and pushed nothing. The repaired five-step split passed the fresh required server dry run: exit 0, `OK (not pushed)` at `10ac70c0ae8`, preflight passed. The direct delivery command reruns preflight before pushing and prints the delivered commit. No checker was run locally.
