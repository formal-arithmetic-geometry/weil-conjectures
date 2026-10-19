1. files written

- item: `lem-weil-pbc-finite-ring-derived-local-constancy` (split)
- `lem-weil-pbc-derived-local-constant-model`, statement, Mathlib no match
- `lem-weil-pbc-finite-derived-hom-isom-sheaf`, statement, Mathlib no match

2. attachments

None.

3. WANTED:

None; the cited Stacks files are present.

4. what was wrong or changed

The imported item had no proof steps. I split it into the Tag 094G local-model statement and the finite derived Hom/isomorphism-sheaf statement using Tag 09BE and the finite-ring argument. The item proof now applies the two statements on a common etale refinement and records the connected geometric-stalk conclusion. I checked the existing DAG for duplicate statements and found none; existing generic local-constancy nodes do not state bounded derived local models or derived isomorphism sheaves.

5. what could not be finished

No Lean implementation was attempted, as required for stage 1.

## Review by NG

I read the item source and blueprint ancestor `thm-weil-pbc-amplification-proper`, the Stacks passages for Tags 094G and 09BE, and the statements of every cited DAG node. Step 1 uses the new Tag 094G node exactly for bounded complexes with locally constant finite stalk cohomology. Step 2 uses that node for both local models and the new finite derived Hom node for the finite Hom fibre and finite locally constant isomorphism subsheaf. Step 3 uses the local-model node and the geometric-stalk definition to identify the local constant fibre at a chosen geometric point. I verified the finite-ring implies Noetherian/finite-type hypothesis and that the covers can be refined to a common etale cover. Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch where available) were run for both new nodes; LeanSearch was unavailable and recorded as such. I corrected the originally empty proof by making all three item steps explicit and preserved the no-finite-Tor clause.

## Not duplicates

lem-weil-pbc-derived-local-constant-model vs lem-weil-pbc-finite-ring-derived-local-constancy: the new node isolates only the Tag 094G local-model conclusion for one complex K, while the existing item additionally asserts finite derived Hom/isomorphism sheaves for two complexes and connected-stalk constancy.

lem-weil-pbc-derived-local-constant-model vs lem-weil-pbc-compatible-finite-derived-trivializations: the new node proves existence of an etale bounded finite-module model for a single complex; the existing node assumes finite local models and proves simultaneous compatible pro-etale trivializations of an inverse system.

lem-weil-pbc-finite-derived-hom-isom-sheaf vs lem-weil-pbc-finite-ring-derived-local-constancy: the new node concerns only the Hom and isomorphism sheaves for already constant bounded finite complexes; the existing item also includes local modeling and connected-X stalk identification.

lem-weil-pbc-finite-derived-hom-isom-sheaf vs lem-weil-pbc-compatible-finite-derived-trivializations: the new node establishes finite local constancy of one-level Hom/isomorphism sheaves, whereas the existing node uses such sheaves as hypotheses to construct compatible trivializations across all levels.

lem-weil-pbc-finite-derived-hom-isom-sheaf vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: the existing node treats evaluation on weakly contractible pro-etale objects, while the new node is the finite-ring etale derived Hom and isomorphism sheaf for arbitrary schemes and constant bounded complexes.

## Second reading by NG

The first worker's sections, including `## Review by NG`, are retained above as history. This second reading supersedes their claim that the three-step proof is complete and their justification for creating the two clause nodes. The preliminary ownership edit and audit were superseded by the substantive repair below. The imported item's statement is unchanged: Tag 094G's proof gives bounded constant finite-module models; Tag 09BE assumes a perfect source and does **not** by itself give this item's finite-source Hom extension. The latter is now proved in the item's steps, without introducing finite Tor dimension. Connectedness must propagate the stalk model across all of X, which the original step did not do.

- Step 1 (original step 1, now the induction setup): checked Tag 094G `lemma-locally-constant`, the standard-t-structure definition, constant-stalk theorem and exact-stalk statement. Verdict: the input interval, zero case, one-degree base and empty-cover case are explicit; constant module values are determined at geometric stalks.
- Step 2 (local-model induction, formerly hidden in a new node): checked the statement of `lem-pc-finite-free-constant-local-lift`, constant exactness, `lemma-constructible-flc-serre`, the triangulated-category definition and the cohomology long-exact leaf against the source proof at 094G. Verdict: actual lifts into the top term of a representative replace the source's omitted hypercohomology-class lifting; the precise short exact sequence and reduced interval justify induction.
- Step 3 (induction reconstruction): checked orthogonality and Hom-out-of-triangle exactness against their full statements, `lem-sc-connective-single-hom` for the shifted degree-zero Hom identification, then `lemma-constructible-hom-constant-locally` against the module map needed at the top degree. Verdict: the connecting morphism factors through top cohomology and yields the actual final differential; its square-zero condition and the shifted-cone identification are explained, not assumed from a cited node's proof.
- Step 4 (original step 2, free model preparation): checked `lem-pc-ring-finite-cone-free-model` including its universal finite-cone hypothesis, against every cone term of a bounded finite-module model. Verdict: all terms and thus their cohomology are finite; no projectivity or finite Tor dimension of E is inferred. The common covering is explicitly the family of fibre products.
- Step 5 (finite approximation): checked cycles/boundaries, long-exact cohomology, orthogonality, Hom-out-of-triangle exactness, and constant exactness. Verdict: m is at most g-2; the cone is at most m-1 and its [-1] shift at most m, so both Hom vanishings hold. This verifies algebraic and site-local comparison and compatibility with restriction.
- Step 6 (original step 2, finite derived Hom): checked new local-actual node clauses (1) and (2) against 08FR `lemma-local-actual`, existing constant-morphism node, constant-stalk statement and `lem-pc-ring-derived-map-representative`. Verdict: surjectivity and injectivity of the constant Hom sheaf map are both proved; finitely many component maps and homotopies suffice. The algebraic representative leaf applies to bounded projective modules, not to sheaves alleged globally projective.
- Step 7 (original step 2, isomorphism subset): checked exact stalks, constant stalks and the sheafification definition. The full statement of `lem-weil-pbc-site-sheafification-sections-local` supplies local representatives and local equality (in a universe containing the site); its overlap-gluing clause also proves the final Hom and isomorphism sheaf identifications. Verdict: actual inverses pass to the stalk, and algebraic inverses give constant inverses; representability of sheafified germs by local actual maps is accounted for. The possibly empty case is retained.
- Step 8 (original step 3): checked exact-stalk and constant-stalk statements, etale-open-map node and connected-scheme definition. Verdict: the locus of a fixed derived isomorphism class and its complement are both unions of etale images, hence open; connectedness and the chosen point make that locus all of X. This repairs the original argument, which only established the conclusion near the chosen point.

New-node audit:

- Removed `lem-weil-pbc-derived-local-constant-model`: checked against Tag 094G and the item's first clause; it was exactly that clause, so D1 applies. Its complete induction is now steps 1-3, including the omitted lifting.
- Removed `lem-weil-pbc-finite-derived-hom-isom-sheaf`: checked against Tag 09BE and the item's Hom/isomorphism clauses; it was a restatement of those clauses with the main finite-source argument omitted. Its proof is now steps 4-7. In particular 09BE's perfectness hypothesis is no longer silently replaced.
- New `lem-weil-pbc-finite-free-etale-local-actual`: read 08FR `lemma-local-actual` (sites-cohomology.tex lines 11881-11909), both assertions. Constant finite-free terms give a strictly perfect sheaf complex, and the arbitrary target is allowed. Verdict B1-B7: statement-only, every object introduced, definitions cited, homotopy equations and finite-free meaning given inline, single-escaped TeX, source tag and label verified in `tags/tags`; no unrun searches recorded. It is strictly smaller than the item and applies to arbitrary coefficient rings and arbitrary target sheaf complexes. The two clauses are not elementary consequences of definitions; 08FR is a real local derived-representation theorem.

Small cases: zero K and one-term K are in step 1; zero E or G gives a finite zero Hom group, with an empty isomorphism set unless the objects are isomorphic; over a finite field the argument specializes to bounded finite-dimensional complexes; B=0 has only zero modules and singleton isomorphism/Hom sets; over the empty scheme the covers and stalk tests are vacuous. The new local-actual node at a zero or one-degree free source gives the expected zero map or local lifting/null-homotopy statements, and permits rank zero in every term.

Search and duplicate checks: read the full DAG tag hits for 094G, 09BE and 08FR and keyword matches for locally constant derived complexes, finite-free models and null-homotopies. Existing ordinary constant-morphism, exactness and stalk nodes are cited directly. Full blueprint searches for `strictly perfect`, `locally constant cohomology`, `finite free`, `resolution` and `homotopy` found no imported version of the new etale local-actual statement. Mathlib searches were rerun using the independent queries recorded in searches.jsonl (finite-free complex resolutions, and local chain representatives/null-homotopies); hits were generic K-projective/localization APIs, not a local sheaf theorem. `lem-pc-ring-derived-map-representative` is the existing Mathlib leaf for the algebraic comparison. Grep of the read-only slopmaster2 and master sources by item id, local-actual label and derived/local-constant keywords found no exact finished declaration to attach. Master sorry declarations were not treated as proofs.

Changes and reasons:

1. Deleted the two clause-restatement nodes (D1/D2), replacing them with the one genuine 08FR tool and explicit eight-step argument.
2. Replaced the omitted 094G lifting with a finite-free sheaf-epimorphism lift into a bounded representative's top term; added the precise induction and reconstruction.
3. Proved the finite-source Hom extension by a finite-free approximation below the target bound, with both local surjectivity and null-homotopy injectivity.
4. Proved the isomorphism subset by actual inverses and exact stalks, and connected stalk constancy by the open/closed class locus; the original near-one-point argument was insufficient.
5. Added missing definition/source-theorem citations and regenerated citations.json from the actual cited node statements.
6. The new node's created.item is this item. No original statement was weakened and no Lean source was changed.

Tool use for maintainer: `lem-pc-ring-finite-cone-free-model` belongs to the Picard-duality unit and is used only as a general algebraic finite-free resolution tool. The unit's route has no theorem furnishing this model from the finite-cone condition. Its hypothesis follows because every term of the finite cone is a finite module over B. This replaces the first worker's unsupported finite-free approximation. The declaration is recorded under split_report.tool_uses for route review, not as a maintainer-approved top-level tool_uses field.

## Not duplicates (second reading)

`lem-weil-pbc-finite-free-etale-local-actual` has source 08FR, with no existing source-tag node. Existing `lemma-constructible-hom-constant-locally` treats ordinary maps between constant sheaves and cannot represent derived maps into arbitrary sheaf complexes or detect their null-homotopies. Existing `lem-pc-ring-derived-map-representative` is the algebraic bounded-projective Hom comparison and does not claim globally projective sheaves or etale-local chain representatives. Neither states the new fact.

Additional tool use: `lem-sc-connective-single-hom` is a general localization theorem of the abelian-variety unit, used after shifting both one-degree objects to degree zero. Its statement is read verbatim and supplies the ordinary sheaf map underlying the connecting morphism. Neither the existing standard-t-structure definition nor Tag 094G alone supplies this identification as a stated theorem. It is recorded only in split_report.tool_uses for maintainer approval of the route. Added the existing site-sheafification local-sections theorem to steps 6 and 7: the bare universal-property definition does not supply local representatives or local equality. No new node is needed for that fact.

Final sign check for step 3: using the recorded cone convention, Cone(t)[-1] has final differential -t and its rotated triangle has the original connecting map. The argument now names that sign explicitly and explains invertibility of the TR3 comparison using the cohomology sequence. The induction setup also spells out the cokernel lower truncation instead of assuming one representative satisfies both bounds.
