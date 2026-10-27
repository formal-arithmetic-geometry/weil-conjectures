1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-dvr-generic-line-extension.json: item, split into seven steps; original statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-quasiaffine-line-effective-divisor.json: statement-only input, Stacks Tag 0AYM, no Mathlib match after semantic searches in two formulations, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-cartier-extension-factorial-complement.json: statement-only input, Stacks Tag 0BD8, no Mathlib match after semantic searches in two formulations, Loogle and source grep.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: authentic launcher search log, retained without rewriting.

Two new nodes, zero new Mathlib leaves. Existing Mathlib leaves supply DVR dimension and factorization, open Noetherianity, principal-localization open immersion and stability under base change. The new nodes have empty proofs as required for a one-level split.

2. Attachments

None. Searched the live project's WeilConjectures source for the item's blueprint tag and extension/Picard/invertible-sheaf terminology. No completed project declaration gives the whole item. The existing regular-ring smooth-ascent declaration is supporting material, not an attachment of this item. No Lean was written, compiled or built.

3. WANTED

None. All sources used are available locally under literature/.

4. Problems and corrections

The imported item was statement-only. Its statement agrees with Stacks 0BD9 after smooth regularity and the regular-local UFD theorem; it needs no added hypothesis and no statement dispute. I supplied the actual divisor construction and finite-cover gluing argument instead of creating a node restating line-bundle extension. A contemplated principal-localization/base-change node was removed when the existing lem-weil-pbc-principal-localization-open-immersion and lem-weil-pbc-open-immersion-base-change were found. The overlap in the induction is only quasi-affine, not asserted affine: the new 0AYM input explicitly covers it. The two new nodes concern effective Cartier divisors, not a clause of generic line-bundle extension.

The inherited ancestry ends at blueprint.from.node=null: tools/blueprint_refs.py ancestor returns None. I preserved that ancestry and filled the exact inherited place with each support input's role; searched the whole blueprint for alternate formulations and recorded same_as=[]. Read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and the chapter/unit records. This remains the recorded auxiliary Picard input within the alteration ancestry; it does not change the unit route. Off-unit algebra and gluing tools are explained individually in split_report.tool_uses. No SGA source is used.

5. Unfinished work

None in the stage-1 split. The two new inputs remain statement-only for subsequent workers. Remote review_split passed before this report; final required delivery preflight is recorded by the delivery command.

## Not duplicates

lem-sfb-quasiaffine-line-effective-divisor vs lem-sfb-smooth-dvr-generic-line-extension: the new statement presents a line bundle on an arbitrary Noetherian quasi-affine scheme by an effective Cartier divisor; it neither assumes a DVR nor extends the bundle to a bigger scheme.

lem-sfb-cartier-extension-factorial-complement vs lem-sfb-smooth-dvr-generic-line-extension: the new statement extends an effective Cartier closed subscheme using UFD local rings, not an arbitrary line bundle. Steps 5--7 perform the passage from line bundles to divisors and back and the gluing.

Searched all DAG sources for 0AYM and 0BD8: no existing node has either tag. Searched DAG statements and the full blueprint for effective Cartier/quasi-affine/closure/extension and invertible-sheaf formulations before creating the nodes. The source-tag collision check has no further pair to explain. The broad regularity, factoriality, DVR and localization candidates were reused rather than duplicated. The inherited 0BD9 general extension statement is intentionally not made a new node.

## Review by Q72

I read Stacks divisors.tex, Tag 0BD9 (lemma-extend-invertible-module), including its affine divisor argument and gluing; for each new input I read the actual lemma and proof in that same file, 0AYM (lemma-quasi-projective-Noetherian-pic-effective-Cartier) and 0BD8 (lemma-closure-effective-cartier-divisor). In 0AYM the quasi-affine clause allows the negative divisor to be empty; the new statement is precisely this clause, and its proof directly produces a regular section even on a nonreduced Noetherian scheme. In 0BD8 the conclusion is existence of an effective Cartier divisor restricting as a closed subscheme; neither density nor separatedness nor global integrality appears in its hypotheses. I checked smooth regularity against descent.tex 036D and regular-local factoriality against more-algebra.tex 0AG0, and the DVR claims against algebra.tex 00PD. The affine localization/open-immersion facts were also checked against schemes.tex 01I3 and 01JY. These are the sources actually used, rather than the forbidden trace route.

For C4 I opened every existing node cited in the seven steps and read its statement, not merely its title. citations.json quotes the statements verbatim. Step 1 uses the DVR definition (local nonfield PID), the existing dimension-one theorem, and the definition of a regular ring. Every ideal being principal gives Noetherianity; the maximal ideal has one generator and dimension one. A nonzero prime generator in a PID is irreducible and hence maximal, so the only prime localizations are R and its fraction field. This makes the regular-ring hypothesis for Step 2 explicit, not an unproved extra assumption.

Step 2 uses the affine characterization in def-sbc-smooth-morphisms and the exact smooth-affine iff node, followed by lem-weil-pbc-regular-ring-smooth-ascent. Its conclusion is regularity as a Noetherian ring, so the charts really are Noetherian. The finite-type definition supplies quasi-compactness over the affine base, hence a finite subcover of the smooth charts. The regular-scheme definition says exactly that these regular affine charts make the scheme regular. No excellence or residue-field assumption enters.

Step 3 uses the affine-open stalk-localization theorem's explicit isomorphism with the prime localization. The definition of regular ring then makes each stalk regular local. The cited boundary-factorization theorem explicitly allows r>=0 and first concludes UFD; taking the empty parameter list r=0 meets all its hypotheses. Its extra conclusions are not needed, and no global UFD coordinate-ring claim is made.

Step 4 uses the precise DVR unit-times-uniformizer-power theorem: Step 1 verifies its Noetherian local domain hypothesis, and the uniformizer is nonzero because the maximal ideal of a DVR is nonzero. The fraction calculation proves K=R[1/pi]. The principal-localization node states that its spectrum map is an open immersion, and the base-change node states exactly that its pullback is an open immersion. This identifies the generic fibre with an open without invoking properness or a valuative criterion.

Step 5 applies the existing open-of-Noetherian theorem to W, a Noetherian affine chart from Step 2. Thus its open V is both locally Noetherian and quasi-compact as the new 0AYM statement requires. V is open in an affine scheme, so that statement supplies D and the required isomorphism for the restriction of the current invertible module. Intersections need not be affine or separated, so I did not silently strengthen the input.

Step 6 uses exactly the new 0BD8 conclusion. Its ambient W is locally Noetherian, V is open, D is an effective Cartier divisor, and all complement stalks are UFD by Step 3; restricting an open neighbourhood leaves the same stalk. The divisor-line-bundle definition makes O_W(E) invertible. The argument with a local free Cartier ideal generator and its dual writes out why restriction gives O_V(D), so no uncited restriction/duality theorem is hidden here.

Step 7 uses the existing site-module-sheaf-gluing theorem on a two-open Zariski cover, a finite set of indices. I specified both overlap maps and all equal-index maps, so the full triple-overlap cocycle in the cited statement follows by cancellation. Its result is a module sheaf with compatible restriction isomorphisms. Rank one freeness is local: refine each of the two opens by its trivializing cover; on each piece the glued module is the structure module and hence quasi-coherent. This verifies the quasi-coherent, locally free rank one definition of invertibility. Retaining the prior restriction isomorphism gives the original L after the finite induction, including its specified identification rather than only an equality of Picard classes.

For C1 I checked each passage needing a theorem has a node: smooth ascent, factoriality, principal-open immersion, preservation under pullback, Noetherianity of overlaps, divisor presentation, divisor extension and module gluing. The remaining passages are written local generator calculations or finite induction. None of the seven steps exceeds 2000 characters or hides a separate comparison or existence lemma. I checked the delivery-errors B--E concerns against these actual sources: complete hypotheses and conclusions, no def-for-theorem substitution, no duplicate or item-clause node, no assertion of an unavailable Mathlib theorem, no unsupported topology or gluing shortcut, and authentic recorded searches. LeanSearch and LeanFinder use different formulations for each proposed input; their hits are about basic opens, Noetherianity or ideal supports and do not state the Cartier theorem. Loogle and source grep give no match. I retained inherited searches and added only searches actually run through msearch.

Small cases checked: empty schemes and overlaps allow the empty Cartier divisor and trivial module; if the open is already the whole affine chart the divisor extension input is still applicable with empty complement. Disconnected and nonseparated Y do not affect finite open-cover gluing. No integrality of Y, uniform relative dimension, connected fibres, properness, excellence, perfectness or characteristic restriction is introduced. The UFD conclusion is local at every point, not a false assertion that every regular affine ring is factorial. The two new statements also allow an empty open, an empty divisor and components disjoint from the open, as their sources do. There is no uniqueness claim about extensions.
