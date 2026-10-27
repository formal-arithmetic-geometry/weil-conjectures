# Stage-1 report: lem-trf-finite-center-open-closure-kernel-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-center-open-closure-kernel-data.json`: statement, now split into eight proof steps; no full Mathlib match. The statement is unchanged. Added `def-weil-quasi-separated-morphism` as a statement dependency because the statement already asserts quasi-separatedness.
- New DAG nodes: **0**. New Mathlib leaves: **0**. Existing generic results suffice; creating either a finite-center clause node or an ambient-recognition clause node would duplicate the item instead of splitting it.
- `citations.json`: verbatim statement quotes for all 25 step citations.
- `searches.jsonl`: actual msearch.py searches; the original item's 2026-10-22 search history is retained in the node, and today's five searches are appended there.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact node tag and by finite-center, closure-kernel and schematic-density terminology. The StrictTransform/StrictTransformBlowup and blowup-density files concern special blowup constructions; no project declaration supplies every clause under the present arbitrary-scheme hypotheses. Mathlib's `Hom.ker_apply`, `Hom.toImage_app_injective`, the quasi-compact image-factor instance, and the open-immersion image-factor instance supply component results already represented by existing DAG nodes. They do not state this whole item in one line.

## Wanted sources

None. All mathematical source material used is available locally in the Stacks source. No SGA source is used.

## Problems found and corrections

The item was an unsplit statement with earlier searches; the sandbox contained no earlier split or report. No repair-note file exists for it. There is no statement dispute. In particular, Tag 01PH is stated for a qcqs scheme, but only the affine-local implication in its proof is needed here. Applying that whole equivalence globally would add unjustified hypotheses. Step 1 instead proves quasi-compactness of the complementary immersion from finite generation on each affine open, including the empty-generator case. All base changes then use arbitrary-base-change results.

The quotient in Step 3 is a quotient of sheaves. Surjectivity on sections of arbitrary opens is neither asserted nor used. In Steps 6–8, injectivity on all open sections follows from the vanishing sheaf kernel on an affine basis, so no global-section exactness is assumed.

The chapter `sec-trace-formula` and unit `sk-i-curve-zero` were read. This is a subsidiary geometric kernel calculation in the already chosen strictification/strict-transform branch, not a replacement of the contracting-correspondence route of that unit. The two non-leaf generic tools from other units are declared in `split_report.tool_uses`: affine finite generation, and the ideal formula for a base-changed closed subscheme. Other cited statements are Mathlib leaves; definitions are used for their stated meanings. No unit record was changed.

## Unfinished work

None in this one-level split. No Lean was written or compiled. No new unsplit nodes were required.

## Not duplicates

There are no new nodes. Reused `lem-weil-pbc-scheme-image-qc-kernel` for the actual sheaf-kernel ideal on affine opens and `lemma-nagata-scheme-image-ideal-qc` for injectivity of the image factor. The latter's statement alone would not justify identifying the raw kernel before quasi-compactness has been proved, so Step 3 explicitly uses the former. Reused the existing affine finite-type, spectrum quasi-compactness, basic-open localization, open-immersion base-change, quasi-compact base-change, closed-base-change ideal, monomorphism, and equal-ideal closed-immersion nodes. Blueprint searches for “scheme-theoretic image” and “finite type ideal” found no imported node stating the full item. The nearest ancestor remains `lem-trf-local-term-locality`; its already specified exact `from.place` and `via` chain are retained.

## Review by Q16

I read the item against `morphisms.tex`, Tag 01R8 (`lemma-quasi-compact-scheme-theoretic-image`), including the proof that the sheaf kernel is quasi-coherent for a quasi-compact morphism. I also read `properties.tex`, Tag 01PH (`lemma-quasi-coherent-finite-type-ideals`), especially the final affine-local paragraph, and Tag 01PB (`lemma-finite-type-module`). For the topology used there I read `algebra.tex`, Tags 00E4 (`lemma-standard-open`) and 00E8 (`lemma-quasi-compact`). There are no new nodes requiring separate source reviews.

For Step 1, the complete statement of `lem-weil-pbc-quasi-coherent-finite-type-affine` gives precisely finite generation of the sections of a finite-type quasi-coherent module on an affine open, without Noetherian hypotheses. The localization/basic-open statement gives the homeomorphism to a localization spectrum; the spectrum statement gives its quasi-compactness. The finite-union and prime-ideal arguments are written out, and the definition of quasi-compact morphism closes the step. I do not infer that an arbitrary open immersion is quasi-compact.

For Step 2, the two base-change statements allow any morphism of schemes and thus apply to the displayed pullback along f. I read their local source statements in `schemes.tex`, Tags 01K5 and 01JY. Their conclusions are exactly quasi-compactness and the open-immersion property of j.

For Step 3, `lem-weil-pbc-scheme-image-qc-kernel`(1) explicitly equates the ideal on every affine open with the kernel of the section map, rather than merely defining an abstract kernel ideal. The closed-ideal definition explicitly gives its quasi-coherence, and the closed-immersion definition gives a surjective map of sheaves. Equality of the two kernel sheaves on an affine basis and the sheaf quotient argument then prove exactly the required conclusion.

For Step 4, I read the full statement of `lem-pc-closed-subscheme-base-change-ideal-image` and its source Tag 01JU (`lemma-fibre-product-immersion`)(1). It gives the actual ideal of the pulled-back closed subscheme, so zero restriction of J proves the scheme-theoretic equality over Omega, not just equality of supports. The equal-ideal closed-immersion statement applies to that closed immersion and the identity. The two base-change results give h quasi-compact and open. The open-immersion monomorphism statement and the fibre-product universal property prove that the diagonal is an isomorphism; the quasi-separatedness definition then applies. This is about the morphism h, and requires no quasi-separatedness of S or Y.

For Step 5, `lemma-nagata-scheme-image-ideal-qc` explicitly asserts injectivity on sections and stalks of the image factor when the original morphism is quasi-compact. The original morphism here is j, proved quasi-compact in Step 2. I also read its blueprint source and the returned Mathlib source in `IdealSheaf/Subscheme.lean` (the image-factor injection) and `Morphisms/Immersion.lean` (the open image factor). The definition of scheme-theoretic image explicitly defines its ideal as the largest quasi-coherent ideal inside the sheaf kernel. A zero sheaf kernel therefore makes the image the whole S.

For Step 6, the given equality R times_Y Omega = Omega identifies the correct pullback, so quasi-compactness of h_R is proved before the quasi-compact image-kernel lemma is applied. The hypothesis SIm(h_R)=R makes its ideal zero. That cited lemma states the raw kernel on affine opens, which is enough to conclude injectivity of the sheaf map and hence injectivity on all opens. This does not take the converse of mere topological density.

For Step 7, the structure-sheaf composite uses the injection just proved; equality of kernels is an elementary ring calculation on every open. The cited ideal-sheaf definition identifies that kernel with the ideal of s. The equal-ideal closed-immersion statement then gives exactly the unique isomorphism over Y needed for equality as closed subschemes. I read its sources Tags 01HO and 01HP in `schemes.tex`.

For Step 8, I verified that the inverse images in each section map are s^{-1}k^{-1}W and j^{-1}k^{-1}W, respectively. The section map from R to Omega is injective for this particular open by Step 6. The ambient equality is therefore the direct ring identity ker(beta alpha)=ker(alpha) for injective beta, and its alternative form is the definition of inverse image of J(k^{-1}W). The composition of closed immersions is checked using their affine quotient description from the cited closed-immersion definition. Thus this elementary step uses no uncited non-elementary image theorem.

I checked B–E of `delivery-errors.md` against these statements: no new nodes, no duplicated clause nodes, correct local source tags, actual logged searches, no proof-of-a-node substitution, and every use has its full verbatim statement in `citations.json`. All eight steps are shorter than 2000 characters. The non-elementary inputs are explicitly cited rather than hidden in a long step. No assertion from another unit replaces the unit route.

Small cases checked: I=0 gives Omega empty and J=O_Y, so S and any admissible R are empty; the ambient kernel is then O_P. I=O_X gives Omega=Y and J=0, so S=R=Y and the ambient formula is the ordinary ideal of k. If I is nilpotent, its complement is again empty, with the same conclusion. Nonreduced examples are preserved: for A=k[t,epsilon]/(epsilon^2,t epsilon), localization at t kills epsilon and J=(epsilon), not its radical; the proof keeps that exact kernel. For a non-quasi-compact disjoint union of schemes the affine-local finite-generation proof still applies and does not assert Omega is globally quasi-compact. Finally, a topologically dense open need not be schematically dense on a nonreduced scheme; the proof uses SIm(h_R)=R and quasi-compactness, exactly as assumed, to exclude this failure.
