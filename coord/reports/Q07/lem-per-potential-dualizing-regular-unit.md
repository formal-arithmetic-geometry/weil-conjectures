# Q07: lem-per-potential-dualizing-regular-unit

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-potential-dualizing-regular-unit.json: item, split into eight proof steps; statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-absolute-gysin-purity.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-putative-finite-detection.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-trait-gysin-residue.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-immediate-catenary.json: statement, unsplit; no Mathlib match.

Four new nodes, zero Mathlib leaves. citations.json contains verbatim statement evidence for every use in every step. research-results.json preserves the output of the twenty searches for the new nodes; searches.jsonl is the unmodified msearch log. The local gabber.txt extraction is reference material, not a delivered file.

## Attachments

None. I searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag, potential-dualizing terminology, pinnings, Gysin and tame residue terminology. No declaration states this item. Affine-space dualizing statements and relative trace-formula package fields do not cover arbitrary excellent regular schemes or their residue-compatible pinnings. The upstream master search likewise gave no attachment, and master is not evidence of completion.

## WANTED

None: the ILO volume is present in literature/ and supplies the proof. The finite-twist tool has its existing Stacks sources. No SGA source is used.

## Findings and corrections

There was no earlier sandbox node, report or search log. I copied the current unsplit item and retained its statement, inherited searches, citations and blueprint ancestry. Its proof was empty. Its source accurately identifies XVII 2.4.1.1 and 2.4.4.1, but pointwise purity alone does not prove potentiality: it must identify the residue normalization, including its sign. The split now follows the intervening trait, quasi-finite pinning and finite-surjective detection arguments in the source.

In self-review I added the existing regular-local-localization theorem: regularity of the closed local ring alone had initially been treated as if it already stated regularity of the entire affine scheme. I also made explicit that the existing codimension-one geometry theorem is applied to an auxiliary F_ell sheaf; its coefficient-dependent costalk formulas are never applied to Z/ell^n. No statement dispute or departure from the unit route was found.

## Unfinished work

None for this one-level split. The four new nodes are intentionally statement-only future items, with empty proof lists and proof dependencies. They do not claim formal proofs. No Lean was written and no compiler, Lake or global build was run.

## Not duplicates

lem-per-absolute-gysin-purity vs thm-pur-regular-immersion-purity: the existing theorem assumes a smooth ambient scheme over the fixed perfect field and chapter coefficients; the new theorem applies to regular affine schemes without a field of definition, including mixed characteristic, and includes quasi-finite finite-type Gysin composition. The existing theorem cannot be applied to the local rings in this item.

lem-per-absolute-gysin-purity vs prop-pur-regular-immersion-purity-compatibilities: that proposition retains the smooth-field hypotheses of its parent; it supplies no absolute-purity comparison for the finite normalized-curve morphism into an arbitrary excellent regular local scheme.

lem-per-absolute-gysin-purity vs lem-pur-gysin-structure: the existing statement is the relative affine-line Gysin comparison under the fixed smooth-purity conventions, not absolute Gysin purity for regular affines.

lem-per-putative-finite-detection vs lem-per-potential-dualizing-finite-pullback: the existing theorem assumes an already potential input and propagates it forward. The new statement starts with pointwise pinnings only and detects the missing residue condition by finite-surjective exceptional pullback. Using forward preservation here would be circular.

lem-per-putative-finite-detection vs lem-per-potential-extraordinary-pullback: the same distinction applies, and that node has only F_ell coefficients.

lem-per-putative-finite-detection vs lem-per-codimension-one-costalk-reduction: the existing node gives normalization geometry and F_ell costalk identifications; it does not give the quasi-finite induced Gysin pinnings or finite-surjective reflection of potentiality for prime-power coefficients. The split reuses its geometric assertions instead of creating them again.

lem-per-trait-gysin-residue vs lem-per-trait-residue-model: the existing node constructs the three-term residue model for F_ell; it does not compare its transition with the closed-point Gysin morphism, including the sign, for Z/ell^n. The new node states that missing comparison as a concrete equality in the model, not as a second assertion of potentiality.

lem-per-trait-gysin-residue vs lem-sc-generic-kummer-residues: the existing theorem concerns smooth curves over an algebraically closed field and Kummer residues in their function fields. The new comparison concerns an arbitrary excellent strict DVR trait and the extraordinary local-cohomology Gysin normalization, including mixed characteristic.

lem-per-geometric-immediate-catenary vs lem-trf-regular-ring-universally-catenary: the existing node proves universal catenarity from regularity; the new node uses catenarity to compare geometric and Zariski immediate specializations, without assuming regularity. The height-chain argument itself is written in Step 1 and is not another node.

None of the new nodes restates the item: they are, respectively, general purity for finite-type morphisms, detection of compatibility for arbitrary pointwise pinned complexes, a calculation identifying two trait morphisms, and a comparison of two scheme-theoretic specialization notions. The item itself constructs the pinnings, checks their compatibility through the normalized curve, and derives the twists and coefficient compatibility.

## Review by Q07

I read the chapter and unit records and the current ancestry through lem-per-artin-gabber-affine-curve. The item serves the finite-torsion regular local model in the dimension-normalized Verdier-duality part of that node's Step 3; it is not the key statement of sk-p-dl-a1-perverse, so no unit binding is changed. I read ILO XVII 2.4.1.1 through 2.4.4.1 in full, including the Gysin composition square in 2.4.3.4. For the new purity node I read XVI 2.3.1–2.3.2, 2.5.3–2.5.12, 3.1.1–3.1.2 and the coefficient diagrams and compatible cocycles in 3.3.1–3.3.2. For finite detection I read XVII 2.2.1 (including the localization observation), 2.4.3.1–2.4.3.3 and the first reduction in 2.4.4.1. For the trait comparison I read XVII 1.2.2–1.2.3 and 2.4.2.1(a), with the Gysin normalization of XVI 2.3.1. For geometric immediacy I read XIV 2.1.1–2.1.6 and the proof of 2.2.2.

Step 1 uses rem-pc-regular-normal for integrality, the explicit catenarity condition in def-exc-excellent-ring, and the new geometric-immediacy comparison. I verified that the last theorem compares the geometric notion actually used by def-per-potential-dualizing-complex, not merely ordinary Zariski specializations. The remaining chain-length argument is displayed: integrality gives a unique minimal prime and catenarity makes concatenated saturated-chain lengths agree. This avoids confusing minus local-ring dimension with dimension of the closure, which fails on nonequicodimensional examples.

Step 2 uses absolute Gysin purity for the closed point in its local spectrum, and the new putative-complex interface only to name the pointwise data. I verified regularity and Noetherianity of both affine schemes; the existing localization theorem supplies regularity at all primes. The generic point gives an identity immersion, so its pinning is exactly identity, not an arbitrary automorphism of the coefficient unit.

Step 3 uses the actual statements of the existing strict-henselization regularity and dimension theorems, the existing codimension-one reduction for its geometric clauses, excellence under finite type, and the new putative restriction/closed-costalk comparisons. The F_ell hypothesis of the geometry theorem is satisfied by its auxiliary application. This supplies a strictly henselian DVR, with finite surjective normalization, without presuming that the original prime-power costalk formula is available. The normalization algebra is finite, hence finite type, so the cited excellence theorem applies. I corrected the regular-local-versus-regular-scheme issue here too.

Step 4 uses absolute Gysin purity and composition, and the pointwise formula for quasi-finite induced pinnings in the finite-detection node. I checked that h is finite between regular affines, that its virtual dimension is 1-d, and that the closed and generic normalizations agree with the induced dimension function. The displayed equality compares the two factorizations through a residue-field morphism; taking inverses is precisely the induced pinning formula. This is not an unexplained transport of underlying isomorphisms and assumes no potentiality of the input.

Step 5 uses the new trait calculation for the exact equality sp = Cl_i(1)[2], then the existing finite-Tate-twist tool for the rank-one property. The inverse Gysin pinning cancels this transition, including its sign. I wrote why the scalar-linear model commutes with a trivial line and a shift, so the shifted trait conclusion is not another hidden lemma. Step 6 uses finite-surjective reflection, not the existing forward exceptional-pullback theorem whose hypothesis would already be the conclusion. Its costalk comparison is stated in the new node and identifies exactly the residue square being checked. The definition of potentiality then finishes the arbitrary-specialization argument.

Step 7 is an elementary consequence of the proved pinning equations and the existing finite-Tate-line theorem. I checked negative m through the dual line, the exactness and preservation of injectives of tensor with a trivial line, gluing under unit changes of basis, and the linearity of the specified residue construction. Step 8 uses the Gysin coefficient square and the finite-twist power transition. I checked that inversion of isomorphisms preserves the commuting square and that ordinary reduction of the coefficient unit does not assert the quotient ring is flat. No uniqueness theorem or coefficient-tower theorem depending back on the item is cited.

For small cases I tested a field (only the identity generic pinning), a strict trait (the equality in Step 5), and a regular local surface (the normalization map has virtual dimension -1). I checked a ramified normalization, where its residue-field Gysin factor cannot be discarded; the finite-detection interface explicitly retains it. Mixed-characteristic DVRs with ell invertible remain allowed. I also checked n=1 and n=2, m=0 and m=-1. The generic-point pinning assertion concerns the constant sheaf; a nonzero twist is allowed its correspondingly twisted pinning.

I read every cited existing statement and copied it verbatim to citations.json. I searched the whole DAG and blueprint by the notions, Gysin, absolute purity, traits, putative complexes, immediate specializations, and the ILO proposition numbers before creating nodes. All twenty new-node Mathlib searches ran through msearch.py with their own intended statements and a second phrasing; all services answered. I inspected the hits: finestTopologySingle is a spelling substring hit, Kummer-Dedekind is algebraic prime splitting, and the local-ring, specialization and normalization declarations do not state the derived etale comparisons. There is no Mathlib leaf. The item also has fresh logged searches in addition to its inherited search record.

I checked B–E of delivery-errors.md against each file: new statements introduce their objects and use definition dependencies; they have no proof sketch or partial split; pinnings and comparisons cited in the proof are actually stated; each non-elementary input is a node; all hypotheses and coefficients match; there is no appeal to an already potential input, no cycle through the parent, and no smooth-field replacement route. All proof steps are below 2000 characters, so none triggers the long-step audit. Generic tools outside the unit are declared individually in split_report.tool_uses with their mathematical purpose. No maintainer-owned unit, review, tool or live-project file is changed.


## Repair of the landing refusal (2026-10-18)

The returned delivery was approved mathematically but refused landing because lem-per-codimension-one-costalk-reduction changed after review. I compared the retained returned-head quotation in citations.json with the current DAG statement. The sole textual difference is in its last sentence: the current version explicitly cites def-asd-finite-etale-tate-twist and specifies that negative twists mean dual tensor powers. Its hypotheses, normalization geometry and costalk formulas are unchanged. The original Step 3 needs only the geometry, so the added twist clarification changes no inference or coefficient hypothesis.

I re-read the complete current statement and ILO XVII section 1.3 and Definition 1.4.1. Step 3 still applies the theorem to the auxiliary constant F_ell sheaf on the given Noetherian excellent scheme, using only the integral excellent strictly henselian one-dimensional closure and its finite normalization by a strictly henselian DVR. I made the current universal-homeomorphism, unchanged-generic-point and purely inseparable closed-residue conclusions explicit in that step. The prime-power costalk and residue comparisons continue to come from lem-per-putative-finite-detection; no F_ell formula is extended to prime-power coefficients. The purely inseparable degree is a residue-characteristic power and is a unit for our coefficients because ell is invertible.

I replaced the old whole-statement quote with the current verbatim geometry paragraph that Step 3 actually uses. I checked every other retained citation against its current statement: all are still verbatim, so no further stale citation needs repair. The item statement, the four auxiliary statements and all existing logged searches are retained. No new mathematical claim requires another Mathlib search. The delivery tool rebuilds the delivery on current main; no repository git command or live-file edit is involved.

Under my Review by Q07 signature, I rechecked B–E for this repair: the changed use is supported by the cited statement with its actual F_ell hypothesis, no new node or inline comparison is hidden, the original eight-step proof still follows XVII 2.4.4.1, and no source or statement dispute is introduced. Fields, traits, regular local surfaces, and mixed-characteristic traits with ell invertible remain valid tests. Every proof step remains below 2000 characters. This repair changes the item proof, citation evidence and report, rather than merely rebasing an unchanged delivery.
