## Worker report

Q10 split lem-sfb-affine-principal-relative-pseudocoherence-localization at stage 1 only. The statement and statement dependencies are unchanged. The eight proof steps follow Stacks Tag 09VD (more-morphisms.tex, lemma-localize-relative-pseudo-coherent), restricted to the principal-source-open case that the item actually states. The proof constructs r=n+2. No Lean was written and no compiler or build tool was run.

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-principal-relative-pseudocoherence-localization.json: item, split; no Mathlib match.
- citations.json: 23 verbatim statement quotations, one for every step/node citation.
- report.md: this report.

Attachments: none. The project-source searches for the exact blueprint tag and for relative pseudo-coherence found no declaration giving this statement. The principal pseudo-coherent model declarations that did occur concern absolute affine models of module complexes; they do not give these two chart changes for arbitrary E.

WANTED: none.

## New nodes

None. All non-elementary results already have nodes. In particular the two-term inverse-adjoining calculation and the sectionwise open comparison are written out as elementary steps instead of being turned into redundant nodes. There are zero new Mathlib leaves.

The new Mathlib searches are recorded verbatim in searches.jsonl and the item's mathlib_searches. LeanFinder was tried with two semantic phrasings; LeanSearch, Loogle and Mathlib grep were also run. No service was unavailable. The semantic hits concern local properties of affine scheme morphisms and ordinary closed immersions, not pseudo-coherence of arbitrary derived module complexes. The grep for pseudo-coherence and strictly perfect complexes and Loogle PseudoCoherent returned no hits. Existing searches in the imported item are preserved.

## Source and blueprint audit

Read more-morphisms.tex Tag 09VD in full, perfect.tex Tag 09VA (lemma-closed-push-pseudo-coherent) with its proof, modules.tex Tag 01AX (lemma-i-star-exact), schemes.tex Tag 01HV (lemma-spec-sheaves), algebra.tex Tag 08JZ (lemma-principal-localization-NL) with its displayed polynomial quotient, and more-morphisms.tex Tag 068C (lemma-regular-immersion-perfect), where the finite-free resolution supplies pseudo-coherence. The explicit coefficient induction below fills in why aT-1 is a nonzerodivisor without assuming a is one.

Read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). Also read the live chapter and unit records and SETUP's three levels. This is a supporting prerequisite in the inherited long dependency chain, not a replacement of a unit step. blueprint_refs.py ancestor returned None for this chain, so the inherited null ancestor, via and precise from.place are retained. Whole-blueprint searches for pseudo-coherent, pseudo coherence, localize-relative-pseudo-coherent and principal localization found no equivalent item; same_as remains []. DAG searches included Tag 09VD and closed-pushforward, exact closed immersion, affine-quotient sheafification, inverse-polynomial localization, and pseudo-coherent restriction notions. Every reused node's statement was opened. No new node requires a same-tag duplicate comparison.

What was wrong: the item was an unsplit statement with no proof. There is no statement dispute. The source's lemma is phrased for an arbitrary affine source open while its displayed proof writes U=D(g); this delivery makes no assertion about arbitrary affine opens and uses exactly the principal-open statement assigned here. The existing affine-quotient sheafification node names more-on-morphisms.tex in its source, but the actual Stacks file and Tag 068C are more-morphisms.tex; I read the latter and schemes.tex 01HV rather than silently depending on a missing file. No other node was edited.

## Review by Q10

I checked the statement against 09VD with the fixed integer m carried through both inverse-adjoining operations. Its given closed immersion is the surjection R_a[x_1,...,x_n] -> A, so no additional finite-presentation, regularity, Noetherianity or quasi-coherence hypothesis is used. The construction remains over the original S and uses n+2 variables.

Step 1 uses the actual statements of def-weil-closed-immersion (the affine surjective-ring characterization), def-nagata-relative-affine-space (the polynomial chart on an affine base), and lem-weil-pbc-localization-away-polynomial-quotient (the quotient by aT-1 and its surjection). I verified the quotient identifies the coefficient map, not merely two abstractly isomorphic rings. Commutation with each x_i and the inverse of a gives the required universal-property identification. This is a direct application of the three statements, with the elementary polynomial-variable identification written out.

Step 2 uses the quotient node for the cokernel. Injectivity is proved in the step itself: the constant coefficient forces u_0=0 and each successive coefficient forces u_q=0. This works even when a is a zero divisor or nilpotent. The displayed augmentation is therefore a quasi-isomorphism, as required by the sheafification node used next; no regular-sequence theorem is being silently assumed.

Step 3 uses lem-sc-affine-quotient-resolution-sheafification exactly for a quotient-spectrum map and the explicit augmented nonnegative chain complex, on the whole affine target. Its statement supplies the quasi-isomorphism to the pushed-forward structure module. It does not assert finite freeness; that is checked here: there are exactly two rank-one free terms. The localization-section characterization in lem-weil-pbc-spec-module-tilde-sections identifies the associated sheaf of C with O_P, including restrictions on the principal basis. def-pur-pseudo-coherent-complex then applies directly to this bounded finite-free model. This avoids citing a definition as if it were a theorem that arbitrary closed pushforwards preserve pseudo-coherence.

Step 4 uses lem-sc-closed-immersion-pushforward-exact for underlying abelian sheaves and explicitly explains the passage to module sheaves. The existing statement really is for topological closed inclusions, which suffices after identifying a closed immersion with its image. Exactness of module sequences is exactly that of their underlying abelian sheaves, with the induced module structures. The definition of derived direct image then agrees with termwise direct image because this functor preserves quasi-isomorphisms. Composition is checked on every open set, including its ring action. This is an elementary extension of the quoted exactness theorem, not an assumed arbitrary-scheme base-change theorem.

Step 5 applies lem-sfb-closed-pushforward-pseudocoherence to k and Ri_*E, not to i: the structure-module hypothesis is established for k in step 3, whereas no such hypothesis was assumed for i. The cited statement includes every integer m and arbitrary derived objects without quasi-coherence or boundedness. The composite is closed by lem-weil-pbc-closed-immersion-comp. Step 4 supplies the required equality of derived images.

Step 6 uses lem-weil-pbc-principal-localization-open-immersion for W and U, the inverse-polynomial quotient statement for l, def-weil-closed-immersion for i' and l, def-nagata-relative-affine-space for Q, and the closed-composition node for j. The lift h exists from the already established C -> A surjection. The surjectivity after localization is proved on fractions, not hidden in the words 'clear denominators'. Equality of scheme maps follows from equality of their specified ring maps. I checked that the preimage of D_P(h) is D_X(b) as a scheme, not only set-theoretically: it is given by this localization map C_h -> A_b.

Step 7 uses the finite-stage approximation definition for restriction of pseudo-coherence, the ordinary module open-restriction statement for its section formula, and def-pc-derived-pullback for why derived restriction agrees with that exact restriction. All cohomology conditions survive because restriction preserves stalks and is exact. The comparison with i'_* is proved on the same open T and the same preimage, hence on all restrictions and structure-ring actions. Exact closed images from step 4 make the equality valid for unbounded representatives. Thus there is no invocation of an uncited flat base-change result that might require quasi-coherence of E.

Step 8 again applies the affine-quotient sheafification statement, now to l with ideal (hz-1), using the same explicit injectivity proof from step 2 and the quotient presentation in step 6. Its rank-one terms are identified with O_Q by the same localization-section statement; the pseudo-coherence definition verifies the structure-module hypothesis. The closed-pushforward theorem is then applied to the m-pseudo-coherent object from step 7. Exact composition identifies its output with the precise Rj_*(E|_U) required by the conclusion. In particular it is not a different coefficient category or a module-only replacement of E.

I checked B--E against these files: no new nodes, no invented searches, no source-only citations in place of theorem nodes, no circular reference, and no clause moved into a new node. The closure of all proposed dependencies does not contain the item. All proof steps are below 2000 characters. citations.json quotes are literal parts of the cited statements (the full statement in each case).

The two cross-unit generic tools are lem-sc-affine-quotient-resolution-sheafification and lem-sc-closed-immersion-pushforward-exact. They supply affine resolution sheafification and exact topological closed direct image, respectively; no statement of this unit gives those tools. They are declared in split_report.tool_uses for the maintainer to review. The other cross-unit theorem citations are existing Mathlib leaves; the remaining citations are definitions.

Edge cases checked: n=0; R or A the zero ring; a=0 or nilpotent (then V and X are empty); a a zero divisor; b=0 or nilpotent (then U is empty); b=1 (the second construction is still valid); E=0; arbitrary negative or positive m; and an unbounded complex E without quasi-coherent low-degree cohomology. The coefficient induction still proves injectivity of cT-1 in every case; when the localization is zero the resolution has unit differential where appropriate. No cancellation by c, no nonempty-open assumption and no affine cohomology theorem for E is used.

Nothing remains mathematically unfinished at this splitting level. No new node is split recursively. Required server checks and the direct-delivery result are recorded below after they finish.

## Validation

The server review_split check passed with zero new nodes. The required deliver.py --no-push dry run exited successfully and printed OK (not pushed) at 283c8f11834; full server preflight passed. The warning that the inherited unit has no realization recorded is pre-existing and does not require changes to its fixed record. A final dry run follows this validation-note update, then the authorized direct push.
