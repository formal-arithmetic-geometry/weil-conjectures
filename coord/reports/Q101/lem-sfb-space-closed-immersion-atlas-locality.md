# Q101: lem-sfb-space-closed-immersion-atlas-locality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-immersion-atlas-locality.json: statement item, now split into six proof steps, using existing nodes only. The imported statement and statement dependencies are unchanged. Mathlib has scheme closed-immersion criteria and scheme property descent, but no matching algebraic-space representability criterion.
- citations.json: one verbatim statement quotation for each of the fifteen step/node citation pairs.
- report.md: this report. Searches and the small writing script are sandbox working records only.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id, AlgebraicSpace, algebraic spaces, and the closed-immersion/atlas notions found no project declaration giving this statement. Scheme-only lemmas cannot attach this item. No Lean was written and no compiler was run.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and scope

The item had no proof. Its statement is correct, including representability as a conclusion and absence of quasi-compactness or finite-presentation assumptions. No STATEMENT-DISPUTED correction is needed. I implement the arbitrary-family version directly over each scheme test, using the covering-family forms of the source's descent inputs rather than introducing a coproduct compatibility lemma.

Read AGENTS.md, roles/worker.md, coord/brief-stage1.md, stages/1-dag.md, SETUP.md (including the three authority levels), GOAL.md, the chapter and unit records, the open-stage STATE entry, the delivery-error checklist B–E and tools/README.md. No repair note exists. The item remains unsplit in the read repository before this work. The latest blueprint unit and direct-images statement/proof were read under literature/blueprint/latest/. The item is a supporting geometric lemma in its inherited long ancestry, not a replacement of the unit route. blueprint_refs ancestor returns null for this existing item; its inherited detailed place and via chain are retained. Whole-blueprint searches for closed immersion, 03I0, effective descent and descent data found no statement identical to the item.

## Not duplicates

No new node was created. I considered the closed-immersion scheme effectivity lemma (Stacks 03I0), searched it through all four Mathlib search modes with two semantic phrasings, and then discarded that proposed node: the already existing lem-trf-separated-lqf-fppf-effective-descent supplies effectivity once separation and local quasi-finiteness are verified. That verification is an elementary proof step. The searches remain recorded, and are not represented as searches for a nonexistent delivered node.

The existing lem-pc-descent-finite-flat-closed-subschemes, which shares 03I0, requires a finite locally free degree and a specified ambient scheme, so it cannot be applied here. lem-trf-space-closed-immersion-cover-descent assumes representability in advance; it does not solve this item. lem-sfb-space-descend-closed-immersion concerns descent to a finite stage of an inverse limit; its similar name does not state atlas locality. lem-sfb-space-affine-locality concerns affine morphisms, not the closed-immersion property. No duplicate node was introduced for any of them.

## Review by Q101

I read the item source, spaces-morphisms.tex Tag 03M4 (lemma-closed-immersion-local), in particular its proof of (4) implies (1). That proof first obtains representability by effective scheme descent and only then descends the scheme property. I also read the cited general mechanism in spaces.tex, lemma-morphism-sheaves-with-P-effective-descent-etale; descent.tex Tag 02W5 (lemma-descent-data-sheaves); more-morphisms.tex Tag 02W8 (lemma-separated-locally-quasi-finite-morphisms-fppf-descend); descent.tex Tag 02L6 (lemma-descending-property-closed-immersion); topologies.tex Tag 022C (lemma-zariski-etale-smooth-syntomic-fppf-fpqc); and the elementary closed-immersion argument in morphisms.tex, lemma-immersion-locally-quasi-finite. The unused 03I0 source was also read. No SGA source is used.

For step 1 I opened lem-trf-space-fibre-products-etale-covers: its statement explicitly provides scheme pullbacks of representable etale charts and preserves joint surjectivity. The definition nodes def-weil-etale-morphism and def-pc-fppf-site give precisely flatness, local finite presentation, and the covering criterion. def-trf-algebraic-space says E and Y are fppf sheaves and defines representability. The fibre sheaf condition is proved explicitly by gluing E-sections and checking their Y-images. This does not assume that E times_Y T is already a scheme.

For step 2 I opened lem-weil-pbc-closed-immersion-base-change, which states exactly that a closed immersion remains one under an arbitrary scheme base change. The base change here is T_i to U_i; its source is W_i=Z_i times_{U_i} T_i. The functor-of-points identification with F restricted to T_i is written with all coordinates. I opened lem-trf-fppf-sheaf-representability-descent-data: its statement supplies the scheme comparison isomorphisms and their cocycle, not merely fully faithful Yoneda. It applies because the family in step 1 is fppf, all schemes lie in the stipulated universes, and the local representatives have been exhibited.

For step 3 I opened lem-weil-pbc-closed-immersion-integral-separated-uc and used only its explicit clause (a). I checked the quotient criterion in def-weil-closed-immersion, the isolated-fibre definition in def-weil-pbc-ring-map-quasi-finite-at-prime, and the affine-local definition in pqf-def-quasifinite. The explicit two inverse tensor maps identify the fibre of R to R/J at a prime containing J with its residue field. The singleton spectrum is isolated and R/J has zero algebra generators. Thus local quasi-finiteness follows without assuming J finitely generated; finite presentation is neither needed nor inferred. This calculation is elementary and does not deserve a new node.

For step 4 I opened lem-trf-separated-lqf-fppf-effective-descent. Its statement is the covering-family theorem, and it expressly does not assume quasi-compactness or local finite presentation of the morphisms being descended. The required separation and local quasi-finiteness were established in step 3. I then used the final representability-if-and-only-if-effectivity clause of lem-trf-fppf-sheaf-representability-descent-data, not a construction hidden in its proof. Its statement gives the local base-change identifications of the descended scheme.

For step 5 I opened lem-trf-fppf-covering-is-fpqc and lem-pc-fpqc-descend-closed-immersion. The first applies to the whole family, not only a singleton or a globally quasi-compact atlas. The second requires a scheme morphism; only now, after step 4, is that hypothesis available. Its base changes are exactly the W_i to T_i of step 2. Step 6 is the definition of a representable transformation from def-trf-algebraic-space, for the arbitrary scheme test T fixed at the start. No choice of compatible representatives across different T is required by that definition.

I checked B–E against the files: no new statement-only node or hollow definition was needed; every non-elementary fact is a cited node whose statement was opened; all citations have full verbatim statement quotations; the proof carries the argument rather than passing the whole conclusion to a renamed lemma; and no cited dependency reaches this item (a read-only traversal confirmed this). The off-unit geometric descent tools are declared in split_report.tool_uses with reasons; they realize the source proof's generic tools. Every step is under 2000 characters.

Edge cases checked: empty T; the empty atlas family (joint surjectivity then forces every test T to be empty); empty E and empty local closed subschemes; identity closed immersions J=0; nonreduced bases; ideals J not finitely generated; infinitely many atlas members; and non-separated bases or spaces. Quotient fibres at points of the source are fields even when J is not finitely generated. Both family descent theorems allow arbitrary families, so none of these cases requires an added hypothesis. I corrected no source statement; the only implementation choice was to reuse the existing more general effective-descent theorem instead of making a redundant 03I0 node.

## Unfinished work

No mathematical part of this stage-1 split remains. The required server dry run and direct push follow this report; the delivery tool's output is the authority for delivery status.
