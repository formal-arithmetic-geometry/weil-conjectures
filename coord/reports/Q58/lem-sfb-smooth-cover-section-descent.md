## Worker report

Item: lem-sfb-smooth-cover-section-descent. Group: Q58. Stage: 1. Date: 2026-10-23.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-smooth-cover-section-descent.json, with a five-step proof and the original statement unchanged; citations.json, containing one verbatim statement extract for every step/node citation. The sandbox also contains searches.jsonl and a local writing script. No Lean file, repository file or launcher file was written, and no compiler or build was run.

## New nodes

None. The smooth base-change fact already has lem-sfb-stack-smooth-permanence. Smooth implies flat and locally of finite presentation already has the Mathlib leaf lem-pc-smooth-flat. The remaining argument is the sheaf equalizer axiom with its local elements and restriction maps written explicitly. Creating separate statements for its gluing, naturality or uniqueness clauses would only rename elementary parts of this item.

Mathlib leaves created: 0. Attachments: none. Searching the upstream WeilConjectures source for the blueprint tag and for algebraic stacks, smooth atlases and section descent produced scheme/sheaf descent results, not this statement on arbitrary algebraic stacks. In particular the existing modules for scheme module descent do not supply this stack-cover conclusion.

WANTED: none.

## Sources and searches

Read Stacks stacks-sheaves.tex, Tag 076S (lemma-map-from-quasi-coherent), including its exact source-module quasi-coherence hypothesis and its arbitrary target-module hypothesis, and Tag 06WV (lemma-quasi-coherent-algebraic-stack)(1). These explain the imported source description: compatible chart maps descend, and maps from the structure module give sections. Because the live coefficient definition explicitly uses the big fppf site and precomposition, the proof can spell out the simpler underlying sheaf argument, rather than introducing an equivalence with a quotient groupoid. I read the inherited topology and sheaf definitions, Tags 06TP (definition-inherited-topologies) and 06TR (definition-sheaves), and Sites Tags 00VH, 00VM (definition-sheaf-sets), 00VR, including the empty-cover paragraph immediately after 00VM. I also read smooth flatness and local finite presentation in morphisms.tex, Tags 01VF and 01VE, and the smooth base-change statement in stacks-morphisms.tex, Tag 075W. The assembly proof is marked agent-written: it is an explicit argument from these definitions, not a claim that Tag 076S literally states the item.

The sandbox search log records all six searches made in this session, and their hits were read. Two semantic phrasings were used. The first leanfinder query returned sheafed-space gluing and scheme-open-cover results. LeanSearch and the second leanfinder query returned CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section and CoversTop.sections_ext. I read Mathlib/CategoryTheory/Sites/CoversTop/Basic.lean: these require a CoversTop family and compatibility for all arrows to its objects. The geometric covering condition and the translation from algebraic-space relations to all these arrows still need the present proof. Loogle returned the equalizer sheaf-condition declarations, which similarly presuppose an actual covering. The two grep searches found only unrelated manifold atlas lines for the geometric query and the general CoversTop machinery for the categorical query. Thus this item is not an exact Mathlib theorem or a one-line specialization. Existing item searches are retained, with only actually logged new queries appended.

Searched the whole DAG for 076S and 06WV, for smooth covers, section descent and fppf covering calculus, and read the candidate statements. The affine-groupoid and flat-affine-action algebra-descent statements have affine/presentation hypotheses, and the smooth-image statement concerns images of algebra morphisms; none states the item. The generic geometry needed here already exists and is reused. Whole-blueprint searches with blueprint_refs.py for quasi-coherent, sections, 076S and smooth cover revealed no exact duplicate. No new node is proposed.

## Blueprint and route

Read GOAL.md, the three levels in SETUP.md, the chapter and unit records, and the current latest blueprint unit sk-thm-sf-ctf-stability and its direct-images proof. This auxiliary lemma serves the inherited chain from direct-images proof (3), through stable-curve moduli and adequate algebra pushforward. In particular its parent uses it only to glue compatible powers after choosing a smooth scheme cover. The proof stays below the unit; it does not alter the constructibility/direct-image route. No unit record is changed, since this item is not a unit's key statement.

blueprint_refs.py ancestor returns None for this existing node, agreeing with the live blueprint.from.node = null. Its long from.place and via chain already identify the intended ancestor and use. These inherited fields are retained; same_as is [] after the whole-blueprint search. The split_report records which parent argument the proof supplies. No maintainer metadata was repaired or guessed.

## Not duplicates

No new-node/existing-node pairs: no new node is created.

## Review by Q58

I checked the unchanged statement against 076S and 06WV(1), but used their big-fppf sheaf setup to give the section argument directly. The two important hypotheses are that representable smooth maps remain smooth after each scheme test and that joint surjectivity is required after each such base change. Neither step needs the relation spaces to be schemes, nor any cover member to be affine or quasi-compact. Quasi-coherence is part of the item but is not needed beyond the existing assumption that this algebra is a sheaf on the big fppf site. This does not change the statement or the coefficient convention.

Step 1 uses the actual global-section and precomposition clauses of def-sfb-stack-quasi-coherent-algebra and the explicit triples in def-sfb-stable-pointed-moduli-groupoids. Evaluation at the identity on a scheme and subsequent restriction are inverse directly from the compatible-family definition. For two arrows from a scheme object to chart objects, the triple retains the isomorphism between their images in the stack; pulling the overlap equality back along that triple gives equality in the one common value of C. I checked that i=j is included, so invariance under automorphisms is not omitted.

Step 2 uses exactly the arbitrary-base-change clause of lem-sfb-stack-smooth-permanence, not a definition node purporting to prove base change. The item hypotheses make each scheme-test pullback an algebraic space. def-trf-algebraic-space actually supplies a surjective etale scheme chart. Since the space projection is smooth as tested on these charts, its chart composite to T is a smooth scheme map. The statement of lem-pc-smooth-flat gives both flatness and local finite presentation, so def-pc-fppf-site then declares this jointly surjective family a covering. The big-site definition of def-sfb-stack-quasi-coherent-algebra declares the resulting arrows a cover of x. This checks every step from a representable smooth cover to a cover on which the sheaf axiom can actually be used, with all chart choices in the given universe and no finite-subcover assertion.

Step 3 applies the precise equalizer in def-weil-pbc-sites-and-cohomology to the underlying set sheaf explicitly required in def-sfb-stack-quasi-coherent-algebra. It first writes the local elements, checks their restrictions using step 1, and glues them. Independence is proved on the actual pairwise scheme fibre products of two chosen covers, using the base-change/composition axioms and the injective part of that same equalizer. These are applications of the definitions, not an unquoted descent theorem or a second lemma with its own hypotheses.

Step 4 checks an arbitrary arrow y to x, including a non-smooth underlying scheme map and an automorphism over an identity. The base-change axiom in def-weil-pbc-sites-and-cohomology applies to every such arrow. On the pulled-back cover, functoriality makes the restricted s_x the same local family defining s_y; step 3's uniqueness and independence give their equality. The identity cover computes s at each x_i as c_i. Thus the constructed data are compatible over the whole big site, rather than merely sections of individual chart restrictions.

Step 5 checks uniqueness object by object on the same fppf covers, using the injective half of the equalizer. The algebra definition says restrictions commute with all ring operations and global operations are pointwise, so the bijective restriction map is the claimed ring isomorphism. Naturality follows from the defining restriction maps and uniqueness of their inverse. This also supplies the equality-detection clause explicitly.

I checked small cases: the identity cover of a scheme; repeated charts (where the same-index relation forces the needed invariance); a stack with stabilizers (arrows and their 2-isomorphisms are retained); empty chart members; an empty index set; and arbitrary infinite, non-quasi-compact covers. In the empty-index case every object lies over an empty scheme and the empty fppf cover forces a singleton value, including the one-element section ring. There is no characteristic restriction, Deligne--Mumford assumption, finite presentation of C or noetherian assumption. All five steps are shorter than 2000 characters, and no inline comparison lemma is hidden in them. There are no new statements needing B1--B7 checks, no cycles through new dependencies, and no off-unit non-Mathlib statement tool: smooth permanence has the item's unit and smooth-flat is already Mathlib.

I corrected the source tag for definition-sheaves from a provisional 06TQ to the actual 06TR after checking tags/tags, and tailored the citation extracts to the covering and underlying-sheaf clauses actually used. No statement dispute or mathematical correction was needed. The required server checks and delivery dry run follow this review.

## Unfinished work

No mathematical part left unfinished. Stage-1 delivery leaves the pre-existing dependencies at their existing statuses; it creates no new obligations beyond the already present smooth-permanence node.
