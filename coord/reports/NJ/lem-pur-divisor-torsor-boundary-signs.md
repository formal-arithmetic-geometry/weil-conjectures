# Stage-1 report: lem-pur-divisor-torsor-boundary-signs

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-divisor-torsor-boundary-signs.json: statement, now split in eight steps; not a Mathlib leaf. Its statement and original source are unchanged. Blueprint provenance is made precise and searches are appended.
- citations.json: 25 step/node citations, each quoting the actual statement used.
- report.md, searches.jsonl and write_split.py are sandbox records. Only the item and report enter the delivery.

New nodes: 0. New Mathlib leaves: 0. No unit record needs changing: this is a child of lem-pur-divisor-class, not the unit's key node.

## Attachments

None. Searches of WeilConjectures/ for the exact item id, the literal blueprint tag, relative torsor/cohomology words and torsor-boundary notions found no declaration giving this relative representative and both sign identities. Torsor.lean's nonempty_equiv_H_one_torsor only addresses ordinary H1. The upstream master's sorry declarations were not treated as proved results.

## WANTED

None: all sources used are available locally.

## Corrections and mathematical content

The imported statement is well typed and true; no STATEMENT-DISPUTED correction is needed. The imported node had no proof. The new proof constructs the representative from the extension and specified section, verifies its torsor interpretation, removes the extension and resolution choices, computes the localization minus sign and then the positive composite-boundary identity. The argument uses abelian sheaves throughout, without a finite coefficient or module structure on G.

The current blueprint proof at literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md states clause (a) as cl(f)=boundary(kappa(f)) and invokes the comparison with the line bundle's Chern class at the end. The present node supplies precisely the sign computation needed by that construction. It neither proves smooth purity by a different route nor edits the chapter or unit. The existing parent has already corrected the blueprint's two-function-frame wording for a sum of divisors; nothing about that correction is assumed in this general sheaf calculation.

## Searches and reuse

I read the item, its chapter and sk-prop-a1-kummer unit, all its statement dependencies, and the candidate proof-tool statements. Blueprint searches for relative torsor, torsor and boundary and DAG searches for 03AJ, 013T, 011J, 05TK and resolution-comparison notions found the interfaces now cited. In particular the Zariski-only lem-sc-torsor-h1-boundary-representative was read and deliberately not used for the etale assertion. The reviewed lem-amb-relative-torsor-cohomology supplies the canonical relative bijection and natural connecting maps; it does not state the signs, so those are calculated in this item.

All new Mathlib search queries were executed through msearch.py and recorded verbatim in searches.jsonl. Two semantic phrasings returned ordinary presheaf H1, cocycle equivalence and general homological constructions, not the relative torsor sign assertion. Loogle returned sheaf-H connecting maps and exactness/naturality statements. Its online ExactSequences.lean module is absent from the pinned local Mathlib: I checked the actual pinned SheafCohomology directory, Basic.lean (H', H.equiv0 and H.map) and NonabelianCohomology/H1.lean (H1 and OneCocycle.class), so the online hit was not promoted to a pinned-source match. The first grep found no relative-cohomology/torsor-boundary declarations; the focused second grep found only the Mayer-Vietoris connecting homomorphism, which does not classify a torsor with prescribed section. No missing match or service failure is represented as an unavailable proof.

## Not duplicates

No new nodes were created. The injective extension factorization, the trivial-torsor calculation, finite sums of split rows and the equality of the two (0,-dr) representatives remain arguments in this item, rather than new nodes restating its clauses.

## Review by NJ

I read Stacks sites-cohomology.tex Tag 03AJ, lemma-torsors-h1, including the free-abelian-sheaf pushout, its boundary of 1 and the inverse solution-torsor construction. The relative assertion is not claimed verbatim in 03AJ: its signed refinement is the agent proof here. I also read derived.tex Tags 014E/014F (cone and functoriality), 013T (injective horseshoe) and 05TK (resolution equivalence and the adjoining comparison discussion), homology.tex Tags 0117, 011J and 011K (long exact sequence, split off-diagonal and its agreement with the cohomology boundary), and sites-modules.tex Tag 03CN (kernels and local exactness). I checked each tag against tags/tags. There are no new-node sources to audit.

Step 1 uses the relative-cone definition, the actual derived-category cone/shift and the explicit signed-fibre statement. I checked the chain isomorphism C[1] to Cone(r), (a,b) to (-b,a): its differential is correct and the cone inclusion becomes (0,-b). This is a direct coordinate computation, marked elementary. I did not infer a sign merely from an abstract existence of a triangle.

Step 2 uses the canonical short exact extension expressly included in lem-sc-torsor-h1, the quotient/equivariance maps in def-sc-torsor-extension-presentation and the extension property of an injective object. The differential kills the augmentation because this is a resolution. The epi E_P to Z permits both factorizations. The formula h(s) means h applied to the presentation's jmath(s), made explicit in the proof.

Step 3 uses the resolution's kernel in degree zero and the presentation equivariance. I verified the local inverse on an etale cover trivializing P: x-h(jmath(t0)) belongs to the kernel, hence has a unique G-coordinate. This gives an actual isomorphism of pairs, including the specified section b, not merely agreement after forgetting support. The two components a and b are respectively the extension's boundary cocycle and its specified nullhomotopy on W; these realize the canonical relative refinement of the cited bijection. Translation by a global resolution section has exactly the signed-cone boundary, which is checked in the text. This step constructs its own solution torsor and uses no object existing only inside another node's proof.

Step 4 is elementary factorization through the extension quotient: h'-h factors through Z and gives (dx,res x). No global triviality of P is assumed. Step 5 invokes the full statements of signed-fibre homotopy functoriality and bounded-injective descent, not just a definition of resolution. I checked enough injectives for abelian etale sheaves, the identity exact functor, additive section functors and the natural restriction square. Both given resolutions are nonnegative. Homotopic augmentation comparisons are equal here since the target degree -1 is zero. The image of h is an allowed extension, so the coordinate comparison really sends the representative in this assertion to its counterpart.

Step 6 uses the quotient universal property with the natural equivariant family t to epsilon(t). It produces h with dh=0; this is not an assumed splitting of a nontrivial torsor. It gives (0,g), and the previously computed cone inclusion supplies the minus sign. This is a short elementary specialization and remains a step, not a new lemma.

Step 7 uses the stated nonnegative split horseshoe, enough injectives, the relative connecting-map interface and the explicit split-complex connecting formula. I verified that split sheaf rows remain split on both section groups; ordinary section-surjectivity of an arbitrary epi is not used. The augmented g is a degree-zero cycle. Its lift exists because the degree-zero row splits on W. The equation beta dr=0 and injectivity of alpha identify the unique c, whose cycle equation follows from d squared zero. Both maps are represented by (0,-c); the coefficient boundary is not replaced by an unsigned differential. The text also checks that changing the lift gives D(0,t), a genuine relative boundary.

Step 8 uses the actual etale restriction clause of the cohomology-pullback theorem, componentwise signed-fibre maps, the naturality clauses of the relative torsor theorem, and long-exact-sequence naturality for general complex-sequence morphisms. It does not assume chosen horseshoe splittings are preserved by coefficient maps. The cited statements give naturality on cohomology independently of those choices; step 5 removes the remaining resolution choices. Off-unit general tools are declared in split_report.tool_uses with their purpose; they replace no step of the unit's purity route.

For edge cases I checked W empty (the second component disappears and one recovers the ordinary torsor extension class), W=T (a chosen global section gives the boundary D(h(s)), so the relative class is zero), G=0, g=0, and g extending to G(T) (then (0,g)=D(g)). The coefficient calculation also covers a split coefficient sequence: choose a cocycle lift and both displayed boundary classes are zero. With restriction r=id the signed fibre is contractible, consistent with W=T; no surjectivity of G(T) to G(W) is implicitly assumed. No noetherian, smoothness, finite-order or invertibility hypothesis enters this purely sheaf-theoretic assertion.

I checked delivery-errors B through E against the actual files: no unsupported new nodes, duplicate clauses, changed statement, hidden source lemma, unstated hypothesis or circular use of lem-pur-divisor-class. Each cited statement was opened and the relevant literal passage is in citations.json. All eight proof steps are below 2000 characters; none hides an unrecorded comparison theorem. No second worker or sub-agent was started, under the direct-delivery brief.

## Unfinished work

None in this one-level split. Descendant statements retain their existing DAG status. Server dry run and direct delivery are the remaining mechanical gates.
