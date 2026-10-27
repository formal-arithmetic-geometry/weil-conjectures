## Worker report

Item: lem-per-admissible-modification-valuative-stalks. Group Q52, stage 1, 2026-10-24. Direct delivery after the released Q112 repair order; no earlier sandbox split or report existed.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-modification-valuative-stalks.json: statement, split; seven proof steps, existing interfaces reused; no Mathlib match.
- citations.json: seven step/node entries, each quoting the actual cited statement verbatim.
- report.md: this report and signed review. searches.jsonl contains the six actual msearch.py calls; write_split.py is a sandbox-only construction script and is not a project source or delivery node.

## New nodes

None: 0 new nodes and 0 Mathlib leaves. In particular, the Fujiwara local-ring/stalk input, valuation quotient input and strict-local congruence input already exist and were explicitly re-admitted by Q112. They are cited, not re-created. The remaining injection, topology and approximation arguments are written into steps 3–5 instead of introducing elementary helper nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact item id, admissible modifications and valuative stalks; searched again for the valuative and Zariski–Riemann notions and checked the relevant file names. The results concern properness, compactification and blowups, not the asserted etale cohomology stalk identification. The live item's upstream audit is none. A source declaration containing sorry would not count as an attachment.

## Sources and searches

Read ILO, Travaux de Gabber, XX 4.4, printed pp.373–374 (PDF pp.379–380), including the local-ring paragraph, the fraction-field reduction and the final Note. The source supplies the outline; the explicit separated-quotient, topology, density and exchange-square verification here is marked agent-origin. The independent lower obligations remain at the admitted existing nodes. For the generic cohomology tool read Stacks etale-cohomology.tex, Tag 09ZI, label theorem-gabber: only the affine henselian-pair form is used. Also read Tag 03Q1, label lemma-stalk-pullback, and the torsion-sheaf section 0DDB, and cohomology.tex section-functoriality, lemma-functoriality (01F8), equation-functorial (01FA) and remark-explain-arrow (01FB). No restricted SGA source is cited or used.

Read the six newly logged searches and the four preserved search records. The two LeanFinder phrasings return ordinary etale algebra/morphism results, tilt and valued-field/residue-field constructions; LeanSearch returns ordinary stalk restriction, valued extension and etale topology. None states the item, or specializes to it in one line. Loogle for "HenselianLocalRing", "stalk" and both grep patterns returned no hits. All six current queries and the raw summary records were appended to mathlib_searches; every service responded successfully. No search was invented. No compiler, Lake, Lean writer or build tool was used.

Before writing, searched the whole DAG for admissible blowups/modifications, I-valuative and valued-field stalk statements and henselian/residue-field cohomology comparisons. Opened the existing lower interfaces and their full statements. Whole-blueprint searches with tools/blueprint_refs.py for valuative, admissible, dense embedding, valued and completion found no alternative blueprint node asserting this interface; same_as stays []. The ancestor command confirms lem-per-artin-gabber-affine-curve. Read the latest chapter, unit and ancestor source in literature/blueprint/latest. The current latest ancestor no longer contains the historical proof paragraph recorded in this item's ancestry. Q112 expressly preserves that provenance and independently re-admits this exact interface from ILO XX 4.4, so I preserved the statement, statement dependencies, source and blueprint fields and recorded the precise ILO steps in split_report.blueprint. No chapter or unit record is changed.

## WANTED

None for the argument in this delivery. Proving the admitted unsplit Fujiwara/local-algebra/congruence inputs is separate stage-1 work; this delivery does not pretend to have supplied their proofs or invent text of an unavailable reference.

## What was wrong or missing

The released item has no active proof. Q112 withdrew the old proof and attachments; they are not used as evidence. The missing argument was the assembly from the admitted punctured-local rings to valued fields: injectivity of the separated-quotient map, agreement of the induced topology, explicit density, and the square identifying exchange. These are now explicit. There is no statement dispute or statement correction.

The broader finite-type affine comparison in prop-weil-pbc-gabber-affine-comparison would be inappropriate here. I used the separate correct pair-form prop-weil-pbc-gabber-pair-comparison on the henselian local rings themselves. This is the generic tool declared in split_report.tool_uses, together with inverse-image torsion preservation and cohomological pullback functoriality. The initial DAG traversal found no path from the pair comparison to this item (3190 dependency nodes inspected), avoiding a circular comparison argument; the server checks also test the delivered graph.

## Unfinished work

No part of this one-level split is left as an uncited claim. Its existing unsplit inputs remain independent obligations, as normal for stage 1. This delivery asserts no isomorphism between the two valued-field cohomology groups and does not invoke dense-field Galois comparison or Krasner's lemma.

## Not duplicates

No new nodes, hence no new/existing pairs. All three admissible-modification interfaces needed in this proof are reused by their exact existing ids.

## Review by Q52

I checked the item against ILO XX 4.4 with its source open, rather than interpreting the words "reduces to" as a theorem about stalks by themselves. The item asks for henselian valued fields, not for the punctured-local rings supplied by the first interface, and it also asks for density, topology and a specified exchange arrow. The seven steps account separately for those obligations. No new node requires its own source or small-case audit. The original statement, all eight statement dependencies and the original source/provenance were retained.

In step 1 I read lem-per-admissible-modification-fujiwara-valuative-local in full: it explicitly supplies a conservative family, both nonzero henselian local colimit rings, the compatible local homomorphism, both nonunit nonzerodivisors, the principal-ideal condition, all-degree punctured-local cohomology identifications, and their exchange compatibility. It is not merely a definition of the rings. Thus all hypotheses used in step 2 really are in the cited statement. In particular I did not infer the principal-ideal condition from the word valuative, or assume that arbitrary geometric points have the required property.

In step 2 I read lem-per-admissible-modification-valuative-ring-reduction: its exact conclusion gives prime intersections, henselian local localizations with the specified maximal ideals, henselian valuation quotients, fraction-field identifications and the power-ideal neighbourhood bases. Its hypotheses are exactly the two ring/equation pairs from step 1. Nonzero nonunits in the quotient show the valuations are nontrivial. A field being henselian as a local ring with zero maximal ideal would not suffice: what is used here is henselianity of V and W themselves as valuation rings.

In step 3 I read lem-per-admissible-modification-completion-density. Despite its title it asserts congruences, not density of the fraction fields. The compatible strict-local colimit rings are the same B and C as in step 1; the stated congruences apply to every positive power. I wrote out why P maps into Q and why the preimage of Q is P, so the quotient homomorphism is injective even if B and C are not domains or are not separated. Quotienting the congruences by P and Q is legitimate because each intersection is contained in every displayed power. The field map then follows by the defining fraction-field property. No flatness of the completion map, reducedness of B or C, or excellence was assumed.

In step 4 I read def-trf-valuation-ring, whose either-an-element-or-its-inverse characterization is exactly the one used. The localness descends from the already supplied local map after quotienting by prime ideals contained in the maximal ideals. If an element is outside V, its inverse is in the maximal ideal of V; its image cannot become a unit in W. This proves K intersect W = V and, after division by the exceptional equation, the equality of the basic neighbourhoods. Those are elementary ring calculations, not an uncited valuation-coarsening theorem. Step 5 is the explicit three-line approximation: choose a denominator, lift the numerator modulo the required higher power using step 3, then divide. It addresses any element of K', rather than only elements of W, and uses only the power bases from step 2.

In step 6 I checked the full statement of lem-weil-pbc-inverse-image-torsion for each pullback sheaf, and the full statement of prop-weil-pbc-gabber-pair-comparison against Stacks 09ZI. Henselian local means its maximal-ideal pair is henselian, so both applications are to affine henselian pairs with exactly the closed-point quotient. No coefficient invertibility, Noetherian, finite-type, excellent or discrete-valuation hypothesis is needed. The restriction map in the pair comparison is the canonical pullback, not an arbitrary abstract group isomorphism. The same G is obtained before choosing q, so all degrees have one coefficient sheaf.

In step 7 I read clauses (3) and (4) of lem-weil-pbc-cohomology-pullback-functorial. The ring diagram really commutes by the quotient and localization formulas in step 3. Its inverse-image composition identifications give the exact coefficient h^{-1}G on K'. Its cohomological composition equality is precisely (i')* f* = h* i*, so no unsupported claim that a comparison "transports" the exchange map remains. Coefficient naturality is clause (3), not a deduction from the existence of isomorphisms alone. Every step/node citation has a literal quote in citations.json; there are seven such pairs. All non-elementary inputs are cited statements, and every elementary calculation is given in the proof text. The longest step has 830 characters, so no long step conceals a comparison lemma.

For edge cases, I checked the ordinary henselian DVR case: P=0, V=B, and the construction produces the expected fraction-field inclusion and power-ideal approximation. I also checked the proof with P or Q nonzero; it uses their containment in every power, never cancellation modulo the intersections. It works for higher-rank valuation rings when the exceptional powers are a neighbourhood basis, exactly as the admitted ring-reduction statement asserts, and does not impose rank one. For a zero sheaf the same construction yields zero cohomology; q=0 uses the same canonical maps as positive degrees. If the supplied conservative family is empty, all pointwise assertions are vacuous and the selection of a point is conditional; no nontrivial field is manufactured from the zero ring. No nonzero hypothesis on F or implicit nonempty choice of family was added.

I checked B1–B10 and C1–C8 of delivery-errors.md against the actual files: no new unsplit node with hidden proof, no definitions introduced, no duplicates, genuine logged searches, no excluded source, no use of a cited node's proof instead of its statement, and generic off-unit tools explicitly declared for review. For D1–D5 the proof carries the quotient, topology, density and exchange argument itself; it does not rename the conclusion as a new input. For E1–E7 I verified each hypothesis at the point of application and wrote the fractional approximation and cohomological square explicitly. The corrections during this reading were to use the correct pair-form comparison, retain possible nonzero intersection ideals, and verify the arrow in every degree through the actual functoriality clause.
