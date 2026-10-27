# Stage-1 report: lem-trf-divisorial-section-chart-factorization

## Files written

- dag/nodes/sec-trace-formula/lem-trf-divisorial-section-chart-factorization.json: statement, now split into four steps; no Mathlib match.
- citations.json: eight verbatim statement quotations, one for every cited dependency of every step.
- report.md: this report. searches.jsonl is the search command's actual log; write_split.py is sandbox-only preparation code.

No new nodes and no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint id and for divisorial, LogStructure, log regularity and monoid charts. The only divisorial hit concerns a line-bundle Riemann–Roch section, which does not state this lemma. The existing Sheaf log-pair definition is a definition, not an attachment proving the item.

## WANTED

None. I read the available ILO PDF directly by pdftotext, physical pages 75–77, printed pages 69–71. No download was needed.

## Corrections and source audit

The statement is unchanged. The imported node had no proof. I supplied the membership argument and the actual finite-list argument, rather than citing the single h = epsilon a sentence as though it already supplied global units and a common neighbourhood. I explicitly represented inverse units as well as units and forced their products to equal 1 on the final neighbourhood.

The inherited Mathlib searches from Q113 remain verbatim, including the service-unavailable verdict. Five fresh searches appear exactly as logged: LeanFinder with two different semantic phrasings, LeanSearch, Loogle "LogStructure", and grep LogStructure|divisorial|log.regular|logarithmic in AlgebraicGeometry. I read all signatures returned. Standard etale presentations concern representing ring elements after powers of a localization denominator. The structure-sheaf fraction and localization hits have no fs log structure or chart. The second LeanFinder phrasing returned ordinary stalk and local-ring properties, not logarithmic chart factorization. The grep hit is an elliptic-curve height comment. These are no match, not Mathlib leaves.

I searched the whole DAG for chart factorization, divisorial functions and stalk representatives, and ran blueprint_refs.py ancestor plus searches divisorial, chart, monoid, stalk data, divisorial section and monoid chart. There is no equivalent blueprint item. The existing lem-trf-finite-monoid-stalk-data-spreading contains precisely the finite-elements, finite-equalities and restriction-stalk statements needed here; it replaces any temptation to create a duplicate spreading lemma. The sharp-chart lemma is stronger than needed and not used; the divisorial-structure lemma proves an identification which is already part of our hypothesis definition. No new node is needed for the product-quotient description of a commutative-monoid pushout: that calculation is written out in step 3.

The chapter record and unit record were read. The newest blueprint is main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345. I read its sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md. Its present contracting-correspondence route differs from the older ancestry that created this local log-geometric auxiliary. This delivery proves the still-live requested auxiliary by its recorded ILO source; it makes no assertion that logarithmic chart factorization replaces the contracting-correspondence theorem and changes no chapter, unit or target. The blueprint.from place and via retain that historical explanation.

## Not duplicates

No new nodes were created, so there are no new/existing pairs with a shared source tag to distinguish.

## Review by Q136

I checked B–E with the actual statements and source text open. For the item, ILO VI 1.1 defines fs structures by etale-local fs charts, 1.4 gives the sectionwise divisorial structure, and the proof of Proposition 1.9 on printed p. 71 writes h = epsilon a after h belongs to the log structure. The finite list and its single neighbourhood require additional reasoning; they are not quoted as a separate assertion of ILO. Accordingly proof_origin is agent. I read Stacks etale-cohomology.tex lemma-cofinal-etale (03PQ), lemma-geometric-lift-to-cover (03PR), definition-stalk and its immediately following representative/equality description (040R), and categories.tex lemma-directed-commutes (002W). No SGA source is used.

Step 1 uses the exact sectionwise clause of def-trf-log-regular-pair: a regular function invertible on the pulled-back open is a log section. This is a direct application of the definition, not a theorem identifying an arbitrary log structure with a divisorial one. The hypothesis on each h_i is exactly what it needs.

Step 2 uses the fs-chart clause of that definition and the family-lifting statement of lem-weil-pbc-etale-cover-geometric-point-lift; I checked that the latter preserves the same Omega, not merely a larger geometric field. The covering is etale and jointly surjective by the etale-local meaning of the chart condition. Lem-weil-pbc-etale-composition-cancellation explicitly states composition of etale maps. Lem-trf-finite-monoid-stalk-data-spreading explicitly identifies restriction stalks with the original geometric stalk; it is applied on base Y, which is locally Noetherian by hypothesis, and with the chosen pointed etale neighbourhood W. Thus I do not silently assume a new local-Noetherianity hypothesis on V or W.

Step 3 uses the chart pushout formula of def-trf-log-regular-pair, which I read in full. The quotient of P times A-units has a representative (a,u) for every class, because a product of such pairs is again one pair. No integrality, cancellation, sharpness, or chosen splitting of the characteristic monoid is required for this surjectivity. The pushout relations are written explicitly. The unit's inverse exists by its definition. These are elementary calculations, so I have not made them new nodes restating a clause of the item.

Step 4 uses exactly the existing spreading node's general finite sheaf-of-sets clauses, not its separate monoid-Hom finite-presentation theorem or the proof of that theorem. The structure sheaf on the small etale site is the sheaf already used in the divisorial log definition. I use 2r ring-stalk elements, then finitely many equalities in that ring sheaf. Their germs agree by step 3 and functoriality of restriction/multiplication. The equations e_i d_i = 1 show that the representatives really are global units; merely representing a unit germ would not suffice. The factorization equalities and inverses survive every subsequent restriction. The spreading node states compatibility of the restriction-stalk identification with sections and refinements, so the restricted chart has the same pushout condition at every geometric point. Etale composition and the pointed nature of every refinement preserve the required map and lift. All citations have verbatim quotations in citations.json. There is no hidden smallness assumption introduced here: the cited spreading statement already states the small filtered skeleton it uses.

Small cases checked: r=0 leaves only a pointed fs chart, with no unnecessary unit choices; a trivial boundary reduces to units and may use the trivial monoid; h_i=1 can use the identity chart element; repeated h_i impose no incompatible choices; a germ in a non-sharp fs chart still has a product representative, so sharpness is unnecessary. The geometric point rules out an empty final neighbourhood. Zero cannot be a unit on a nonempty trivial locus; the proof does not use a cancellation inference from h_i or assume that h_i is a nonzerodivisor. No new hypotheses or conclusion changes were made. Every proof step is under 2000 characters, and the only non-elementary inputs are existing nodes, whose actual statements were checked. There are no off-unit non-Mathlib tools; the spreading node is in sk-i-curve-zero and the other nondefinition inputs are Mathlib leaves.

## Unfinished work

None at stage 1. Independent maintainer review is the normal next stage after direct delivery.
