# Stage-1 report: lem-trf-integral-codimension-one-affine-neighbourhood

Group Q106; 2026-10-23. Stage 1 only. No Lean files written, no compiler invoked, no repository or launcher files changed.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-codimension-one-affine-neighbourhood.json`: item, split into six proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-one-dimensional-subrings-common-dvr-criterion.json`: statement; no Mathlib match; Stacks 09N0, varieties-lemma-glue-separated, in Situation 09MY.
- `dag/nodes/sec-trace-formula/lem-trf-semilocal-subring-affine-gluing.json`: statement; no Mathlib match; Stacks 09N4, varieties-lemma-glue-a-bunch-of-local-rings, together with the local-ring consequences explicitly used in 09NJ.
- `dag/nodes/sec-trace-formula/lem-trf-affine-source-stalk-isomorphism-neighbourhood.json`: statement; no Mathlib match; Stacks 09NI, varieties-lemma-points-in-affine.
- `citations.json`: verbatim statement quotations for every cited node in every numbered proof step.
- `searches.jsonl`: actual msearch log. `write_split.py`: sandbox-only JSON assembly helper.

All three new nodes have complete statements and empty proofs and proof dependencies. Their Noetherian, dimension, spectrum, tensor, generic-point and immersion notions cite existing definitions or are explicitly explained inline. The new algebraic nodes are genuinely different inputs to the geometric construction, rather than restatements of its affine-neighbourhood conclusion. The 09NI node works for a different input, an arbitrary affine-source morphism satisfying precise generic-point and stalk conditions; constructing that input from the original finite set occupies Steps 1–5.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact blueprint id, 09NJ, codimension-one affine neighbourhoods and finite sets in affine opens found no declaration proving this item. The generic-point affine-neighbourhood results and quasi-projective results have different hypotheses. Existing project declarations are reference material only when their proofs contain sorry. Existing DAG nodes for stalks in the function field, affine bases, canonical local-spectrum morphisms, valuative uniqueness, morphism gluing and separated-implies-quasi-separated are reused.

## WANTED

None. All sources needed here are present in `literature/stacks-project/`.

## Findings and changes

The item was unsplit; its statement is exactly Stacks 09NJ. No repair note or previous sandbox split/report was found. I retained its statement, source, existing searches and blueprint lineage. I read the chapter and unit records, the three blueprint levels in SETUP, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. This auxiliary sits below the inherited finite-pinching/contraction chain; it does not change the chapter or unit argument or any target. No same-as blueprint node was found by blueprint_refs searches for the relevant tags, affine neighbourhoods, intersection of local rings, local-ring isomorphisms, and codimension, supplemented by text searches in the latest blueprint.

The source suppresses two boundary reductions. Its algebraic gluing lemmas assume dimension exactly one and a nonempty family, while the item allows dimension zero and the empty set. Step 1 removes the generic point, proves that every remaining selected point has dimension exactly one, and handles an empty remainder separately. Every nonempty open of the integral scheme contains the generic point, so it can be restored at the end. The item is true unchanged; there is no statement dispute.

The source also moves directly from no valuation dominating both local rings to the tensor-surjectivity criterion, whose actual statement supplies a DVR *containing* both. Step 2 supplies the missing justification: a DVR containing a local dimension-one domain with common fraction field contracts its maximal ideal either to zero or to the unique nonzero prime; zero would invert every nonzero element of the domain and make the DVR the whole fraction field. Hence the inclusion is local, as required for both centres to be the selected points.

The new 09N4 node states the source's general semilocal theorem and its local-ring consequences used by 09NJ. The local consequences follow from an open immersion preserving local rings, a one-dimensional local domain having exactly its zero and maximal prime, and each closed point lying in exactly one chart. The open overlaps therefore have only the generic point and are the specified spectrum of the fraction field. These consequences are kept in the same source theorem statement so later work cannot mistake a purely topological overlap for the scheme-theoretic one needed to glue morphisms.

## Mathlib searches

Each new node was searched with leanfinder, loogle, grep through msearch, and leansearch; each was also searched using a second natural-language phrasing. All actual responses were read. The item was searched again under Q106 with a second formulation as well. Exact query strings and logged response summaries are in the node records and searches.jsonl. The loogle query `IsNoetherianRing, IsSemilocalRing` had an unknown identifier, which is recorded as an invalid pattern, not evidence of absence; I followed it with a valid quoted Noetherian/Subring/inf query and additional semantic and grep searches. No service was unavailable.

For 09N0, returned DVR characterizations, valuation extension/exclusion lemmas and general tensor surjectivity statements do not compare the image of the joint tensor map with existence of a common DVR. For 09N4, the finite-coproduct affine theorem treats disjoint unions, while scheme GlueData constructs a scheme without proving this gluing affine. I read Mathlib/RingTheory/LocalProperties/Semilocal.lean: its Noetherian criterion assumes a ring with finitely many maximal ideals and already specified maximal localizations; it does not construct the intersection or its covering. For 09NI, the affine basis treats one point, and the returned spreading-out results impose finite-type hypotheses and do not give this simultaneous affine-neighbourhood conclusion. I read the returned FunctionField, AffineScheme arrowStalkMapIso, and SpreadingOut contexts. The FunctionField hits are exactly the reason to reuse the existing stalk/fraction-field leaf. The item hits likewise cover one-point neighbourhoods, affine covers, or stronger Noetherian assumptions, not the item.

## Not duplicates

lem-trf-one-dimensional-subrings-common-dvr-criterion vs lem-trf-integral-codimension-one-affine-neighbourhood: the new node is the purely algebraic 09N0 equivalence for two arbitrary subrings of a field; the item is the geometric common-neighbourhood theorem. The shared 09NJ reference merely records where the algebraic theorem is applied.
lem-trf-semilocal-subring-affine-gluing vs lem-trf-integral-codimension-one-affine-neighbourhood: the new node is the 09N4 construction for arbitrary semilocal subrings satisfying pairwise tensor surjectivity; it mentions no ambient X or selected points. Steps 1–3 establish its hypotheses and Steps 5–6 convert its ring construction to the required open of X. The shared 09NJ tag identifies the source of its local-chart consequences.

lem-trf-one-dimensional-subrings-common-dvr-criterion vs lem-sc-separated-affine-function-field-surjective: the existing node starts with an affine open of a separated integral scheme and a point outside that open; the new node concerns arbitrary subrings in a common fraction field and gives the equivalence with a common DVR. It cannot be obtained by specializing the existing geometric statement.
lem-trf-one-dimensional-subrings-common-dvr-criterion vs lemma-nagata-local-domain-valuation-dominates: existence of a dominating valuation for one local domain does not assert existence of a discrete valuation overring containing two subrings or its tensor-surjectivity equivalence.
lem-trf-semilocal-subring-affine-gluing vs lem-sc-semilocal-dedekind-dvr-reduction: the existing node localizes an already given semilocal Dedekind domain; the new node constructs an affine gluing ring from independent, possibly nonnormal, one-dimensional semilocal domains.
lem-trf-affine-source-stalk-isomorphism-neighbourhood vs lem-trf-integral-codimension-one-affine-neighbourhood: the new node assumes an affine-source morphism, stalk isomorphisms and generic-point compatibility, without codimension, Noetherian or integrality hypotheses; the item constructs precisely that morphism using its different hypotheses.
lem-trf-affine-source-stalk-isomorphism-neighbourhood vs lemma-nagata-affine-neighbourhood-generic-points-exists: the existing node covers one arbitrary point and component generic points, whereas the new node covers finitely many image points with an affine-source witness. Neither selected image point is required to be generic.

No existing node with source tag 09N0, 09N4 or 09NI was found. Whole-DAG searches by tags, labels and the subring/intersection, semilocal, valuation and stalk-isomorphism concepts supplemented the blueprint searches. New ids were absent before creation. None of the new statements is an elementary two-line observation, and none replaces the whole proof of the item.

## Review by Q106

I read 09NJ's statement and complete proof in varieties.tex, 09N0 and its proof, Situation 09MY, 09N4 and its proof, and 09NI and its complete proof. I checked the tags against stacks-project/tags/tags: 09N0, 09N4, 09NI and 09NJ have exactly the recorded labels; 09MY is the subring situation. I also read Schemes 01KZ and its proof and the local-ring/function-field discussion preceding Morphisms' lemma-distinct-local-rings. No SGA source is used. The new nodes remain statement-only: source proofs and the construction explanation are not placed in their statements.

Step 1 uses the actual statement of lem-sc-integral-scheme-stalks-in-function-field: the stalks are domains embedded in the generic stalk with that fraction field, and the generic point lies in every nonempty open. The canonical-morphism node expressly identifies its image with all generalizations of the selected point. The Krull-dimension definition gives the strict prime-chain argument, and the affine-basis node supplies the affine neighbourhood in the empty-remainder case. The remaining deductions are explicitly elementary. I checked that a zero-dimensional domain cannot have a nonzero prime and that the integral scheme is nonempty.

Step 2 uses the DVR definition, the same dimension definition, the canonical-morphism node's closed-point image clause and lemma-nagata-separated-valuation-lift-unique. I opened each statement; the uniqueness lemma allows the separated structure morphism and any valuation ring with fraction field K, with no properness or finite-type assumption. A DVR is a valuation ring and is not a field as the cited definition says. The inclusions are local by the argument written in the step, so the same closed point really maps to both x_i and x_j. Agreement on the generic spectrum is induced by the same embeddings in K, not just agreement of underlying points.

Step 3 cites exactly the newly stated 09N0 equivalence. Its A_i is Noetherian, has dimension one, and both subrings have fraction field K. Step 2 rules out the precise containing-DVR alternative; there is no change from domination to containment left unjustified.

Step 4 cites exactly the new 09N4 statement. The family has r at least one, each local ring is semilocal, and Step 3 gives every ordered pair's surjectivity hypothesis. The node explicitly supplies open immersions, the covering, closed-point localizations and scheme-theoretic overlaps with their prescribed K maps, so the step does not take information from a hidden proof.

Step 5 uses the canonical-morphism node and the scheme-morphism-gluing node, whose actual statement gives existence with the prescribed restrictions and uniqueness from overlap agreement. The overlap statement comes from Step 4. I checked the restrictions via affine germ maps, hence they are equal as scheme morphisms. The canonical node explicitly states that the normalized closed stalk map is the identity and the closed point maps to x_i. Open charts identify the stalk at m_i with that closed stalk. Since A is a domain with fraction field K, the generic point maps to eta and both generic-point sets are singletons.

Step 6 cites the existing separated-implies-quasi-separated Mathlib leaf, whose statement gives exactly the needed implication, and the new 09NI statement. The affine source is Spec A, X has exactly one component because it is integral, and Step 5 checked both the generic-point injection and all induced stalk isomorphisms. The resulting open is nonempty because r is positive, so restoring eta is justified. No hypothesis of global Noetherianity or finite type on X has been added.

Edge cases: T empty and T containing only eta are handled before invoking any gluing theorem; r=1 has no pairwise conditions and uses the local ring itself; distinct height-one points on Spec Z give the expected semilocal localization of Z; two distinct closed points on an affine line work similarly. A nonnormal one-dimensional local domain is allowed, so I did not assume DVR or normality for any A_i. The common-DVR criterion allows A=B, where the tensor map is not onto unless the ring is already a field; the gluing hypothesis excludes that repeated local dimension-one chart. The general gluing node assumes r positive, avoiding the false dimension-one claim for an empty intersection. The affine-source criterion does not assume that f is an open immersion, flat of finite presentation, or finite type.

I checked delivery-errors B–E against the actual files: definitions and hypotheses are stated, sources have verified tags and labels, no new node contains a proof, every non-elementary input has a node citation, and every citation has a verbatim quote in citations.json. Off-unit nonleaf canonical-local-spectrum use is declared in split_report.tool_uses as a generic scheme tool; all the other reused off-unit results are Mathlib leaves or the Lean-closed valuative uniqueness node. There is no dependence of the new nodes on the item, hence no introduced circular proof. No step is longer than 2000 characters (the maximum is 1056). The corrections made in this review were the explicit dimension-zero/empty-family reduction and the containment-to-domination argument described above.

## Unfinished work

No omitted argument remains in the item's assembly proof. The three named new source theorems are intentionally unsplit queue items, as required by one-level splitting. Server preflight and final delivery results are recorded below when obtained.
