# Q66: lem-sfb-coefficient-heart-curve-complement

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-heart-curve-complement.json`: existing statement node split in seven steps; not a Mathlib leaf. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each node cited in each proof step.
- `report.md`: this report. Existing sandbox scripts and searches.jsonl are retained as interrupted-work records; they are not DAG additions.

## Attachments

None. Searched the live project under lean/WeilConjectures for the exact blueprint id and for coefficient-heart, curve-complement, localization and open/closed exact-sequence names. The open/closed library results found concern etale sheaves, rather than all internal modules over an arbitrary commutative condensed coefficient ring on the pro-etale site together with the geometric assertions. No project declaration found states the whole item under its hypotheses.

## WANTED

None. The blueprint and supporting Stacks sources are available locally.

## Corrections and source comparison

The source field inherited from the item points to sk-lem-coefficient-heart.proof.md and calls this its final curve paragraph. In the current snapshot that paragraph is actually at the end of sk-lem-coefficient-heart/_section.md; the proof file ends with the general filtration argument. The proof_origin and per-step sources name the actual location. The item's statement is sound and is retained verbatim. Its extension assertion follows from the ring-object localization theorem; no constructibility assumption on F or restriction of Lambda to E or Qlbar is needed for that assertion. The lisse hypothesis enters only the last interpretation.

The interrupted sandbox already contained the split and logged searches. I compared it with the live unsplit item and retained its proof and search history. I did not rerun finish_report.py: its edits had already been applied to the node. I completed the missing report and added the missing dimension-definition and Grothendieck-sheaf citations to citations.json. The server review_split check passed before the report was written.

## Unfinished work

No part of the one-level split is left unfinished. Cited unsplit nodes remain their own items; none is silently treated as a proved Lean declaration. This is stage 1 only: no Lean file was written and no compiler or build command was run.

## Mathlib and blueprint searches

Read the retained searches.jsonl and all recorded results. The Q66 searches use two semantic phrasings, the qualified Loogle query AlgebraicGeometry.IsNoetherian, Topology grep for finite_compl|topologicalKrullDim|openClosed|open_closed, CategoryTheory/Sites grep for proetale|ProEtale|lowerShriek|extensionByZero, and two LeanSearch queries. The hits concern algebraic module localization, structure-sheaf sections, rank loci or Noetherian topology, not the full internal-coefficient localization and finite-complement statement. The unsuccessful/rate-limited searches inherited from the original item are retained with their original unavailable or unusable verdicts. No unrun search was added.

The whole-blueprint searches for curve complement and finite closed points found no exact imported duplicate. blueprint_refs ancestor identifies sk-lem-coefficient-heart. The item's blueprint.from.place identifies the final curve paragraph; same_as remains empty. The current chapter and unit were read: the proof implements the stated open/closed exact-sequence route, with geometric finiteness and scalar identifications made explicit.

## Not duplicates

No new nodes were created. Existing lem-sc-zero-dim-noetherian-closed-finite and lem-sf-ring-sheaf-closed-localization supply the two substantive tools instead of making special-case copies.

## Review by Q66

I read coord/delivery-errors.md B through E, the current chapter and coefficient-heart unit, the curve paragraph in the current blueprint _section.md, and its proof file. For geometric input I read Stacks schemes.tex lemma-reduced-closed-subscheme (01J3), properties.tex lemma-Noetherian-topology (01OZ), lemma-locally-Noetherian-quasi-separated (01OY), lemma-locally-Noetherian-dimension-0 (0AAX), and topology.tex lemma-Noetherian-quasi-compact (04ZA). For the sheaf assertion I read proetale.tex lemma-ses-associated-to-open (09AH) and the existing ring-sheaf proof at sec-smooth-purity/sk-prop-sf-closed-unit/det-sf-open-closed-sequence-ring-sheaf.proof.md. I read the coefficient-morphism, pulled-back-coefficient, change-of-scalars, module-pushforward-pullback, sheaf-tensor, and linear/open lower-shriek blueprint definitions. No new node needs an additional source.

For step 1 I opened the statements of the reduced-induced-subscheme, minimal-closed-subset, compact-subsets and locally-Noetherian-quasi-separated nodes. They give the closed complement, Noetherian topology, quasi-compactness of every subset, and quasi-separatedness exactly as used. Quasi-compactness of u is checked on intersections with quasi-compact opens; qcqs of X uses the stated quasi-compactness, rather than assuming it from local Noetherianity.

For step 2 the components-cover statement contains every irreducible subset in a component, the sobriety statement gives that component's generic point, and the dimension definition forbids a strict length-two chain. The generic-point hypothesis forces the inclusion B in C to be strict. This is an elementary chain argument, not an uncited dimension-drop theorem. In step 3 I checked that the finite-closed-subset node is a theorem for Noetherian T0 spaces and closed dimension-at-most-zero subsets, not merely an Artinian scheme theorem. Sobriety supplies T0 by the written point-closure argument; T is closed and its dimension was established in step 2. The cited statement then gives both finiteness and closedness in X.

For step 4 I checked the actual coefficient-morphism statement: alpha is invertible for every condensed ring, not just the special admissible rings. The change-of-scalars node explicitly states the inverse restriction equivalence and its identification with extension of scalars. Its categorical hypotheses are supplied by the sheaf-tensor and Grothendieck-sheaf statements: closed symmetric tensor, colimit preservation, equalizers and coequalizers. The pulled-back coefficient ring is commutative as required.

For step 5 I checked all six cited statements. Module pushforward is restriction along eta, pullback is extension along alpha, and eta is the unit followed by the pushforward of alpha. Restricting along alpha before the ring-sheaf pushforward gives exactly that action; the linear open extension uses the displayed projection-formula action. Cancelling restriction followed by extension along the isomorphism alpha identifies the two outside terms. The text also writes the composite-adjunction unit and counit after cancellation, so step 6 uses the actual maps, rather than arbitrary isomorphic objects. This is a direct expansion of the cited functor/adjunction definitions; it does not assert a new base-change or exactness theorem.

For step 6 I checked the arbitrary-ring-sheaf localization node itself: it allows arbitrary ring objects, requires qcqs X and a quasi-compact complementary open, and explicitly states the mono counit, epi unit, exactness and vanishing. All its hypotheses were proved in step 1 or hold by the choice of Z. Step 5 identifies the maps; step 4 preserves the zero object in the remaining vanishing. Step 7 only substitutes L=u*F and G=i*F and interprets vanishing off the finite closed complement. Its components-cover and sobriety citations also justify that an empty U satisfying the generic-point assumption forces X empty.

I tested the empty scheme and complement, F=0, a zero-dimensional scheme, nonreduced curves, and reducible curves including a zero-dimensional component. The generic-point assumption excludes dropping such a component into the complement, so the same length-two-chain contradiction works; neither integrality nor reducedness was used. Without the generic-point condition the conclusion fails already for U empty in an irreducible one-dimensional scheme, which explains exactly where that hypothesis is needed. No statement dispute arose.

For B, no new node duplicates an existing theorem or elementary step; formulas retain valid JSON escaping and definitions are cited. For C, every uses entry was read against its statement and every quotation is checked verbatim; the union is exactly proof_deps. For D, the item carries the dimension and scalar-comparison arguments rather than moving its clauses into fresh nodes. For E, quasi-compactness, quasi-separatedness, T0, coefficient invertibility, coefficient category and adjunction maps were checked individually. The off-unit topology, Grothendieck-sheaf and ring-localization tools are declared in split_report.tool_uses because they are generic tools for this route. Every step is under 2000 characters; none hides a long standard argument requiring a new node.

The first full dry run requested a longer quotation for quasi-separatedness (minimum 40 characters). I replaced that short excerpt by the complete cited statement; the mathematical dependency and proof are unchanged.
