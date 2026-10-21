# Q154 stage-1 report

Item: lem-pur-clopen-finite-constructibility-bounds. Date: 2026-10-21.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-clopen-finite-constructibility-bounds.json: statement, now split into eight steps; no Mathlib match for the whole statement.
- citations.json: verbatim statement evidence for every proof-step citation, including all hypotheses and formulas.
- report.md: this report. searches.jsonl is the unmodified msearch command log. prepare.py is sandbox-only preparation code, not a project change.

There are **0 new nodes and 0 new Mathlib leaves**. The statement and statement dependencies are unchanged. Existing imported searches and blueprint ancestry are retained; six searches actually run for this delivery are appended.

## Attachments

None. Searched the live project source under lean/WeilConjectures both for the exact blueprint tag and for clopen decomposition, constructible sheaves, and Tor amplitude. The topological constructible-set declarations, EtaleSheafClopenProduct.lean (an etale module category equivalence), and pro-etale Tor preservation declarations do not together state every clause of this item as an existing exact declaration. No sorry declaration was treated as a finished proof.

## WANTED

None. The needed blueprint and Stacks sources are present locally.

## Corrections and scope

The imported item was a statement-only child of lem-pur-finite-clopen-derived-decomposition. That parent depends on this item and therefore cannot be used to prove it. Instead the proof uses its two independent sibling statements, lem-pur-clopen-ringed-module-gluing and lem-pur-finite-product-derived-tensor-calculus, whose proof dependencies are currently empty. This avoids circularity and does not move this item's content into a new node.

No statement dispute or change was necessary. The blueprint's short final invertibility assertion does not supply a written finite-clopen boundedness argument. The supplied proof is therefore explicitly agent-originated, with that exact blueprint place recorded. The current blueprint, chapter and unit were read; the unit has no numbered proof steps that this would replace. This is the inherited finite-level subargument of the parent, not an alternate purity route. No SGA source was used.

Generic off-unit facts are recorded in split_report.tool_uses: the existing open/closed immersion base-change leaves and the existing topological constructible inverse/image leaves. The finite-coefficient category definitions were already statement dependencies and are unpacked in the proof. All substantive clopen derived algebra stays in the existing same-unit siblings.

## Search results and reuse

The item could conceivably be a general sheaf-theoretic Mathlib result, so the required msearch commands were run for it: LeanFinder with two distinct conceptual phrasings, Loogle, LeanSearch and source grep, followed by a grep locating the promising general hits. Every service answered successfully. The queries are recorded exactly in the node and the command log; no unavailable service was called a negative search.

Read the returned declarations in Mathlib/Topology/Constructible.lean (especially lines 264 and 534), Mathlib/Topology/Sheaves/SheafCondition/PairwiseIntersections.lean:428 and Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:180. The first concerns constructible subsets, the second products of sections on disjoint opens of a topological space, and the third bounded representatives in a general derived category. None says constructibility of pro-etale finite-coefficient sheaves together with fixed Tor-interval detection. The existing 005J and 09YD Mathlib leaves supply the topological ingredients, so no leaf is duplicated.

Searched the whole DAG by constructibility/clopen/immersion keywords and ran blueprint_refs.py ancestor on the item and blueprint_refs.py search for clopen, constructibility and Tor amplitude. No blueprint node states this precise combination in another form. The nearest blueprint ancestor is def-pur-section-invariant with the existing via list through lem-pur-finite-clopen-derived-decomposition. No new node was required, so no new-node search or same-tag collision is hidden here.

## Not duplicates

No new nodes were created. The two sibling lemmas are reused, and the four generic topology/scheme tools are existing Mathlib leaves. In particular the parent is a consumer, not a duplicate dependency available as a proof.

## Review by Q154

I read the current blueprint's def-pur-section-invariant.md and its sk-def-purity-conv unit section, the chapter/unit records, the finite-torsion constructibility source, and the statements defining finite Tor amplitude and fixed pro-etale Tor intervals. The blueprint gives the invertibility application but no full argument for this child, so I wrote and marked the expansion as agent work. For the topological ingredients I read Stacks topology.tex, labels lemma-open-immersion-constructible-inverse-image (005J) and lemma-quasi-compact-open-immersion-constructible-image (09YD), and checked the existing DAG statements against those formulas. There are no new nodes needing separate sources.

For step 1 I opened all six cited statements. The open/closed immersion definitions identify the subscheme structures and the factorization of an immersion. The two base-change leaves give exactly the open and closed pieces after pullback, for arbitrary scheme maps, so they apply to Xi without additional flatness or finite-presentation assumptions. The constructible restriction leaf asserts constructibility in the open subspace. The image leaf requires retrocompact openness; I supplied that hypothesis explicitly because Xi intersected with a quasi-compact open is a closed subset of that quasi-compact space. For the reverse direction the open factor V of a stratum in Xi remains literally an open subscheme of X, and its closed stratum embedding is unchanged. Thus no incorrect factorization through a merely set-theoretic containment is being used.

For step 2 I checked that the definition requires a finite partition by locally closed constructible subschemes and locally constant finite-module restrictions. The strata are the actual fibre products justified in step 1. The cited pro-etale site has the base-change covering property, so restricting each trivializing cover to the open part gives the same constant finite module model; no theorem about arbitrary direct images is being assumed. For step 3 I use the same constructibility definition in the other direction. Finiteness of I and of every component stratification implies finiteness of their disjoint union. Disjointness and coverage use precisely the original cover hypotheses. The sheaf on each stratum is the same sheaf on the same scheme, so no comparison between etale and pro-etale constructibility is invoked.

For step 4 I read both sibling statements in full. The module gluing lemma says exact equivalence and explicitly identifies constant coefficient restrictions and the inverse gluing functor. It detects zero sheaves. The derived tensor calculus lemma states the unbounded equivalence and the exact identity H^m(riK) = riH^m(K), not just a bounded-below result. These are exactly the facts used to detect every cohomological degree. Constructibility in each degree uses steps 2 and 3; no uniform stratification over infinitely many degrees is asserted.

For step 5 I checked that the calculus sibling supplies the uncompleted derived tensor comparison for arbitrary module sheaves, with no constructibility or Tor hypothesis on the test module. With M arbitrary in degree zero, all component tensors vanish outside the same interval, and step 4 detects global vanishing. This is the full quantifier in the cited Tor definition. For step 6 the gluing sibling explicitly provides zero insertion eiN and ri ei = identity. Hence every component module N, including nonconstructible ones, is tested by a legitimate global degree-zero module. The calculus sibling again supplies both tensor and cohomology comparisons. I did not infer preservation of Tor bounds merely from conservativity or from a one-way locality statement.

For step 7 I checked the cited definitions of Db_c and Db_ctf, including that finite Tor amplitude is additional at finite coefficients. The cited unbounded equivalence gives full faithfulness and an inverse image of every tuple. The componentwise property checks then restrict that equivalence to the full subcategories. Finiteness is used exactly when enlarging the finitely many cohomological or Tor intervals to their common minimum/maximum. Given common bounds are preserved verbatim; the argument does not just prove some unspecified boundedness. No claim about completed integral or rational coefficients is being slipped into this finite-coefficient item.

For step 8 the two sibling statements explicitly include empty components and the empty partition. The finite zero module is a valid constant model, and the zero complex tensored with any complex is zero term by term. I checked I empty (so X must be empty), X empty with I nonempty, a cover with extra empty components, and the singleton cover. No minimum over an empty set is taken. As a further check against an accidental strengthening, a nonzero module in degree c detects failure of a cohomological interval not containing c; and over A = O_E/varpi^2 a residue-field module need not have finite Tor amplitude, so the proof consistently retains the separate Tor condition. An infinite cover could have components with unboundedly varying shifts; that does not contradict this statement because I is finite.

I checked delivery-errors B through E: every citation uses a node statement, all non-elementary algebra is cited, the only generic geometric facts are existing leaves, no clause was moved to a new node, and no dependency points back to the parent. Proof steps marked elementary are the explicit finite partition/quantifier deductions from these cited statements. Step 1, which collects geometric lemmas, is marked non-elementary. Every step is below 2000 characters; none hides a long comparison lemma. citations.json records the exact original statements, including the original escaping of the 09YD leaf, without modifying another worker's node.

## Unfinished work and validation

The split is complete at one level. The existing sibling algebra lemmas remain their own stage-1 items; this delivery does not claim to prove them. Server dry run and delivery results will be recorded after execution.
