# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-maximum-history-finite-realization.json: statement, split; six explicit steps; no exact Mathlib match.
- citations.json: one verbatim statement quote for every step/node citation.
- No new nodes and no Mathlib leaves. The existing item, its historical searches, source, blueprint lineage and statement were preserved.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint id and by maximum history/center/stratum and invariant/history identifiers. There is no declaration stating this conditional finite realization. I also read the actual calculus interface in lean/Sheaf/AlgebraicGeometry/ResolutionInvariantCalculusData.lean; its existence/geometry/progress/termination fields are hypotheses, not a completed realization proof.

## Literature wanted

WANTED: Bierstone--Milman--Temkin, Q-universal desingularization, arXiv:0905.3580, Theorem 6.1 and Addendum, sections 6.1--6.3, for the detailed underlying existence/synchronization source of lem-trf-maximum-history-finite-realization. No archival copy is present. This delivery does not assume that unread source proves the conditional lemma; proof_origin is agent. Existence of the calculus is not proved or used without the explicit calculus hypothesis.

## Findings and changes

The live item was unsplit; the sandbox contained no previous split, report or searches. I copied the live item without changing its statement. The strong termination and geometric hypotheses are already in def-trf-resolution-invariant-calculus-data, so extracting these conclusions into new lemmas would only duplicate the assumptions or clauses of this item. The proof now carries the construction, termination contradiction, uniqueness comparison and cut reindexing itself.

I read the chapter and unit records and the current literature/blueprint/latest local-term-locality statement and proof. The current local-term proof uses the normal-cone contracting-correspondence argument, whereas this node records a historical alteration/resolution branch. I retained the assigned supporting result and its recorded ILO route; I did not reintroduce this branch into the current local-term proof or edit the unit. Blueprint searches for maximum, resolution and blowup found no imported node stating this conditional history realization. Existing specialized resolution-word progress/comparison nodes concern one particular normalized invariant; they are not needed for a theorem conditional on an arbitrary supplied calculus.

Mathlib searches were run using msearch.py only: LeanSearch, Loogle, LeanFinder and grep, followed by a second semantic formulation about termination of recursive histories. I read the returned signatures: the first services found generic order duals, series, simplicial normal forms and complex embeddings; the second found Computation/Turing termination facts requiring their own encodings and termination assumptions. None states this geometric realization. Loogle blowup and source grep returned zero hits. Actual logs and exact queries are in searches.jsonl and the node; inherited searches were retained.

## Unfinished work

None within stage 1. No Lean was written, and no compiler, Lake or local DAG/preflight checker was invoked. The formal proof remains a future stage.

## Review by Q59

I read ILO Expose VIII 2.1.1--2.1.4 (printed pp.86--87), 2.3.1--2.3.5 (pp.91--92), 2.3.11 (p.93) and 2.3.13 (p.94), from the local PDF. These specify ordinary blowups with retained centers, strict transforms, stopping before exceptional cleanup, and synchronization by disjoint unions. They motivate the conventions but do not replace the proof from the calculus hypotheses. There are no new nodes requiring separate sources or duplicate-tag comparisons. No SGA source was used.

Step 1 uses the actual statements of the calculus, admissible-history and labeled-resolution definitions. The calculus explicitly supplies an extension at every nonregular stage, regular coherent nonempty nowhere dense centers, next ambient geometry and reduced strict transform. The history statement explicitly closes admissibility under maximum extensions. Thus the induction has both its base and its step with no unproved preservation theorem smuggled in.

Step 2 uses precisely the calculus's no-infinite-chain condition, not its decreasing maxima as a purported well-foundedness theorem. Under the supposition of never stopping, choosing one available successor successively constructs a forbidden natural-number chain; this is the ordinary elementary dependent-choice argument. Regularity of the empty scheme is vacuous. Least stopping time exists in the natural numbers, not in V.

Step 3 is the only non-elementary comparison step. I opened all four cited statements. The history definition allows a smooth comparison over the identity initial pair, with no deletion for our nonempty centers. The calculus's smooth-values clause identifies values under that comparison. Reduced closed loci determine radical ideals, including their ambient closed immersion. The blowup universal-property node says finality and uniqueness of the induced map; its current blueprint_update explicitly gives the unique factorization when the extended ideal is invertible. Applied in both directions to blowups of the same ideal, uniqueness makes the composites identities. The strict-transform definition is scheme-theoretic closure, so its transport under an isomorphism is the very same closure, not merely a statement about topological support. The induction compares only finite prefixes already identified, avoiding any assumption of uniqueness before the comparison is built. Regularity then forces the same stopping length.

Step 4 uses the calculus center/progress clauses verbatim and the labeled-tower convention. Strict progress is applied only when the next stage is nonregular and therefore has a positive greatest value. In the order dual the inequalities reverse. Finite disjoint unions are explicitly among the calculus's inputs, so the maximum is over the union; no componentwise renumbering or dimension restriction is introduced.

Step 5 uses the labeled-tower definition, the Cartier-ideal blowup isomorphism and the strict-transform definition. A lower cut intersects the increasing finite active list in a prefix, so prefix count gives every stage and every composite transition without an existence-of-colimits assertion. Across an inactive label the unit ideal is invertible, and strict transform along the resulting identity is the closure of the whole scheme, namely itself. Empty/full cuts and arbitrary gaps in a possibly dense label order are covered; no successor element in L is assumed.

Step 6 uses the history and labeled-tower definitions, both of which explicitly retain center ideals and their order even for identity intrinsic blowups. It checks that reindexing inserted only inactive identities, never erased a chronological active center. It makes no claim that an isomorphism of intrinsic schemes determines the center ideal.

I checked delivery-errors B--E: no statement-only child carries an illicit proof (there are no children); all objects and definitions remain in the unchanged statement; citations.json quotes actual statement text, never a proof; every non-elementary fact is cited and its hypotheses checked as above; there are no cycles through the item or downstream resolution existence; and no result is replaced by a clause-shaped child. The six step texts have lengths 653, 644, 1199, 699, 914 and 521, so none hides a long-step lemma above 2000 characters. Edge cases checked were empty X, regular X, one extension, an identity intrinsic blowup with retained ideal, a disconnected input with different component maxima, a non-well-founded V, cuts containing no active label, and cuts containing all active labels. No statement dispute was found and no statement was changed.
