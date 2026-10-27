# Q48 stage-1 delivery: lem-trf-derived-tensor-approximation-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-tensor-approximation-comparison.json`: statement, now split; no Mathlib match. Five proof steps, all below 2000 characters, use existing nodes only. The statement and its two statement dependencies are unchanged.
- `citations.json`: ten step/node entries, each quoting the statement of the cited existing node verbatim.
- `report.md`: this report. `searches.jsonl` is the unedited output log of the required search command.

New nodes: 0. New Mathlib leaves: 0. No Lean files, unit records, repository files or launcher scripts were written. No compiler, Lake, build or git command was run.

## Attachments

None. Searches in the current `lean/WeilConjectures/` for the exact blueprint tag, tensor approximation, and the corresponding derived-category morphism estimates found no declaration stating the item. The proved `DerivedCategory.isLE_tensor` at `lean/WeilConjectures/CategoryTheory/DerivedCategory/FlatModel.lean:441` proves an object bound, not the item; it already belongs to `lem-weil-pbc-source-derived-tensor-upper-bound`, which this split reuses.

## Literature wanted

None. All sources needed for the argument are present.

## Findings and changes

The assigned live item was unsplit with no proof; the sandbox initially contained no item, report or search log. There is no item-specific repair note. The statement is true as imported. In particular the deliberately asymmetric assumptions bound K and Q, which are exactly the fixed factors after factoring the map through K tensor Q. It is unnecessary to impose flatness, pseudo-coherence or a Tor bound. No STATEMENT-DISPUTED correction is needed.

I read Stacks `more-algebra.tex`, Tag 0DJE (`lemma-tensor-pseudo-coherent`): its proof explicitly omits the tensor-approximation details. The delivered argument supplies those details with cone triangles instead of citing an undeveloped Tor spectral sequence. I also read the construction and exactness of derived tensor around Tags 064M and 06Y6, the exact-functor construction and naturality following `lemma-derived-base-change`, and `derived.tex` Tags 0145, 05RS and its long exact cohomology formula. The proof is marked agent-written because this cone expansion is not printed in 0DJE. The existing source upper-bound lemma was read at lines 441--449 of `FlatModel.lean`.

The chapter and unit DAG records were read, together with the current `literature/blueprint/latest/blueprint/sec-trace-formula/` chapter, `sk-i-curve-zero/_section.md`, and `lem-trf-local-term-locality.proof.md`. This is the generic algebra input in the item's already recorded ancestry, not a new geometric route. The older imported chapter/unit records differ from the latest text; neither is altered. `blueprint.from.place` already specifies the finite-stage tensor approximation in the ancestor chain and remains intact. Whole-blueprint searches for tensor and approximation and the DAG searches found no imported node equivalent to the item; `same_as` remains empty. The obsolete `coord/dag-sync.md` referenced by the role document is absent, so the explicitly supplied current shared-clone paths are used.

Existing Mathlib search records from the live node are retained. I ran the required command for LeanFinder in two phrasings, Loogle, LeanSearch and two greps, and read every returned hit. LeanFinder gives fractions, standard t-structure and Tor functors; LeanSearch gives cone and SES comparisons; Loogle and the broad grep give basis equivalences and tensor adjunctions. The targeted homology grep has no hits. None states this two-morphism estimate or specializes to it in one line. All six actual searches have their exact tool and query text recorded in the item and their genuine counts and names from `searches.jsonl`; no unavailable service is mislabeled as absence.

## Not duplicates

There are no new nodes. In particular, do not recreate the upper bound: `lem-weil-pbc-source-derived-tensor-upper-bound` already gives the two-complex module statement, whereas `lem-pc-derived-tensor-upper-bound` only bounds tensoring a scheme complex with a degree-zero module. Likewise existing exact fixed tensor descent, K-flat resolutions and the derived long exact sequence supply every substantial input.

## Review by Q48

I checked delivery-errors B--E against the actual item, all cited statements, and the sources listed above. No unsplit auxiliary node is carrying a proof or a disguised clause of the item. All non-elementary facts are cited at the step that needs them. The step arguments, rather than new statements, carry the elementary cone vanishing, exact-sequence chases and composition.

Step 1 cites `def-weil-abstract-derived-category`, whose statement says this is a triangulated derived category, and `def-weil-triangulated-category`, whose TR1 clause actually gives the cone triangle for an arbitrary derived morphism. It does not incorrectly assume the original maps have already been chosen as chain maps. `lem-sf-derived-homology-long-exact` states the complete exact sequence for any distinguished triangle. For r >= n, surjectivity of H^r(alpha) and injectivity of H^(r+1)(alpha) force H^r(C_alpha)=0, including r=n. The identical check holds for beta and m. This verifies the essential minus-one in both cone bounds.

Step 2 cites `lem-pc-derived-tensor-second-factor-functor`, which explicitly treats rings as sheaves on the one-point site and defines the K-flat functor and its maps. `lem-pc-kflat-resolution` supplies representatives with flat terms, exactly the hypothesis of `lem-weil-pbc-kflat-fixed-tensor-triangulated`. The latter statement covers both orders of tensor, arbitrary unbounded varying complexes, the canonical identification with derived tensor, and the connecting maps of the distinguished triangles. It therefore supplies precisely the two displayed triangles with first maps alpha tensor identity and identity tensor beta. There is no inference from a definition of K-flatness to triangle preservation, and no unsupported appeal to symmetry on a different category of sheaves.

Step 3 uses `lem-weil-pbc-source-derived-tensor-upper-bound`, whose statement permits any commutative ring and any two derived module objects bounded above in cohomology. Applying it to (C_alpha,Q) and (K,C_beta) checks all four bounds against step 1 and the item's hypotheses. Its conclusions are vanishing strictly above n+b-1 and a+m-1, respectively. Since the indices are integers these are exactly vanishing at and above n+b and a+m, and hence at and above t. No lower bounds or finite Tor dimension have entered.

Step 4 cites the actual long exact sequence node again. I checked the outside terms are H^(i-1)(C) and H^i(C): both vanish only when i>t, whereas H^t(C)=0 alone gives surjectivity at t. Thus the proof does not claim injectivity at the cutoff. This is a short elementary exact-sequence argument, written out in the item. Step 5 uses the naturality in the second tensor argument explicitly stated by the tensor-functor node to identify the composite with alpha tensor beta; the derived-category definition supplies functorial cohomology. Composition of isomorphisms and of surjective module maps then proves the conclusion. Every one of these step/node pairs has a verbatim quotation in `citations.json`; the quotes were selected from the nodes' statements, never their proofs.

I tested zero objects, isomorphisms, negative and arbitrary integer bounds, equality n+b=a+m, and the two strict inequality cases. A useful sharp-bound test is R a field, P the module R concentrated in degree n, K=0, Q=L=R in degree 0, beta the identity, alpha zero, a=n, b=m=0. All hypotheses hold; at t=n the tensor map R to zero is surjective but not injective. Its cone has nonzero cohomology at n-1, confirming both the minus-one and the need to retain surjectivity rather than isomorphism at the endpoint. Over a nonregular ring, modules can have nonzero Tor in arbitrarily negative degrees; the argument uses only upper bounds, so this case is also covered without an illicit lower boundedness assumption.

The generic off-unit tools are declared with reasons in `split_report.tool_uses`; no maintainer-owned top-level `tool_uses` or `reviewed` field is written. All new proof dependencies are existing nodes, and none uses a lemma from the proof of another node without its being in that node's statement. No proof step exceeds 2000 characters or hides a standard comparison argument. No prohibited SGA source is used.

## Unfinished work

None in the stage-1 split. The existing tools retain their own DAG status. Dry run and push are performed with the prescribed delivery command; the maintainer's independent mathematical review remains external to this self-review.
