# Stage-1 report: lem-trf-finite-pushforward-reflects-finite-presentation

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-finite-pushforward-reflects-finite-presentation.json` (statement, split; no exact Mathlib match), `citations.json`, and this report. No new DAG nodes or Mathlib leaves. The sandbox initially contained no item, split, report, or searches. The live item was copied with its statement, source, ancestry and earlier search records retained.
2. Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint id and finite-presentation/restriction-of-scalars/direct-image terminology found no completed declaration stating the item. Algebraic finite-generation declarations and site pushforward-preservation declarations do not give this assertion.
3. WANTED: none.
4. The item is correct as stated. Its previously empty proof is replaced by the affine proof of Stacks 05B4, reverse direction. There is no statement correction or change to the chapter/unit route. In particular, finite plus locally of finite presentation is enough: all the needed hypotheses are checked on each affine target open. No Noetherian, flatness, surjectivity, or finite-generation hypothesis on the original sheaf is added.
5. Unfinished: none of the assigned stage-1 split. Existing dependencies remain independent work items; they are used by their statements, not by unproved details in their proofs.

## Proof and sources

I read `literature/stacks-project/descent.tex`, Tag 05B4, label `lemma-finite-finitely-presented-module`, statement and full proof. It reduces to a finite finitely presented ring map and invokes Algebra 0564 and Properties 01PC. I also read `algebra.tex`, label `lemma-finite-finitely-presented-extension` (0564), `properties.tex`, label `lemma-finite-presentation-module` (01PC), `modules.tex`, label `lemma-finite-presentation-quasi-coherent` (01BO), and `morphisms.tex`, label `lemma-locally-finite-presentation-characterize` (01TQ). These are the sources of the existing statements used here; there are no new-node sources to audit.

The latest blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and the recorded chapter/unit records were read. This is a supporting commutative-algebra branch already present through elementary devissage and flatification; the split does not change the contracting-correspondence statement or its route. I retained the precise recorded ancestry rather than suggesting 05B4 is itself written in the current ancestor's text.

DAG/blueprint searches for finite presentation, finite pushforward, 05B4, 01PC, affine-module criteria, and finite extensions found the existing ring-map equivalence and the affine sheaf criterion. Whole-blueprint searches with `tools/blueprint_refs.py search` found no node stating this exact finite direct-image reflection assertion. The parent local-neighbourhood/stalk comparison uses this item and cannot be cited back; the preservation sibling is the opposite implication. No duplicate was created.

## Review by Q92

I checked delivery-errors B through E against the actual node statements and source passages. In Step 1, `def-weil-finite-integral-morphism` explicitly says a finite morphism is affine and its inverse-image section ring is a finite module over the target section ring. Thus the entire inverse image U is affine, without an unjustified choice of an affine intersection. `lem-weil-pbc-lfp-affine-opens-finite-presentation` applies to these very opens: f(U) is contained in V by definition, so it supplies finite presentation of R to S as an algebra. This checks both hypotheses later required by 0564.

In Step 2, I checked clauses (0) and (b) of `lem-weil-pbc-quasi-coherent-finite-type-affine`. Clause (0) is necessary because we have not separately proved pushforward preserves quasi-coherence: finite presentation of the direct image itself makes that module quasi-coherent. Clause (b) then gives finite presentation of its sections on V. The equality of these sections with M and the restricted scalar action is part of this item's own direct-image definition; it needs neither an affine-pushforward comparison isomorphism nor an extra lemma. This avoids hiding a non-elementary affine equivalence in the phrase 'reduce to affines'.

In Step 3, `lem-trf-finite-extension-module-finite-presentation` states exactly the equivalence between finite presentation of the same S-module over R and over S, for a finite and finitely presented ring map. Step 1 supplies its ring-map hypotheses and Step 2 supplies its R-module hypothesis. This is an existing algebraic result, strictly smaller than the scheme item, not a new restatement of the conclusion.

In Step 4, the same affine criterion's clause (b) gives finite presentation of F restricted to U because F is assumed quasi-coherent. The only remaining assembly is local: affine target neighbourhoods pull back to a cover, and a finite free presentation around a point inside one of these opens is already the presentation required in `def-weil-pbc-module-finite-type-presentation` (2). This is why the final step is marked elementary while still citing both the criterion and the definition. I checked every `uses` against the opened statement and supplied a verbatim quotation for every occurrence in `citations.json`. None takes information from a cited proof or a definition that fails to assert a theorem being used.

The two generic tools filed in the proper-base-change unit are declared in `split_report.tool_uses`: the affine-chart characterization and the affine module-sheaf criterion. They are exactly the generic tools in the source's affine argument and do not replace any step of this item's unit. The ring extension lemma is already in the item's unit.

Small cases checked: X empty makes the conclusion vacuous, including the zero section ring and zero module on empty inverse images; the identity morphism gives the ordinary affine finite-presentation criterion; a nonsurjective finite closed immersion still has the stated equality of sections on every target open, so no surjectivity is needed. No finite target cover is selected, so neither quasi-compactness of Y nor a global Noetherian hypothesis enters. The argument works with arbitrary quasi-coherent modules and reduces their finiteness to the hypothesis on the direct image.

All four proof steps are below 2000 characters (423, 451, 314, 605); their combined assembly is 1793 characters. No hidden standard sublemma has been moved to a long step. There is no new node, no restatement split, and no circular invocation of the parent or sibling. The proof dependency list is exactly the union of step citations.

## Mathlib searches

I retained the live node's earlier search records and ran the required logged Q92 searches (LeanFinder twice with different formulations, Loogle, grep, and LeanSearch). Both semantic formulations returned local presentation definitions; the second also found the ring-map characterization already represented by the existing affine-chart dependency. Loogle found no result. Grep's one hit, `Mathlib/RingTheory/Extension/Presentation/Basic.lean:120`, is `Algebra.Presentation.finitePresentation_of_isFinite`, asserting finite presentation of an algebra from finite generator/relation data; I read its source and it is not a sheaf direct-image reflection result. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` around the returned presentation data and classes: these define local finite presentations, not the scheme morphism comparison. All five searches completed; none is recorded as an unavailable service or an invented query. Their exact results are in searches.jsonl and appended to the item.

## Not duplicates

No new nodes. All cited facts were reused under existing ids; no duplicate pair is introduced.

## Validation

The server-side review and required delivery dry run are performed with the prescribed tools; no Lean files, compiler, Lake, local DAG checker, repository writes, or git commands are used by this worker.
