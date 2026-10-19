# Stage-1 delivery: lem-trf-split-transfinite-module-filtration

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-split-transfinite-module-filtration.json`: statement node, now split into five proof steps; not a Mathlib leaf. The statement is unchanged, including the set-sized ordinal, endpoint, continuity, and split-inclusion hypotheses. Both dependencies are existing Mathlib definition leaves.
- `citations.json`: seven entries quoting verbatim the statements of the nodes cited by the proof steps.
- `report.md`: this report. `searches.jsonl` was produced by the required search wrapper.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for transfinite filtrations, ordinal/module combinations, split filtrations, dévissage, and Kaplansky. The hits concern sheafification, finite representation filtrations, derived truncations, or the unrelated UFD criterion. No declaration states this item. The upstream master checkout was also searched as reference material; nothing there was treated as a finished proof.

## WANTED

None. The complete source is present in `literature/stacks-project/algebra.tex`.

## What was wrong or incomplete

The imported item was a correct statement-only node, with no proof. There is no statement dispute or source error to repair. Its use of indices up to and including kappa already avoids a potential endpoint error in applying an ordinal-indexed dévissage to a successor length: Stacks Definition 058U is applied with ordinal S = kappa+1.

The statement's two definition dependencies are exactly the notions requiring DAG references. The retractions, increasing submodules, ordinal conditions, and linear isomorphism are spelled out in the statement. I retained all inherited Mathlib search records and added the actual Q96 wrapper records. No imported fields, chapter/unit binding, or unit realization was changed.

## What could not be finished

Nothing remains in this one-level split. No Lean was written and no compiler, Lake command, or local DAG/preflight checker was run.

## Mathlib and blueprint searches

I read every wrapper result in `searches.jsonl`, including the second semantic phrasing. I inspected the candidate source declarations: `Submodule.quotientEquivDirectSum` in `LinearAlgebra/FreeModule/Finite/Quotient.lean` (lines 25–55 and 104–124) is Smith-normal-form algebra for finite free modules over a PID; `Module.DirectLimit.linearEquiv` in `Algebra/Colimit/Module.lean` (238–257) compares two constructions of a direct limit; `DirectSum.Decomposition.ofLinearMap` in `Algebra/DirectSum/Decomposition.lean` (242–255) assumes the inverse and inverse identities; and `iSupIndep.linearEquiv` in `LinearAlgebra/DFinsupp.lean` (629–635) assumes independence and generation. These are not one-line specializations giving this item. The Hahn embedding results in `Algebra/Order/Module/HahnEmbedding.lean` (149–174) concern a specific family of strata over an Archimedean ordered division ring. Filtration predicates and structure recursors do not prove a transfinite splitting.

`tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality` as the inherited ancestor. Whole-blueprint searches for `transfinite`, `split filtration`, and `058V` found no matching imported statement. The whole-DAG tag and concept searches found this item, its parent Kaplansky decomposition, and the more specialized faithfully flat descent proof, but no replacement for the item. I read the chapter/unit records and the current main-20261015 ancestor proof/update: its contracting-correspondence route is unchanged. This algebraic helper only expands the already-created 058V branch below the reviewed 058X node; it is not the unit's key statement.

## Not duplicates

There are no new nodes. In particular, the construction of a quotient section, the finite-sum map, and the finite-support maximum argument are steps, not separate nodes. `lem-trf-projective-kaplansky-direct-summand` has additional countable-generation and direct-summand hypotheses and uses this item after constructing a filtration; `lem-trf-local-projective-faithfully-flat-descent` states descent of projectivity, not the general split-filtration theorem.

## Review by Q96

I read Stacks Tag 058U (`definition-devissage`) and Tag 058V (`lemma-direct-sum-devissage`) in full, including both image and injectivity inductions. The five steps follow that proof, with its implicit quotient inclusions made explicit and its injectivity induction replaced by the same finite-support argument using the largest support index. Stacks cites no auxiliary lemma in this proof. There is no hidden splitting, colimit theorem, flatness assertion, or infinite-sum convergence claim to import as a new node.

For step 1 I opened `def-weil-pbc-quotient-module` and read its entire statement. It supplies cosets, the linear quotient map, its surjectivity and its kernel. The formula s(q(x)) = x - j r(x) is well-defined because r j is the identity; the cancellation for a changed representative is written out. Applying q proves q s = id. The claim that the section image meets the old submodule trivially is proved by that equality, rather than assumed from a definition of split exactness. The set-sized ordinal is what permits the simultaneous choice of the given retractions.

For step 2 I opened `def-weil-pbc-direct-sum-modules` and read its entire statement. It explicitly defines finite support, componentwise operations, canonical inclusions, and writing an element as the finite sum of its components. These give the displayed map and its linearity directly. The ordinal inequality alpha < beta implies alpha+1 <= beta, together with increasingness of the given filtration, places every summand in X_beta. The initial-sum submodule D_beta is defined inside the proof, not borrowed from a source construction.

Step 3 cites those same two statements for the single-coordinate family and the quotient component. The proof of surjectivity is in the step itself: choose the least failing ordinal, rule out zero, use the explicit formula from step 1 at a successor, and use exactly the assumed union formula at a nonzero limit. The smaller-stage preimage exists by minimality, so there is no circular induction. Retraction linearity and the hypothesis X_kappa = X are used in the indicated places; no projectivity or countable-generation assumption has entered.

Step 4 cites the direct-sum statement for finite support and the quotient statement for the kernel X_gamma. A finite nonempty set of ordinals has a largest member by taking successive pairwise maxima; this elementary argument is included. All earlier section images lie in X_gamma, so applying q_gamma to the relation kills the lower terms and retains the largest nonzero component. This proves injectivity without any assertion about a general colimit. Step 5 cites the direct-sum definition for the final module and empty sum, and proves the inverse is linear from uniqueness of preimages; a separate linear-inverse lemma would be elementary and redundant.

I checked delivery-errors B–E against the written files. B: there are no new unsplit nodes or leaf claims needing extra sources; the item is self-contained, uses ordinary TeX once, and retains its precise blueprint provenance. C: each citation is to a statement actually used, and each use has a verbatim quote in `citations.json`; the only external facts used are the two explicit definitions. D: the proof's construction and both bijectivity arguments are in the item, with no restatement node and no circular dependency. E: all successor quotients exist with alpha+1 <= kappa, the continuity hypothesis is used only at a nonzero limit, all sums are finite, and no stronger ring or factor hypotheses are used. Every proof step is below 2000 characters.

I tested the empty ordinal kappa=0 (X and the direct sum are zero), kappa=1 (the quotient X/0), a two-step split extension, repeated equal stages (the corresponding factor is zero), the zero ring/module, and the omega filtration by finite partial sums. The construction works in each case. I also checked why continuity matters: the filtration X_n=0 for all finite n and X_omega=R with R nonzero has all successor inclusions split but would give a zero direct sum; it violates precisely the stated continuity hypothesis, so it is not a counterexample to the item. The kappa+1 indexing retains a last nonzero factor at a successor endpoint. No SGA source is used.
