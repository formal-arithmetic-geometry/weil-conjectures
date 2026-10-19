# Q91: lem-trf-local-flat-pure-complete-projective

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-flat-pure-complete-projective.json`: item, split into six steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/def-trf-mittag-leffler-module.json`: definition, unsplit; no Mathlib match for the module tensor-product condition (as opposed to an inverse-system condition).
- `dag/nodes/sec-trace-formula/lem-trf-flat-completion-universally-injective.json`: statement-only node, unsplit; Stacks 05DM; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-completion-flat-mittag-leffler.json`: statement-only node, unsplit; Stacks 05DK; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-countable-flat-mittag-leffler-projective.json`: statement-only node, unsplit; Stacks 059X; no Mathlib match.

`citations.json` contains a verbatim statement quote for every citation in every numbered step. `searches.jsonl` is the required search-command log. `research-results.json` preserves the full outputs for reuse; `research.py` and `write_split.py` are sandbox-only working scripts.

## Attachments

None. Searched `WeilConjectures/` in the read-only slopmaster2 checkout both for the exact blueprint tag/id and the completion/projectivity/Mittag-Leffler notions. No project declaration states the item or any of the new lemmas exactly. The item had no existing Lean attachment. No upstream master sorry is treated as a finished proof.

## WANTED

None. All sources needed for this split are available in `literature/stacks-project/`.

## Problems found and corrections

The item was unsplit, with no proof or proof dependencies. Its statement is faithful to all six hypotheses and the conclusion of Stacks 05DP, `flat.tex`, `lemma-flat-pure-over-complete-projective`; it needs no statement correction. The proof now exposes its three genuine black-box inputs and defines the module Mittag-Leffler notion. The latter is not the existing notion of a Mittag-Leffler inverse system. The completion of a module is explicitly constructed as compatible quotient classes in both completion lemmas; no ring-completion definition is cited for a module construction it does not state.

Two short arguments stay in the item: the tensor-square proof that a universally embedded submodule of a Mittag-Leffler module is Mittag-Leffler, and the monomial proof of countable generation. Neither warrants a new lemma node. The new completion-input lemmas have strictly fewer/different hypotheses and different conclusions from the item: 05DM assumes neither completeness nor projectivity modulo I and concludes purity; 05DK has no auxiliary algebra or associated-prime condition and concludes a property of the completion; 059X is an arbitrary-ring criterion with no completion or finite-type data. No new node merely restates the item or its conclusion under its original hypotheses.

Read the chapter, unit sk-i-curve-zero, current main-20261015 local-term blueprint proof, the inherited ancestry, and the item source. The ancestry records the historical semistable-alteration branch via 05FT, whereas the current local-term blueprint uses contracting correspondences. This delivery only splits the already assigned supporting algebra lemma, preserving its maintainer-owned chapter/unit and ancestry; it does not substitute a new route for any unit step or claim the old alteration argument is present in the current blueprint. No SGA source is used.

## Unfinished work

No unfinished work in the one-level split. The four new nodes are intentionally unsplit, with empty proof/proof_deps as required; later workers will split them individually. There are no new Mathlib leaves.

## Not duplicates

- def-trf-mittag-leffler-module vs def-weil-pbc-mittag-leffler-system: the new definition is injectivity of tensor with arbitrary products for a single module; the existing definition is stabilization of images in a countable inverse system of abelian groups.
- def-trf-mittag-leffler-module vs lem-weil-pbc-mittag-leffler: the existing blueprint theorem is derived-limit vanishing for finite inverse systems and does not state the module notion.
- lem-trf-flat-completion-universally-injective vs lem-trf-local-universal-injective-residue: the latter tests a map from a projective module to a flat module over a local ring modulo its maximal ideal; the new lemma gives purity of a completion map over general Noetherian rings from associated primes of fibres.
- lem-trf-completion-flat-mittag-leffler vs lem-weil-pbc-limit-flat-modules: the latter gives flatness and finite-tensor/limit comparison for a tower of flat quotient-ring modules, not the Mittag-Leffler module property of a completion with projective reduction.

No existing node shares the new source tags 05DM, 05DK, 059X, 059F or 059M. Searched the entire DAG by these tags, labels and concepts and the whole blueprint using blueprint_refs.py (Mittag, Mittag-Leffler, countably generated, universally injective, completion and the exact tags); no exact or more-general existing node states the new results. Also checked the existing countable projective decomposition, which is Kaplansky's decomposition of an already projective module, not 059X. The existing finite-type Noetherian lemma 00FN is reused directly.

## Review by Q91

I read the statement and full proof of 05DP in `flat.tex`, not just its dependency list. Its associated-prime hypothesis is the relative fibre condition, not the stronger condition for every tensor with a finite base module. I compared it prime by prime with the item's statement: p is the contraction of q, the tensor product is a B-module, and q is its B-associated prime. The item is unchanged.

For the new universal-injectivity node I read 05DM (`lemma-universally-injective-to-completion-flat`) and the preceding 05DL proof in `flat.tex`. 05DM has exactly Noetherian R and S, finite P over S, R-flat P and the relative associated-prime condition; it does not require R complete or the reduction projective. Its conclusion is universal injectivity of the displayed completion map, not merely ordinary injectivity. For the completion node I read 05DK (`lemma-lift-ML`) including the reduction to a completed free module and the preceding completed-direct-sum lemma. It applies to arbitrary flat R-modules with projective reduction over a complete Noetherian R; no finiteness over R is silently added. For the countable criterion I read 059X (`lemma-countgen-projective`) in `algebra.tex`, including its proof using Lazard, countable finite-free colimits and exactness after Hom and inverse limit. This criterion has exactly flatness, module Mittag-Leffler and countable generation.

For the new definition I read 059F and the complete tensor characterization 059M in `algebra.tex`. I deliberately use condition (2) of 059M as the definition; that proposition verifies agreement with Stacks' original definition. This is a real predicate on a specified module, not a theorem or a proof sketch hidden in a definition. I also read 059N(1)'s proof to verify the tensor-square expansion.

Step 1 cites only lem-weil-pbc-finite-type-algebra-noetherian. I opened its file: its statement gives exactly Noetherian S from a finite-type algebra over Noetherian R, so it applies with (R,S)=(A,B). The compatible-family completion here is an explicit definition.

Step 2 cites the new 05DM node. I read its written statement against the step: both rings are Noetherian (step 1 supplies B), M is finite over B and flat over A, and its fibre associated-prime condition is precisely the item's hypothesis. The map and its universal tensor-injectivity conclusion are both explicitly in the cited statement.

Step 3 cites the new 05DK node. I verified each hypothesis directly: A Noetherian and complete, M flat over A, M/IM projective over A/I. The cited statement supplies the completion's Mittag-Leffler property; the proof does not try to deduce it merely from flatness of the completed base ring.

Step 4 cites the new module definition and the existing tensor-product definition, both opened and read. The former explicitly gives the injectivity used in the lower row; the latter gives tensor generation and bilinear functorial maps. Naturality is checked on a pure tensor in the step itself. Injectivity of u tensor the product is the already proved step 2; no extra exactness theorem or cokernel-flatness fact is being assumed. This is a two-line kernel chase, appropriately elementary.

Step 5 cites the finite-type algebra and finitely generated module definitions; I opened both and used precisely their finite lists of generators and polynomial/linear expansions. The displayed monomials span over A, and countability follows by a finite set at each total degree. I checked d=0 and r=0 explicitly in the step. It does not assume M finite or finitely presented over A.

Step 6 cites 059X's new node, whose statement has all three hypotheses established: flatness is given, Mittag-Leffler is step 4, countable generation step 5. It gives projectivity over A, exactly the item's conclusion.

Small-case checks: the Mittag-Leffler tensor condition is harmless for an empty family or the zero module, and over a field the finite basis support of a tensor shows it holds for every vector space. For 05DM, I=0 gives the identity completion map. With R=Z, S=Z[1/p], I=(p), P=S, the relative associated prime q=(0) violates IS+q!=S and the completion is zero; this confirms why the prime condition cannot be discarded. The same failure can be seen with R=Z_p and S=R[1/p]. For 05DK, I=0 reduces its assumptions to P projective and the completion is P; finite free modules over a complete base are another check, and arbitrary free direct sums are allowed. For 059X, zero and countably free modules fit; Q over Z shows countable generation and flatness alone do not suffice (it is not Mittag-Leffler). The unit ideal in the complete-base item forces A=0, so no hidden nonzero case appears there. No hypothesis was added, dropped or weakened.

I read every Mathlib result returned by the logged commands, then checked the plausible candidates in source: `Functor.IsMittagLeffler` is an inverse-system-of-sets property (`CategoryTheory/CofilteredSystem.lean:136`); `TensorProduct.piRightHom` constructs the canonical tensor/product map (`LinearAlgebra/TensorProduct/Pi.lean:56`) without asserting the new property; `Module.Flat.projective_of_finitePresentation` (`RingTheory/Flat/EquationalCriterion.lean:287`) requires finite presentation over the base; `AdicCompletion.of_injective_iff` and `of_injective` (`Basic.lean:605,619`) require Hausdorffness and give ordinary injectivity; `AdicCompletion.flat_of_isNoetherian` (`AsTensorProduct.lean:379`) completes the base ring itself. None is a one-line specialization to the item or the new lemmas. Each node has two distinct semantic phrasings, a Loogle query and source grep, all run by msearch.py and preserved verbatim; all services succeeded in this run.

B–E checks: all objects/hypotheses introduced, sources are verified tags and labels, no proof inside a new statement, no new node uses the proof of a cited node, no unsupported tensor exactness or comparison theorem is used, and each citation has a literal statement quote. The dependency graph only descends to the three supporting lemmas, the new module definition and existing definitions/Noetherian leaf; no edge points back to the item or its parents. All non-elementary steps are under 650 characters, and none hides a separate comparison. No file outside this sandbox was written, no git command was run in the shared repository, no compiler/Lake/build tool was run, and no agent was started.
