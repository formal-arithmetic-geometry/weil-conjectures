# Q35: lem-sfb-integral-closure-ind-etale-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-closure-ind-etale-base-change.json: item, statement, split into five proof steps; original statement and source retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-closure-etale-base-change.json: new statement, Mathlib leaf. TensorProduct.toIntegralClosure_bijective_of_smooth, Mathlib/RingTheory/Smooth/IntegralClosure.lean:380, specializes using Algebra.Etale.instSmooth, Mathlib/RingTheory/Etale/Basic.lean:223. The comparison map's definition is at IntegralClosure.lean:39–48.
- citations.json: verbatim statement quotations for every citation in every item step.
- searches.jsonl: unmodified output records written by the required search command; queries are copied exactly into the nodes. The single-file grep's output omits its filename, so the same query was repeated on its directory and that usable output is recorded.

One new node, one Mathlib leaf, zero new unsplit nodes. No Lean files or repository files were written, and no compiler, Lake or build tool was run.

## Attachments

None for the item. Searched WeilConjectures by the blueprint tag and by integralClosure, IntegralClosure, indEtale and tensor/colimit combinations. Existing integral-closure declarations cover finite products, normal rings, or integral-element descent, not this arbitrary ind-etale base change assertion. The existing RingHom.exists_integral_tensor_generators_of_colimit is already attached to lem-weil-pbc-integral-tensor-generators-colimit-descent; it is reused rather than duplicated.

## WANTED

None. All mathematical source passages used here are available in literature/stacks-project/.

## Corrections and route

The item was unsplit, with no earlier sandbox node or report. Its statement is correct: Stacks 0CBF allows arbitrary ring maps and a filtered colimit of smooth algebras, and the present etale specialization requires no additional ring hypotheses. No STATEMENT-DISPUTED correction is needed. The source says tensor products and integral closures commute with filtered colimits without expanding that assertion; the five steps supply that argument instead of moving the whole item into a new lemma.

Read the chapter and unit records and the current main-20261015 direct-images proof, paragraph (3). This is the finite tame normalization comparison input below the open-direct-image case. No chapter or unit statement, route, or realization is changed. The inherited nearest blueprint ancestor is null (confirmed with blueprint_refs.py ancestor); the inherited current-snapshot place and via chain are retained and extended for the new leaf. Whole-blueprint searches for integral closure, integral-closure-commutes and integral tensor found no equivalent blueprint node. The weakly-etale integrally-closed-domain result has extra domain hypotheses and does not give the arbitrary-algebra comparison here.

Generic tools from another unit are declared in split_report.tool_uses: directed reindexing, tensor-colimit element calculus, and integral-tensor-element descent. These supply algebraic tools under the existing normalization route, not a replacement of a unit step.

## Not duplicates

lem-sfb-integral-closure-etale-base-change vs lem-sbc-trait-generic-normalization-charts: both cite 03GE, but the existing node asserts existence of polynomial root charts for a finite normalization of a torsor on a smooth scheme over a trait. It neither states integral closure base change for arbitrary ring maps nor specializes to that assertion. The new node is exactly the finite etale algebra comparison, with no schemes, traits, torsors, or chart conclusions.

lem-sfb-integral-closure-etale-base-change vs lem-sfb-integral-closure-ind-etale-base-change: the new leaf assumes a single finitely presented etale algebra. The item allows any filtered colimit of such algebras; the new leaf cannot be applied directly to that colimit. The item's injectivity and surjectivity arguments supply the missing content.

lem-sfb-integral-closure-etale-base-change vs lem-exc-weakly-etale-normalization-tensor: the existing node assumes Noetherian local rings, a universally catenary domain, finite normalization, and compares normalization in total fractions. It does not cover arbitrary ambient B or arbitrary rings as required by this leaf.

## Review by Q35

I read Stacks algebra.tex, lemma-integral-closure-commutes-colim-smooth (0CBF), its cited smooth comparison lemma-integral-closure-commutes-smooth (03GG), and the etale version lemma-integral-closure-commutes-etale (03GE). The new leaf agrees with 03GE, and I read Mathlib's full declaration at line 380 and its map definition at lines 39–48. The smooth declaration has only commutative-ring and algebra assumptions; the Etale-to-Smooth instance at Etale/Basic.lean:223 supplies its extra typeclass. The new leaf writes finite presentation and formal etaleness inline so it does not rely on a convention-collector node for its meaning. The result is a direct Mathlib specialization, not an unproved comparison of different notions of normalization.

For step 1 I opened the statements of def-weil-pbc-ind-etale-algebra, lem-weil-pbc-filtered-category-directed-cofinal and the new leaf. The definition supplies the presentation, the reindexing node explicitly preserves the same colimit cocone for every target category, and the leaf supplies precisely the isomorphism at every stage. I also read categories.tex lemma-directed-category-system (0032). Reindexing stays in commutative R-algebras, so its transition maps are R-algebra maps. A common ambient universe avoids the oversized-diagram failure documented on the existing tensor-colimit node. No injectivity or etaleness of transition maps is assumed.

For step 2 I opened the tensor-colimit node's entire statement: it gives representatives, eventual zero, and ring-homomorphism structure when the tensor factor is an algebra. C is a commutative R-algebra by the integral-closure definition. The tensor definition explicitly says pure tensors generate and gives its universal property, which suffices to verify the displayed square. I opened the integral-closure definition: it gives an actual monic equation, so mapping that equation proves integrality at the limit without invoking an uncited flatness or integral-base-change theorem. The image being contained in C_S makes the map well-defined as an S-algebra homomorphism.

For step 3 the cited tensor-colimit statement supplies eventual vanishing of f_i(t_i) in D_j. The same transition on E_i commutes with f_i by the formulas already checked, and f_j is injective by step 1. Thus eventual zero holds before taking the limit. This does not incorrectly require S_i to embed in S, or require S itself to be flat by an uncited theorem.

For step 4 I opened lem-weil-pbc-integral-tensor-generators-colimit-descent and its Lean docstring in IntegralElementsColimitDescent.lean. Its arbitrary B_0,C_0 and finite s allow exactly B_0=S_i, C_0=S_i tensor_R B, s={x_i}. Its hypothesis refers to integrality through id tensor phi_0, not merely integrality over the wrong coefficient ring. I wrote both directions of the tensor cancellation identification: under them id tensor phi_0 is precisely the S-structure map, and 1 tensor x_i is precisely x. The upper tail is nonempty (contains i), directed, and has the same ring colimit, with the elementary extension-of-cocones argument written in the step. The cited descent lemma needs no module-finiteness or finite-type assumptions. This is a singleton use of an already existing general descent statement, not a new restatement of the item's surjectivity.

For step 5 the finite-stage preimage comes from step 1; compatibility from step 2 identifies its image with x. Only applying an inverse to a bijective homomorphism remains, so the step is elementary. All non-elementary external results used are cited, and citations.json quotes their actual statements, not their proofs. No step exceeds 2000 characters; the largest is the explicit tensor-identification and singleton-descent application, which hides no separate non-elementary comparison.

I checked the B–E checklist against the node files: the only new node has a self-contained statement and no proof; searches are real logged commands; the Mathlib file and lines were read; tags match tags/tags; no SGA source appears; dependencies introduce the notions actually used; no new clause merely restates the whole item. Small cases checked include R=S, S=0, B=0, noninjective R→B, and directed systems with noninjective transitions. In particular, zero rings do not obstruct monic equations or the tensor formulas, and filteredness supplies a nonempty index rather than a nonzero-ring hypothesis. The proof uses neither normality, domains, finiteness of B, nor cancellation inside a ring.

## Unfinished work

None in the requested stage-1 split. Existing dependency nodes keep their own states; the one new dependency is a Mathlib leaf.

## Validation

The first delivery dry run requested a separate numeric mathlib_match.line field; I added line 380, already read and documented above, without changing any mathematics.
