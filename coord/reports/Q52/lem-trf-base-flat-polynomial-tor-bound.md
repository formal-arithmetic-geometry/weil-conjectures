## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-base-flat-polynomial-tor-bound.json: item, split in three steps; no exact Mathlib match.
- citations.json: eight verbatim statement quotations for the eight step/node pairs.
- report.md: this report. searches.jsonl is the unedited search-wrapper log.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. All non-elementary inputs already have DAG nodes. The tensor-complex calculation and the exactness/homology calculation are proof steps, not new nodes or restatements of the item's clauses.

## Attachments

None. The exact blueprint tag has no declaration in lean/WeilConjectures. ModuleCat.polynomial_tor_bound_of_base_tor_bound in lean/WeilConjectures/RingTheory/PolynomialTorBound.lean:47 states the general polynomial-transfer clause with a supplied base Tor bound; it does not state the derived tensor clause or derive base Tor vanishing from flatness. It therefore supplies an existing dependency, not an attachment of this item. DerivedCategory.QObjTensorQObjIsoOfKFlatLeft in FlatModel.lean supplies another existing dependency, not the whole item.

## WANTED

None for this split: the sources used directly are present locally. The existing general polynomial-transfer node records Weibel Theorem 4.3.7; I read its statement and its project Lean realization rather than claim to have read an unavailable local copy of Weibel. No fresh proof of that dependency is delivered.

## Source and blueprint audit

The item statement is unchanged, including every boundary case. I read Stacks more-algebra.tex, lemma-perfect-over-polynomial-ring (Tag 068X), and distinguished its pseudo-coherent perfectness conclusion from this item's unrestricted ordinary-module statement: 068X alone cannot justify the latter without extra hypotheses. The item's source already explicitly calls for the existing general polynomial Tor bound, so the split uses lem-pc-polynomial-tor-bound, with d=0; it does not add pseudo-coherence, Noetherianity, finite generation, or projectivity of M.

I read the current latest blueprint proof lem-trf-local-term-locality.proof.md, especially (1)--(2), and the item's recorded ancestor chain. This is the algebraic sub-input of the already recorded relative-duality/polynomial-chart refinement, not a replacement of the fixed chapter or contracting-correspondence unit route. from.place is retained and split_report.blueprint explains exactly which parent proof input is realized.

Whole-DAG searches for polynomial Tor, module K-flat models, flat exact tensor and Tor symmetry located all existing inputs. The read-only blueprint_refs searches for polynomial Tor, polynomial, Tor_i, K-flat first and flat tensor found no imported node stating the conjunction of this item (same_as=[]). No node was created. The item ancestor command confirms lem-trf-local-term-locality.

The new searches were run only through msearch.py and their outputs read. LeanFinder's two phrasings returned flatness criteria and then Krull dimension, not flat dimension or the desired conjunction. LeanSearch returned exact tensor criteria. Loogle returned no hits for Module.Flat, MvPolynomial and unrelated Vector.flatMap declarations for the alternate query. The RingTheory grep returned tensor exactness and torsion-free statements; CategoryTheory grep returned Tor vanishing for projective inputs and unrelated IsZero statements. I read Flat/Basic.lean:322--345, Flat/CategoryTheory.lean:13--90 and Monoidal/Tor.lean:13--64: the existing exact tensor result is useful but does not make the entire item a Mathlib leaf, and vanishing for projective inputs cannot replace flatness. All actual query texts and log result digests are appended to the item's historical search records without inventing or overwriting searches.

## Not duplicates

No new nodes and hence no new/existing same-tag pairs. Existing lem-pc-polynomial-tor-bound is deliberately reused rather than duplicating its d=0 instance. Existing lem-pc-module-bounded-flat-kflat and lem-pc-source-kflat-module-tensor-model are reused rather than creating a flat-single derived-tensor node.

## Review by Q52

I opened the statements of all seven distinct cited nodes and checked the exact clauses against the proof steps; citations.json copies those statements verbatim. I also read Stacks Tag 064K, lemma-derived-tor-quasi-isomorphism, in more-algebra.tex:14284 onward; Tag 06XZ, definition-K-flat, and Section 06XY; algebra.tex Tag 00M3, lemma-tor-left-right, including its projective-resolution homology formula; and the exact tensor criterion recorded as Tag 00HD. Tags were checked in stacks-project/tags/tags. No new node needs a source review.

Step 1 uses lem-weil-pbc-flat-tensor-exact for exactness, not merely the injectivity definition of flatness. Its statement explicitly gives exactness on both tensor sides. The bounded-above ordinary-module statement of lem-pc-module-bounded-flat-kflat applies to M[0]: degree zero is the assumed base-flat module and every other term is zero. def-pc-module-kflat-complex explicitly identifies acyclic-tensor K-flatness with the categorical quasi-isomorphism convention required by lem-pc-source-kflat-module-tensor-model. That last statement explicitly permits an arbitrary second complex; no flatness of L is inferred or needed. Only the bidegree (0,0) survives the total tensor, so the displayed identification is an actual identification of complexes with zero differentials, yielding the isomorphism in D(R), not just a degreewise homology assertion. This step is marked non-elementary because it invokes the cited K-flat/model theorems.

Step 2 uses def-weil-pbc-tor-modules to choose a projective resolution of the test module L and to identify Tor_j(L,M) with its tensor homology. lem-weil-pbc-flat-tensor-exact applies to the three consecutive resolution terms in each positive degree, since M is flat over exactly R. Its exactness conclusion gives kernel=image and hence zero homology by the definition of homology. This is an elementary calculation after the cited exactness theorem. The non-elementary swap to the required first-variable Tor_j(M,L) is explicitly supplied by lem-weil-pbc-tor-symmetry; I did not confuse the first-variable ordinary Tor definition with the derived-tensor convention or assert their identification without a theorem. Commutativity of R is precisely the symmetry hypothesis.

Step 3 uses only the statement of lem-pc-polynomial-tor-bound: its quantified base bound is established in step 2 for every R-module, its polynomial module is the given M, and d=0 is allowed. The output bound j>d+n becomes j>n. I read the full node and the Lean declaration at PolynomialTorBound.lean:47, including the n=0 and successor clauses; the node expressly permits arbitrary modules and zero rings. It is a more general existing theorem, not a newly named clause of the item. The source 068X is contextual; no unsupported inference from fibrewise global dimension or pseudo-coherence occurs.

For B1--B10, no new node is delivered, no proof sketch is hidden in a new statement, and no duplicate/definition/Mathlib leaf is invented. For C1--C5 every substantive input is named in uses and quoted from the statement, and proof_deps is exactly their union. The generic algebraic inputs outside this unit are declared in split_report.tool_uses with their purpose; no maintainer-only tool_uses field is written. For D1--D5 the actual assembly argument remains in the item, in three steps totaling 2091 characters; none exceeds 2000 characters, and no induction or comparison is silently assumed. For E1--E7 I checked that the base restriction is along R to P, that the resolution in step 2 resolves L rather than M, that all testing modules are arbitrary, and that no local/Noetherian/finiteness assumption enters.

Small cases: with n=0 the polynomial bound is the already proved base bound. With M=0 all tensors and the chosen zero first complex vanish. Over the zero ring all unital modules vanish. With R=Z, n=0, M=Q the module is flat but need not be projective, confirming why the proof must use flat exactness and Tor symmetry rather than the Mathlib projective-vanishing lemma. For n=1, R=k, M=k with x acting as zero, Tor_1 over k[x] against k can be nonzero: the proof only asserts vanishing strictly above n. No statement dispute or source correction was necessary. The original item had no proof; the correction was to supply the assembly and explicitly separate the two Tor conventions.

## Unfinished work

None for stage 1 of this item. Existing dependencies retain their own statuses and are not modified. No Lean was written, no compiler/Lake/build command was run, no other agent was started, and all writes are in the assigned sandbox. The required dry run and direct push follow this review.
