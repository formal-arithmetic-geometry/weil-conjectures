# Stage-1 delivery: lem-weil-pbc-reduction-pullback-derived-tower

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-reduction-pullback-derived-tower.json — statement; ten-step split using existing nodes; not a Mathlib leaf.
- citations.json — one exact statement quotation for every proof-step citation.
- searches.jsonl — actual searches recorded by msearch.py; read their returned hits.

No new DAG nodes, no new Mathlib leaves, no Lean files, and no unit-record changes. The sandbox initially contained only dispatcher brief markers; there was no earlier item, report, or search log to resume. write_split.py is sandbox-only preparation code, not a delivered project file.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, reductionTower, reduction/tower and tensor/pullback terminology. The hits concern ordinary pullback composition, scheme compactification towers, fixed-ring adic towers, or integral coefficients. None states the arbitrary ringed-topos, arbitrary strict algebra-tower comparison with the required universal-counit normalization and augmentation. No sorry declaration was treated as a completed proof.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The item statement is unchanged. Its empty proof was replaced, the statement dependencies were audited, and the proof dependencies now equal the union of step citations. The original recorded Mathlib searches and all origin/blueprint fields are retained. Additional searches were run and appended faithfully. The inherited derived-tensor-pullback statement dependency was replaced by the actual notions used to state the normalization, including K-flatness, flatness, strict inverse systems, restriction, tensor section calculus and derived tensor. No statement dispute was found.

Read the fixed proper-base-change chapter and sk-thm-properbasechange unit. This item is an auxiliary coefficient comparison under the direct-image/completion node, not that unit's key statement. It refines the final sentence of prop-weil-pbc-direct-image-limits: the projection-formula identifications must commute with quotient transitions and identify the completion map. The current main-20261015 node and proof at sec-proper-base-change/sk-prop-pbc-complete were read. No geometric route is replaced.

## Searches and reuse

Read existing DAG statements before using them, including the already split ringed tensor comparison and its construction, the diagram-site realization, exact derived factorization, derived scalar extension and the K-flat localization equivalence. Searched the whole DAG for Tags 06YS, 06YY, 03EL, 0G7E and the reduction/model/localization terminology. Ran blueprint_refs.py ancestor on the item and searches for K-flat, tensor pullback, reduction tower, strict coefficient, strict tower pullback and derived change of rings. No imported blueprint node states this exact normalization; same_as remains empty. Existing general tools suffice, so no new-node duplicate pairs require justification.

The actual new Mathlib searches are in searches.jsonl and appended to mathlib_searches with the identical tool/query strings. Two semantic phrasings were tried, alongside Loogle, LeanSearch and source grep. Read SheafOfModules.pullbackComp and conjugateEquiv_pullbackComp_inv in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean around lines 160–183: these concern ordinary pullback composition and its mate, not tensor reduction on unbounded strict towers. Read CategoryTheory/Functor/Derived/LeftDerived.lean around lines 46–80: it provides the abstract universal property, not this sheaf comparison. Read CategoryTheory/Monoidal/Tor.lean around lines 37–60: its projective-resolution homological functors do not state the required unbounded K-flat comparison. Module.Flat hits concern modules over a ring. No exact match or one-line specialization proves the item.

## Not duplicates

No new nodes were created. The proof directly reuses the stronger existing general statements instead of introducing a new lemma for each clause, elementary assembly, or scalar-extension specialization.

## Review by N5

I read delivery-errors.md B–E in full, including the merged version, and checked the draft against their specific mathematical failure cases. I read Stacks sites-modules.tex Tag 03EL (lemma-tensor-product-pullback), its bilinear-adjunction proof, and Tag 03CZ (lemma-adjointness-tensor-restrict), including its sheafification construction. For the derived part I read sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 06YT (lemma-derived-tor-quasi-isomorphism-other-side), 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change) and 07A4 (lemma-pullback-tensor-product), and derived.tex Tag 06XN (lemma-find-existence-computes), dual half. The tag-to-label table confirms these labels. The tower adaptation is agent-written and is marked as such; the published Stacks result is not represented as already asserting this particular normalization.

Step 1 uses the levelwise-abelian tower node for kernels, cokernels and exact evaluation, the inverse-system definition for strict transitions, the tensor-complex definition for the complex functor, and exact-derived-factorization for the localization comparisons. All are statements read directly. Exactness of termwise F comes from the item's specified coefficient isomorphism and its stated exactness assumption. Diagonal exactness is checked by evaluation. The index category is the small positive-integer opposite category, not a large category of sites or modules.

Step 2 uses K-flat-resolution existence with its actual flat-term conclusion. The change-of-rings quasi-isomorphism node applies to each map of commutative ring sheaves R_T to Q_{T,n}, including non-flat algebras. Restriction is checked on underlying abelian sheaves using its definition; no claim that sectionwise epimorphisms are surjective is made. The levelwise-abelian node then gives a quasi-isomorphism of whole tower complexes. This is the hypothesis needed for the next step's derived-functor criterion.

Step 3 uses the universal left-derived resolving-class theorem with target D(Tow), not a target functor category Fun(J,D). Its two hypotheses are supplied in step 2. Exactness on homotopy categories follows from the written shift and cone matrix calculation, since tensor is additive. The theorem's counit is invertible on the specified representatives, as its statement explicitly says; the proof never borrows a hidden construction from that node's proof.

Step 4 uses the diagram-site realization exactly for a small J, with constant base ring sheaf. I checked the K-flat and termwise-flat assertions by evaluation: tensoring an acyclic tower with Delta P evaluates to tensoring its acyclic nth complex with P, and kernels/cokernels evaluate levelwise. The K-flat and flat-sheaf definitions actually give those tests. Derived change of rings then computes scalar extension along Delta R to the entire algebra tower on that site. This is the elementary identification of the two descriptions of B after the cited theorems, not a new lemma that restates the item.

Step 5 uses the construction node for existence of the normalized ordinary comparison, and its definition and section calculus for the generalized pure-tensor equation and uniqueness of maps from tensor. These nodes are general small ringed-topos statements, so I did not substitute the scheme-only or constant-coefficient restriction-square node. The given ring identification and pulled-back algebra structures are the ones required here.

Step 6 uses the actual scalar-extension adjunction and insertion unit contained in the tensor section calculus, together with the restriction definition and canonical tensor comparison. I calculated the mate: extension on X followed by pullback on the Q-side sends Fm tensor Fq to F(m tensor 1)Fq. Its inverse sends F(m tensor q) to Fm tensor Fq. Both composites are identities by the pure-tensor characterization. The same calculation with q=1 gives the augmentation equation. This removes the possible mate-direction ambiguity without imposing nonzero-ring hypotheses.

Step 7 uses simultaneous naturality asserted by the ordinary comparison definition, once for the algebra transition and once for each differential. The explicit transition equation gives a strict tower map; its inverse is strict by composing that equation with the inverse components. Thus this is not an unsupported attempt to assemble derived maps after evaluation.

Step 8 uses the ringed-pullback K-flat theorem precisely with flat terms (not an unrestricted K-flat claim). The exact F sends resolution maps to quasi-isomorphisms by step 1. The site-derived-tensor descent node explicitly states W^{-1}P equivalent to D(R), which is enough for a one-variable localization; I did not infer this merely from a fully faithful Yoneda embedding or from a definition. The localization universal-property node supplies existence, uniqueness, and preservation of identities/composition for transformations. Applying it also to the inverse proves that the conjugated comparison is an isomorphism. The counit conjugation formula is written out.

Step 9 uses that same localization equivalence and universal property to extend the actual cochain augmentation. Unitality of the coefficient transitions makes its cochain map strict. The displayed cancellation proves the augmentation identity first on flat representatives and then on all derived objects by fully faithful restriction. It is not inferred from a collection of evaluated equalities in the derived tower category.

Step 10 uses exact evaluation and the resolving-class theorem for the single-level reduction. Its hypotheses have already been checked at every level in step 2. Evaluating the displayed normalized formula identifies the single-level counits via their common representative models, then localization gives the stated identification for arbitrary K. Equality of evaluations is used only for this final evaluation clause; whole-tower existence, uniqueness and augmentation were proved earlier.

For edge cases I checked the identity geometric morphism, the constant tower Q_n=R, the all-zero algebra tower, and a quotient such as Z to Z/p with an unbounded input. In the identity case the ordinary map and its descended normalization are identities under their counits. The constant R tower reduces to the diagonal. Zero tensors and units are zero as required. For Z/p the quotient need not be flat and the proof resolves the input, never identifies a derived tensor with an underived tensor of an unresolved complex. No boundedness, perfectness, completeness, Noetherian or finite-coefficient assumption enters any step. Generalized pure tensors refer to the sheafified pairing, not a false claim that every tensor section is a single pure tensor.

I checked that every cited assertion is in the node's statement and recorded the full verbatim statements in citations.json so all hypotheses are visible. No new statement-only nodes were needed; there are no hidden substitute nodes asserting the whole conclusion. All ten steps are shorter than 2000 characters. Off-unit citations are generic tensor/resolution/derived tools and are declared in split_report.tool_uses for review. No repository or launcher file was written, and no compiler or Lake tool was run.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own stage-1/stage-3 status; this delivery does not claim Lean proofs for them.
