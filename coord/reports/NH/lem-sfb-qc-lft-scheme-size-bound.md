## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-qc-lft-scheme-size-bound.json: item, split into four steps; statement unchanged; no Mathlib match.
- lem-sfb-affine-scheme-size.json: statement-only prerequisite, Stacks 000P (lemma-bound-affine); unsplit, no Mathlib match.
- lem-sfb-open-cover-scheme-size.json: statement-only prerequisite, Stacks 000Q (lemma-bound-size), with the empty-cover correction; unsplit, no Mathlib match.

citations.json quotes every cited statement for its exact step. searches.jsonl contains the actual msearch results, used verbatim as the results records in the new nodes.

Attachments: none. I searched lean/WeilConjectures by the item's blueprint tag, scheme-size/cardinality terminology, and the new notions; no project declaration gives these size estimates. Neither a sorry proof nor Mathlib's structural SizeOf of an affine cover is evidence of an attachment.

WANTED: none. The source is available as literature/stacks-project/sets.tex. I read section-categories-schemes (the size definition), lemma-bound-affine (000P), lemma-bound-size (000Q), and lemma-bound-finite-type (04T7), and verified these tag-label pairs in tags/tags.

What changed: the item's empty proof is now the proof of 04T7: choose finitely many affine finite-type charts, bound each chart's ring by finite expressions, use 000P on the charts, and use 000Q to reassemble X. No statement, target, unit or chapter was changed. The two new lemmas are genuinely independent supporting facts: one concerns an arbitrary affine scheme without a morphism to a base, and the other an arbitrary open covering without finite-type assumptions. Neither repeats a clause of the item's conclusion.

The existing blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor; I preserve that inherited root and extend its via chain in the two new nodes. I read the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md: paragraph (3) now uses compactification, whereas the inherited breadcrumb names an older alteration reduction. This subordinate split expands the seeded Stacks size input only; it does not change the current unit route or claim the latest blueprint itself states a size estimate.

Unfinished: the proofs of the two new statement-only supporting nodes are intentionally left to their own stage-1 items, as the one-level split requires. No obstacle to the item's assembly remains.

## Source error

STATEMENT-DISPUTED: the displayed inequality in Stacks 000Q omits the empty-cover case. Take Y empty and I empty: s(Y)=aleph_0 by the definition, but max(|I|,sup_i s(Y_i))=0. The new open-cover node includes aleph_0 in the maximum. This agrees exactly with 000Q for a nonempty index set and gives the correct empty-cover bound. The item 04T7 is true as written, including X empty, so its statement requires no correction. This edge case was also noticed in the earlier bounded-affine-lft-coproduct review.

For the future split of 000P, its source counts finite lists of principal opens, then injects sections on an affine open into the product of sections on a finite principal covering; the localization fraction estimate is the remaining algebra input. For 000Q, its source refines an affine open by finitely many affine opens in the covering members and uses the sheaf uniqueness axiom to bound sections; finite-list cardinality bounds the possible unions. These are source-reading notes, not proofs inserted into the new statements. In particular, no intersection of two affine opens is assumed affine or quasi-compact.

## Not duplicates

lem-sfb-open-cover-scheme-size vs lem-sfb-qc-lft-scheme-size-bound: the former is a size inequality for arbitrary open coverings, independent of morphisms and finite-type hypotheses; the latter needs chart selection and the finite-type algebra cardinal bound to compare X with a separate base S. The shared 000I reference locates only the inline scheme-size definition, not a theorem identifying the two statements.

lem-sfb-open-cover-scheme-size vs lem-sfb-bounded-affine-lft-coproduct: the latter places a particular coproduct of locally finite type affine schemes in a fixed big fppf site; the new node gives a numerical size estimate for any scheme and any open covering, without a site or base scheme.

lem-sfb-open-cover-scheme-size vs lem-sfb-big-site-open-cover-size-closure: the latter concludes existence of a representative in a specified big fppf site under a bound relative to T; it does not state the numerical open-cover size inequality needed here. It uses 000Q but does not expose its statement.

lem-sfb-affine-scheme-size vs lem-sfb-qc-lft-scheme-size-bound: 000P computes the absolute size of an arbitrary affine scheme from its own global ring; 04T7 bounds the source of a locally finite type morphism over an unrelated, possibly non-quasi-compact scheme. The new node does not carry the finite-type or finite-cover assembly argument.

I searched the whole DAG by 000P, 000Q, lemma-bound-affine, lemma-bound-size, scheme-size wording and cardinal/affine keywords. The only tag hits with relevant statements are the two big-site/coproduct nodes above; other hits are historical review prose. tools/blueprint_refs.py searches for size, cardinality, finite type, affine open, scheme size, 000P, 000Q, bound-affine and bound-size found no blueprint node stating either size estimate. The existing lem-trf-lft-finite-relative-affine-atlas imposes qcqs on several schemes and bounds no cardinalities, so it cannot replace this general finite chart selection. The existing lem-weil-pbc-finite-list-cardinality is reused rather than duplicated.

## Review by NH

I read the Stacks source and each cited node's statement with the split open. The item's hypotheses and conclusion agree with 04T7: only X is quasi-compact, f is locally finite type, and s uses all affine opens and their section rings. The target S need not be quasi-compact or quasi-separated. For the two new nodes, 000P gives exactly the affine equality, including the lower bound from Y itself as an affine open. 000Q gives the general open-cover bound, corrected explicitly above for the empty family. Both new statements introduce their schemes, indexing sets and the meaning of s; they have only definition dependencies, no proof sketch or hidden proof dependencies.

Step 1 uses lem-weil-pbc-affine-opens-basis for a covering of S by affine opens. def-weil-finite-type-morphism says for every affine V=Spec A the whole preimage has an affine covering with finitely generated coordinate algebras. Those coverings together cover X; def-weil-pbc-quasi-compact-scheme then supplies a finite subfamily. def-weil-affine-spectrum identifies the rings on the chosen charts. I specifically checked that no claim is made that f inverse V is quasi-compact, or that an arbitrary affine chart has a finite-type section map. We select the particular charts provided by the definition. This is a direct two-line application of the definitions once the basis statement is cited, hence elementary.

Step 2 uses exactly the inequality in lem-weil-pbc-finite-list-cardinality: lists on any set have cardinal at most max(aleph_0, cardinal of the set). I read its Mathlib match Cardinal.mk_list_le_max at Mathlib/SetTheory/Cardinal/Arithmetic.lean:746-750. A finite-type algebra is generated by polynomial expressions, which are valid finite words over constants and a finite list of symbols; adjoining finitely many symbols does not exceed max(aleph_0,|A_i|). Restrict to syntactically valid words and evaluate, a surjection onto B_i. Thus this short encoding needs no separate polynomial-cardinality lemma. The alphabet can be finite; the max with aleph_0 handles that case. No algebra presentation with finitely many relations is assumed. I checked zero generators and zero rings.

Step 3 cites the new affine-size node for its equality, not an argument hidden in its proof. Its hypothesis is just that U_i is affine, already supplied in step 1. Step 4 cites the new open-cover-size node for its displayed inequality; its index set is the finite chosen family, and its members carry the induced open structures. Taking the maximum with aleph_0 handles an empty family directly, and taking the supremum of the chart bounds yields s(X) <= s(S). These two steps are marked non-elementary because the size estimates are genuine independent lemmas; the arithmetic after applying them is immediate.

I tested X empty and S empty (a morphism to the latter forces X empty), S=Spec F_2 with X affine space, the zero ring, a finite field, an uncountable coordinate ring, and a finite cover of a nonseparated source. I also checked that the open-cover node allows an infinite index set and repeats of a member. No separation hypothesis or affine-intersection claim enters the assembly or either new statement. The empty-cover source defect was corrected before delivery. Every step is shorter than 2000 characters; the assembly is under 3000 characters and no standard comparison is hidden in it.

For the Mathlib audit I read all returned hits from two semantic phrasings per new node, Loogle and source grep. AffineScheme, IsAffineOpen.Spec_basicOpen and cover/refinement declarations do not count affine opens or their sections. The sizeOf_spec hits concern structural recursion SizeOf, not cardinality. Neither new node is a Mathlib leaf. All searches in their records were actually executed with msearch.py; no failed service is recorded as absence. The finite-list bound already has a Mathlib leaf and is reused. Both new nodes inherit the item's unit, and all other proof dependencies are definition nodes or Mathlib leaves, so no off-unit tool-use declaration is required. No new dependency points back to this item or to its ancestors.
