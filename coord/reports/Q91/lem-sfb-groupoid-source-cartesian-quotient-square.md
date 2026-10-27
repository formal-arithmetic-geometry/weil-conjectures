# Q91 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-source-cartesian-quotient-square.json`: split item, unchanged statement, five proof steps; Mathlib verdict no match.
- `citations.json`: one verbatim statement quotation for each dependency cited by each proof step (12 entries).
- `searches.jsonl`: five actual search records produced by the prescribed msearch command.

New nodes: 0. Mathlib leaves: 0. All the required supporting nodes already exist.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for quotient-stack, stackification, and source-cartesian notions. No project declaration states the item. This is not an ATTACH claim; no compiler or Lake was run.

## WANTED

None: the sources needed here are in the local Stacks checkout.

## What was wrong or missing

The item was statement-only. Its statement agrees with Stacks Tag 04ZN (spaces-groupoids.tex, lemma-criterion-fibre-product), for base algebraic space equal to the base scheme, and needs no smoothness, flatness or finite-presentation assumption. It remains unchanged. I read its source proof and lemma-quotient-stack-functorial. The source proof factors through an explicit auxiliary action groupoid; this delivery instead writes a direct proof from the existing local stackification theorem and the existing fully faithful local-equivalence criterion. Consequently proof_origin.by is agent. This is a choice below the node level, leaving the unit and chapter route untouched.

The inherited blueprint.from.node is null: `python3 tools/blueprint_refs.py ancestor lem-sfb-groupoid-source-cartesian-quotient-square` returns None. I preserved it and the full non-unspecified inherited place/via. The current latest blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, in particular the unit statement and direct-images proof (3). Its current proof is shorter than the inherited provenance narrative; this generic stack/groupoid input sits below that route and changes none of it. Searches of the whole imported blueprint for `quotient stack`, `cartesian source square`, and `lemma-criterion-fibre-product` found no duplicate blueprint node. The imported chapter and unit JSON records were read too.

## Searches and reuse

No earlier sandbox split or report existed. I retained the live item's existing searches as provenance and appended only searches I actually ran. The prescribed msearch command ran grep, Loogle, LeanSearch and two LeanFinder phrasings. Grep `quotient.?stack|stackification|stackify` and Loogle `"Groupoid", "pullback"` returned zero hits. LeanSearch found ordinary quotient/free-groupoid lifting and categorical-pullback constructions. The first LeanFinder phrasing found Grothendieck cartesian lifts and the stack predicate; the second found condensed sheafification and prestack sheaf-Hom. Their displayed signatures were read: none gives the specified fppf quotient-stack comparison, nor does any specialize to it in one line. The exact queries and result digests in the appended item records match searches.jsonl. No unavailable service was reported in these five calls.

The DAG search included Stacks tags 04ZN, 02ZP, and the words fully faithful / locally essentially surjective / fibrewise equivalence across dag/nodes. Opened the full statements and proofs of lem-sfb-groupoid-stackification-local-description, lem-sfb-stack-fully-faithful-local-equivalence, lem-sfb-fibred-groupoid-equivalence-criterion, lem-sfb-chosen-object-quasi-inverse, lem-sfb-quotient-stack-invariant-base-change, and lem-sfb-action-groupoid-quotient-criterion. Also read the statement of lem-sfb-quotient-map-cartesian-action-groupoid. None is substituted for the item; the first two are precisely its existing generic tools. The arrow-sheaf observation and unique lifting computations are short steps, not new nodes.

## Not duplicates

No new nodes; therefore no new/existing tag pairs to distinguish.

## Unfinished work

None in this one-level split. Existing supporting nodes retain their own stage states. Delivery validation is reported below after the required dry run.

## Review by Q91

I read spaces-groupoids.tex Tag 04ZN, label lemma-criterion-fibre-product, including its inverse/source-to-target argument and auxiliary quotient, and its lemma-quotient-stack-functorial. The hypotheses match: two groupoids in algebraic spaces over one scheme, an actual functor on their operations, and an isomorphism of the source pullback square. The claim is about fppf stackifications, not the orbit-set sheaves. No source restriction was added or dropped. There are no new statements to audit. I also read stacks.tex Tags 02ZP (lemma-stackify-groupoids), 0436 (lemma-stackify-groupoids-universal-property), and 046N (lemma-characterize-essentially-surjective-when-ff), and checked them against the corresponding existing node statements.

Step 1 cites the stackification node for existence of the two stacks and extension of the presheaf functor with its chart comparison; that node explicitly supplies a pullback-compatible extension and invertible natural transformation. The moduli-groupoid definition is used only for its explicitly general fibrewise 2-product definition, which gives the displayed triples and arrow equation, not for its unrelated curve hypotheses. The algebraic-space definition explicitly says spaces are fppf sheaves. I checked stackhood of the product directly: descend its x component in A and its v component in V, and glue alpha in the isomorphism sheaf of D. The compatibility equation on arrows supplies the overlap condition for alpha, and the isomorphism-sheaf axiom supplies unique arrow gluing. This is an explicit application of the stack axioms, not an uncited preservation theorem.

Step 2 uses exactly the algebraic-space sheaf property, the universal property in def-weil-pbc-sheafification, and the isomorphism-sheaf clause in lem-sfb-groupoid-stackification-local-description. The endpoint equations are equations in U, so they survive gluing in R. The same holds for V,Q. The unit of sheafification is invertible on a sheaf by factoring its identity and using uniqueness; no plus-construction assertion is taken from a node that only states the universal property. Hence arrows between chart objects really are sections of R or Q over the test scheme, not merely sections after a further covering. The induced F acts on them by f1 through the specified natural comparison in step 1.

Step 3 uses the item hypothesis and step 2, so no new citation is needed. An arrow of B between comparison images has image the identity Q-arrow. The source-square isomorphism says that its prescribed source and Q-image determine it uniquely. The unit e(u) has this same source and image because f is a functor, so the arrow is e(u) and its target w is u. Conversely it exists when w=u. This proves both fullness and faithfulness, including unequal objects with the same image in V; it does not infer full faithfulness of f itself.

Step 4 uses the local-object clause of the stackification node verbatim: choose theta:a(u)->x locally. I checked the direction of every arrow: alpha:b(v)->F(x), q=F(theta)^(-1) alpha:v->f0(u), q^(-1):f0(u)->v, lifted r:u->w, and h=theta a(r)^(-1):a(w)->x. The functor laws give f0(w)=v and F(h)=F(theta)q=alpha, exactly the product's arrow equation. The source square is used at the source of q^(-1), so no unproved target-square theorem is being smuggled into this step. This establishes local essential surjectivity for an arbitrary object x, without assuming it has a global chart representative.

Step 5 uses the algebraic-space sheaf property to see U is a stack, the fppf-site and size definitions for a common universe-bounded site, the existing local-equivalence node for the actual equivalence, and the fibrewise 2-product definition to conclude the canonical square. I checked the local-equivalence node really assumes and gives fibrewise full faithfulness and covering-local essential surjectivity, and yields a pullback-compatible inverse over the site. Since the comparison projects to f0 in the discrete sheaf V, applying that projection to the counit makes its inverse also lie over V; thus the stronger wording 'over V' in the item is respected.

For edge cases I checked the identity functor (comparison is the identity pullback), discrete groupoids (R=U, Q=V, giving U = V times_V U), and one-object groupoids (the source-square condition forces the arrow-group map to be an isomorphism; it is not enough that it be injective). The empty algebraic space over a nonempty test has no local representatives in either side; on an empty test the empty-cover sheaf and stack axioms give the required unique section/object up to unique isomorphism, so the proof does not falsely treat the fibre there as empty. There is no restriction on stabilizers, characteristic, or fppf flatness of the groupoid source maps. The argument uses sheafhood of algebraic spaces and the given stackifications, which apply without those restrictions.

Checked B--E of delivery-errors.md against the files: no new node format issues, no fictitious search, no duplicate, no hidden non-elementary theorem replacing a citation, no restatement of the conclusion as a child node, no source-route alteration at the unit or chapter level. All cited statements were opened and the exact relevant quotations are in citations.json. Proof steps are 1027, 828, 601, 691, and 789 characters, so none is a long step hiding an independent lemma. No statement correction or STATEMENT-DISPUTED issue arose. No Lean or repository file was written.

## Validation

The first dry run exited 1 before pushing: its citation gate required at least 40 characters for the fppf-site quotation. Replaced that short verbatim fragment with the full verbatim statement; no proof or statement changed.

Resumed after a provider interruption: preserved the existing split, citations and logged searches, compared the sandbox item with the current live statement, and rechecked all 12 verbatim citations. No earlier delivery process remained active. The required dry run completed successfully with exit 0: `OK (not pushed) deliver/Q91/lem-sfb-groupoid-source-cartesian-quotient-square at 19f4ab950e7: preflight passed`. No mathematical or node-file changes were needed.
