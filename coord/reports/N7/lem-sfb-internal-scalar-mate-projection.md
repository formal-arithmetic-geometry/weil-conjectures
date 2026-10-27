# Stage-1 report: lem-sfb-internal-scalar-mate-projection

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-scalar-mate-projection.json`: statement, split into seven proof steps; no Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report and the author's mathematical review.

New nodes: 0. Mathlib leaves: 0. `split.py` is a sandbox-only authoring script; `searches.jsonl` is the search command's own log. No unit or chapter record is changed: this item is not the unit's key statement.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the item id, internal scalar/mate terminology and scalar projection terminology. Read `SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`, the mate section of `CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean`, and `SixFunctors/ProEtale/ScalarExtensionProjectionIso.lean`. The first defines derivedPullIso/derivedPushHom under an exact coefficient-extension hypothesis and does not identify their restriction with this projection map. The last concerns ordinary sheaves with fixed discrete coefficient rings, not the arbitrary unbounded internal coefficient mate. No project declaration supplies every clause of this item under its hypotheses.

## WANTED

None. All references needed for this split are present locally.

## What was wrong or missing

The item was a statement-only node. Its statement is well-typed and was retained verbatim. Its two displayed identities were not already consequences of any completed project declaration found in the attachment search. No source error, statement dispute or change of the unit's route was needed.

The blueprint's proper-base-change integral proof, paragraphs (1) and (3), asserts compatibility of the actual canonical reduction maps without spelling out this comparison. The split supplies the representative calculation and then the two explicit adjoint transposes. The expanded proof is marked agent-written; it does not attribute this entire expanded lemma to a Stacks statement.

In particular, restriction along a possibly nonflat coefficient map is not claimed to preserve K-injectives. The direct-image comparison and its adjunction equation are used from `lem-weil-pbc-ring-sheaf-change-adjunction`, whose statement constructs the comparison through composite ringed-topos direct images without that false preservation assertion. Similarly the scalar sheaf itself is not assumed K-flat: step 2 uses its own K-flat resolution.

## Not duplicates

No new nodes are created. For clarity, the related existing nodes do not remove the work of the item:

- `lem-sfb-internal-scalar-projection-mate` assumes exact scalar extension on every scheme, whereas the present statement has arbitrary coefficient maps. It is not used.
- `lem-sfb-derived-scalar-mate-thick-locus` concerns section-ring coefficients with its own normalized comparison and adds thick-locus conclusions; its projection clause alone does not establish the first explicit equation for the fixed internal maps of this item. It is not used.
- `lem-sfb-internal-scalar-pullback-normalization` supplies the representative formulas and the adjunction transport. It does not itself assert the projection identities. It is cited for exactly those formulas; the equations are proved in the item.

## Mathlib and blueprint searches

Kept all six inherited searches and their results. Ran six additional searches using the required msearch command: LeanSearch, Loogle, two LeanFinder phrasings, and two grep patterns, all available and recorded exactly in `searches.jsonl` and the item's `mathlib_searches`. LeanSearch returned ordinary scalar-restriction declarations. The first LeanFinder returned ordinary sheaf pullback/free-unit maps and their adjunction equations; the second returned ordinary ModuleCat extension/restriction counit and unit calculations. Loogle found no joint projection/mate declaration. The broader grep found general closed-monoidal mate identities. These do not state the normalized unbounded internal-module assertion.

Read the source of the principal search candidates: Mathlib `Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` lines 27–45, `Sheaf/PullbackFree.lean` lines 80–107, and `CategoryTheory/Monoidal/Closed/Functor.lean` lines 74–103. The first is ordinary restriction, the second the ordinary pullback-unit transpose, and the third exponential comparison in closed categories. None is an exact match or one-line specialization for the present item.

Searched the whole DAG for scalar normalization/mate and projection terminology, and searched the imported blueprint with `tools/blueprint_refs.py search` for `projection`, `scalar mate`, `scalar projection`, and `coefficient mate`. Reviewed the relevant same-concept node statements listed above. The blueprint matches concern different finite/compact-support or open-image assertions. No blueprint node states this item exactly. The ancestor command confirms `det-thm-sfb-proper-base-change-integral`; the existing precise origin through `lem-sfb-integral-quotient-direct-image-comparison` is retained, with `same_as: []`.

## Review by N7

I read the chapter `sec-six-functors-basics`, unit `sk-thm-sfb-proper-base-change`, and the current main-20261015 integral proof in the item's source. This item makes explicit the actual map in paragraphs (1) and (3). It does not replace the finite-coefficient route or introduce a purity argument. I also read Stacks sites-cohomology.tex, Tag 07A4 (`lemma-pullback-tensor-product`, lines 3683–3724), Tags 07A6/0D6E (derived adjunction and composition, lines 3989–4030), Tag 0B56 (the projection-map definition, lines 13660–13679), Tag 0G7E (K-flat pullback, lines 3505–3518), Tag 06YP (K-flat tensor preserves quasi-isomorphisms, around line 3011) and Tag 06YS (flat-term K-flat resolutions, around line 3207). Read the ordinary ringed tensor construction in sites-modules.tex, Tag 03EL, around line 3649. Checked each tag against `stacks-project/tags/tags`. No SGA source is used. There are no new nodes with additional sources to review.

For step 1 I opened the complete statements of the normalization lemma, the internal/section tensor comparison, the exact pro-etale operation definition, the K-flat resolution lemma and pullback-preserves-K-flat lemma. Their precise content is what is needed: the section equivalence identifies total tensor and K-flatness, the normalization lemma identifies the actual adjunctions with units and counits, and the two K-flat lemmas apply to all unbounded complexes on the small sites. The coefficient identifications are cartesian, so the ordinary module pullback is exact. This is why a nonflat scalar map is harmless; it is not an assertion about arbitrary noncartesian ringed pullback.

For step 2 I checked that the statement of the ringed derived tensor lemma explicitly gives total-tensor computation on K-flat representatives and that the module-object projection definition specifies the ordinary tensorator and derived computation counits. The ordinary comparison definition contains its pure-tensor equation. The K-flat quasi-isomorphism node applies to the auxiliary resolution Q -> S_Y[0], with P as the K-flat tensor factor; symmetry puts P in its stated slot. After pullback the same hypothesis holds for H_R P. Exactness of identified-coefficient pullback supplies the other comparison. This avoids assuming the scalar sheaf is flat, a frequent erroneous shortcut. Every representative arrow cancelled here is a localized quasi-isomorphism.

For step 3 I checked b's definition in the ring-sheaf adjunction statement, rather than substituting an arbitrary restriction/pullback isomorphism. The normalization lemma gives the actual generator formulas for e and lambda. Both paths therefore induce the same balanced bilinear map, written explicitly in the step. Equality is of sheaf maps, then chain maps, then their localizations, not an appeal to element detection in the derived category. With the auxiliary Q resolution, the augmentation kills degrees other than zero and there is no Koszul sign from the degree-zero scalar. This is a routine computation from the cited statements and the representative maps of step 2, not a separate lemma node.

For step 4 I read the entire final adjunct equation of `lem-weil-pbc-ring-sheaf-change-adjunction`. It applies with M=D_Y F K, N=D_X K and t=D_X(epsilon_K) lambda_(F K), with the inverse b on the required side. It gives precisely d V(rho), not just an unnamed isomorphic map. Postcomposition under the hom bijection and naturality of e_X yield the displayed adjunct; both are formal naturality equations. The interface definition is used only to fix rho as this S-adjunct, not as evidence that the comparison equation already holds.

For step 5 the only additional node is the definition of the specified module-object projection arrow: its statement gives exactly the counit transpose used here. Moving c past epsilon is tensor bifunctoriality; injectivity of the adjunction hom bijection proves equality. This retains the postcomposition F(1 tensor c) in the item's convention. There is no reliance on any theorem saying the projection arrow is invertible.

For step 6 I checked tensor transport separately from ordinary categorical equivalence. The internal/section tensor comparison preserves the underlying pure tensors and total complexes. The internal projection definition and ringed tensor lemma compute their comparisons by those ordinary maps. Thus the same P,Q representative calculation identifies the tensor arrows, and the normalization lemma separately supplies equality of the specified units and counits. The section equation is then obtained by applying the equivalence to the proved equality and recognizing its identical transpose. This spells out the transport, rather than using that word to hide map compatibility.

For step 7 the normalization statement gives natural e and lambda, the ring-sheaf adjunction statement gives natural b,d and reflects isomorphisms, and the tensor comparison and projection definition are natural. The explicit counit equation proves naturality of rho. Since e and d are isomorphisms, the second identity makes V(rho) invertible exactly when pi is; reflection then proves the iff. No flatness, properness, boundedness, finite-type or completeness hypothesis entered any step.

I tested the formulas with f the identity (all geometric maps become identities and rho is the scalar identity), a the identity (the tensor unit case), S=0 and K=0 (the corresponding arrows are zero-object isomorphisms), and the genuinely nonflat coefficient map Z -> Z/2 on the point. In the last case the scalar sheaf is not flat; P tensor S still computes the derived tensor, and the auxiliary Q argument remains valid. These tests do not prove the theorem, but they check the direction of lambda, the inverse b, the placement of c, and the absence of hidden flatness assumptions.

Checked the B–E requirements individually: no new-node form, duplication or relabelling issues arise; every non-elementary ingredient is an existing cited statement; no proof of a cited node is used as an interface; all statements were opened and quotations are copied verbatim in citations.json; unit and chapter routes are preserved; the precise source and hypotheses are recorded above. No proof step exceeds 2000 characters. The elementary steps consist of the explicit balanced-map calculation and formal naturality/adjunction manipulations, after the non-elementary representative and comparison results have been cited. The generic off-unit tools are declared in split_report.tool_uses with their purpose, rather than changing top-level tool_uses.

## Unfinished work

No mathematical portion is left unfinished at stage 1. The existing cited lemma nodes remain responsible for their own proofs. Delivery validation and push are performed after this report is written.
