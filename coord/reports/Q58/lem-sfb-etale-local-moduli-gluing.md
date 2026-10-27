# Q58: lem-sfb-etale-local-moduli-gluing

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-local-moduli-gluing.json`: split statement, seven explicit steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-etale-local-qcqs-homeomorphism.json`: one new statement-only node, unsplit; no Mathlib match after two LeanFinder phrasings, Loogle, LeanSearch and source grep.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `searches.jsonl`: actual msearch log. The item's inherited 2026-10-22 searches were retained and fresh pertinent searches appended. No search was invented.

## Attachments

None. Searches of the project `lean/WeilConjectures/` for the exact blueprint tag, uniform categorical, coarse moduli, stabilizer preservation, and stack-locality terminology found no finished declaration giving the item. Scheme gluing and scheme flat descent do not give this stack theorem. No Lean file was written and no compiler, Lake or build tool was run.

## Wanted

None for this split: all arguments use the local Stacks sources. `coord/dag-sync.md` named in the historical standing brief is absent in this clone; the user's live-repository instructions specify the applicable paths.

## Corrections and source comparison

STATEMENT-DISPUTED: the imported inline definition of quasi-separated was only “quasi-compact relative diagonal”. This fails the definition check against stacks-morphisms.tex definition-separated, clause (4), which requires a quasi-compact AND quasi-separated diagonal; compare the already existing def-sfb-stack-qcqs-morphism. The statement now explicitly uses that project definition in both hypotheses and conclusion. This repairs the meaning faithfully to the source, rather than claiming that scheme terminology automatically applies to a nonrepresentable stack morphism. There is no added finite-inertia, finite-type, DM or separatedness hypothesis.

Removed the unrelated affine-groupoid quotient paragraph and its dependencies: this item has general algebraic stacks and no specified affine groupoid. Replaced the adequate-moduli definition citation with the actual algebraic-stack definition. Added explicit 2-fibre-product, size and algebraic-closure references. No adequacy of the glued map is claimed or needed.

The source's cartesian comparison invokes an etale-isomorphism criterion and uses a separated diagonal of its finite-inertia stack. The present item has not assumed that hypothesis. Instead, base change of the comparison by each original cover member identifies it with the GIVEN cartesian overlap square. Isomorphism-sheaf descent gives full faithfulness, and the existing fully-faithful/local-essential-surjectivity criterion finishes. This is the same cartesian-comparison objective inside the Keel--Mori gluing argument, without borrowing an unavailable hypothesis.

The current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md` was read, especially (3), together with the unit and chapter records and SETUP's three-level rule. This is a lower auxiliary in the imported alteration/moduli branch, not the unit's key statement: no unit file or route was edited. `blueprint_refs.py ancestor` currently returns None for this inherited created.item chain. The item's existing `from.node: null` and via chain are retained, and the new node uses the same ancestor result with the item prepended to via; the exact supporting place is filled. Searches of the whole imported blueprint for moduli, uniform categorical, etale equivalence, locality and the relevant tags found no duplicate blueprint theorem.

## Not duplicates

lem-sfb-stack-etale-local-qcqs-homeomorphism vs lem-sfb-dm-etale-atlas-calculus: the existing statement is DM-only atlas and etale-map calculus; it does not state qcqs or universal-homeomorphism descent for general stacks.
lem-sfb-stack-etale-local-qcqs-homeomorphism vs lem-sfb-stack-coarse-properties-etale-locality: the existing statement assumes DM source and target and treats separated, quasi-compact and universal homeomorphism; the new statement allows arbitrary algebraic stacks and supplies quasi-separatedness, which is needed here. The existing node cannot be applied to this item's non-DM stacks.
lem-sfb-stack-etale-local-qcqs-homeomorphism vs lem-sfb-etale-local-moduli-gluing: the item constructs a relation, its quotient and a cartesian global moduli morphism; the new lemma only descends three morphism properties along a GIVEN target cover, with no moduli or relation data.
lem-sfb-stack-etale-local-qcqs-homeomorphism vs lem-sfb-etale-stabilizer-preserving-affine-moduli: the existing statement constructs affine-quotient charts for special finite-flat-covered stacks; the new statement assumes any target cover and descends qcqs/homeomorphism, with no quotient construction or finite-flat cover.

The tag scan of every current nonmerged source record found precisely these four source-tag pairs. The two existing geometric-equivalence and etale-quotient nodes were reused instead of duplicated. The geometric isomorphism-class fibre-product calculation is an elementary step, not a new lemma node. The new locality theorem is a generic tool with strictly different hypotheses and purpose from the item, and its proof remains empty as required.

## Review by Q58

I read the whole Keel--Mori gluing passage in stacks-more-morphisms.tex, theorem-keel-mori (0DUT), from the overlap squares through equation-fundamental-diagram (0DUU) and its cartesian comparison. I also read groupoids.tex lemma-etale-equivalence-relation (0DT7), spaces.tex theorem-presentation (02WW), and the general-stack descent statements and definitions in stacks-morphisms.tex. For the sole new node I read lemma-check-separated-covering (06TZ), including its quasi-separated clause, lemma-check-quasi-compact-covering (0DTL), lemma-check-universal-homeomorphism-covering (0DTQ), and their base-change lemmas 050F, 050V and 0CI8. These state general-stack properties and do not require DM or finite inertia. The family formulation is obtained by the small disjoint coproduct of the cover spaces; inverse images of affine tests of a disjoint union lie componentwise, so the three properties on the coproduct map are exactly the componentwise properties. The new node is not presented as a proof of gluing.

For step 1 I opened lem-sfb-algebraic-stack-fibre-products, lem-sfb-stack-chartwise-smooth-etale-calculus and lem-weil-pbc-scheme-coproduct-family. The first supplies algebraicity of the actual triple 2-fibre product; the second supplies etale base change and etale implies flat, so the uniform-categorical hypothesis genuinely applies to the flat map P_ijk to M_ij. The third supplies the small scheme coproduct and its disjoint open components. Composition is factored through the categorical map of the triple, not through an unproved arbitrary base-change theorem. Endpoint compatibility follows from injectivity in categorical factorization. A full groupoid-law theorem is unnecessary: 0DT7 only needs the three displayed endpoint identities.

Step 2 uses no non-elementary input: I wrote the isomorphism-class calculation. Surjectivity uses an actual isomorphism between the images; injectivity adjusts that isomorphism using the SURJECTIVE automorphism map furnished by stabilizer preservation. The point bijection for f_ij is deduced from its assumed cartesian square with f_i, rather than silently assumed from the categorical property. This remains valid with nontrivial automorphism groups, such as a chart B G, since pi_0 is classes, not objects or arrows. Dropping stabilizer preservation would invalidate precisely the adjustment of the two isomorphisms, so that hypothesis is used.

For step 3 I opened lem-sfb-unramified-geometric-equivalence-relation: its statement gives monomorphism and the all-test-scheme equivalence relation once etale projections, e/i/c and the geometric relation are established. All those inputs were checked in steps 1 and 2. I then opened lem-trf-etale-relation-quotient: its statement explicitly includes algebraic-space representability, the etale surjective quotient map AND the kernel-pair isomorphism. That last clause, not merely representability, gives every M_ij = M_i x_Q M_j. This is an off-unit generic tool, declared in split_report.tool_uses; no step of the unit route is replaced by a different route.

For step 4 I opened def-trf-algebraic-space and the chartwise calculus. The definition actually says fppf sheaf, which is exactly the gluing and uniqueness used. Pullbacks T_j can be algebraic spaces, so I explicitly refine by scheme etale charts before applying the sheaf condition. Joint surjectivity and etaleness survive the refinements by the cited calculus. I filled the source's omitted verification of compatibility with base change and isomorphisms of a by uniqueness after the same cover, producing an actual morphism of stacks.

For step 5 I opened def-sfb-algebraic-moduli-stack and lem-sfb-stack-fully-faithful-local-equivalence. The latter requires globally fibrewise full faithfulness, not just a vague locally bijective assertion. I checked it first using the isomorphism sheaf axiom and its unique gluing, then used local equivalence over the original etale cover to establish local essential surjectivity. The map after each pullback is the assumed projection-square comparison with its specified maps, so no separated diagonal, DM hypothesis or geometric-point isomorphism criterion is smuggled into this argument. The source and target fibre products are algebraic by the general fibre-product input; their stack descent follows from their stack definitions.

For step 6 I checked that the new locality statement applies to a small cover of Q by scheme algebraic spaces, while q itself can be nonrepresentable. The base changes are identified with exactly the original f_i in step 5, giving all three required hypotheses individually. The corrected quasi-separated convention is the SAME on both sides. In particular the DM-only existing locality node would not justify this step.

For step 7 I opened lem-weil-pbc-etale-cover-geometric-point-lift and verified that it supplies a lift over the SAME algebraically closed field. The scheme hypothesis is met by first taking scheme etale charts of each pullback, for both covers used. The kernel-pair identity and step 2 then prove injectivity on isomorphism classes; surjectivity follows from the given local f_i bijections. No identification of Q(Omega) with a presheaf quotient without a lift is asserted.

I checked all seven texts against C1/C4, copying each quoted sentence from the node statement into citations.json, and checked B--E: statements introduce their objects, definitions and tag labels are explicit, no unsplit-node proof was filled, no one-clause relabelling is created, and no dependency uses a parent's proof. No proof step exceeds 2000 characters. I tested the empty index family (joint surjectivity forces X empty, and Q is empty), empty individual charts, a single chart, repeated identical charts, and stack charts with nontrivial stabilizers. The identity-cover case of the new node is tautological; an infinite cover does not require W or X to be globally quasi-compact, because quasi-compactness is relative to affine tests. The conclusions do not assert global quasi-compactness or separatedness of Q. Mathlib hits only concern scheme gluing, scheme flat descent and scheme diagonals; they were read and do not match general stacks. The new node is therefore unsplit, not a Mathlib leaf.

## Unfinished work

No part of the item's split is deferred. The single new general locality statement is intentionally not split, as required by one-level stage-1 delivery. Validation and delivery results are recorded below after the required commands exit.

## Validation

The required dry run exited 0 and printed `OK (not pushed) deliver/Q58/lem-sfb-etale-local-moduli-gluing at 9897bf47480: preflight passed`. This includes the server preflight, DAG and split checks, as well as delivery-side verbatim citation, actual-search and source-tag duplicate checks. The source/statement review above was completed before the dry run. There is one new node and zero Mathlib leaves. Delivery is direct under the user's current brief; the tool's generic “second-reader handoff” receipt text does not override that authorization.
