# Stage-1 report: lem-sfb-ample-pullback-qc-immersion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ample-pullback-qc-immersion.json`: item split into four steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ample-nonvanishing-basis-criterion.json`: one new statement-only unsplit node, Mathlib no match.
- `citations.json`: verbatim statement quotations for all six step/node citations.

One new node; zero Mathlib leaves. No Lean source was written or compiled.

## Attachments

None. I searched the project's WeilConjectures sources for the exact blueprint tag and ample/pullback/restriction/immersion notions. `Scheme.Modules.isAmple_tensorPullback_of_isAffineHom` in `AlgebraicGeometry/AmplePullback.lean:47` only treats affine morphisms, so it does not finish this item. `AlgebraicGeometry.IsAmple.pullback` in `Modules/VeryAmple.lean:151` assumes projective schemes over a field and a closed immersion and uses the other ample notion. Neither gives the present arbitrary quasi-compact immersion statement. The existing `lem-weil-pbc-invertible-pullback-tensor` is Lean-closed and already attached; I reuse its full statement.

## WANTED

None. All source material used is in the read clone.

## Audit and route

I read Properties `lemma-ample-on-locally-closed` (0B3E), including its reduction of (2) to (4), and `proposition-characterize-ample` (01Q3), especially (1) iff (3). I also read its cited `lemma-affine-s-opens` to check that the criterion does not assume its basis opens affine. I read Modules `remark-pullback-s-open` (0H78). The item is correct as imported: there is no statement dispute.

The important distinction is between an intrinsic topological basis of nonvanishing loci and affine loci in the definition of ampleness. Inverse images of affine opens under an immersion need not be affine, so the argument does not assert this. It instead uses the general basis criterion in both directions. The new criterion is an independent theorem about one invertible module, with no morphism or pullback, not a clause of the item renamed.

I read SETUP's chapter/unit/node levels, the item chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability` statement and proof. The existing ancestor command reports `from.node = None`; I preserve the inherited null ancestor and full via-chain rather than inventing a blueprint ancestor. The recorded place identifies the ample restriction used by `lem-sfb-lft-group-quasicompact-open-ample` in that chain. This is a generic geometry auxiliary below the unit, not a change to a chapter or unit route. No off-unit open statement is newly used: the pullback/tensor/fibre tool is already closed.

Whole-DAG searches used 0B3E, 01Q3, proposition-characterize-ample, nonvanishing/basis, ample/basis, and the prospective new id. Whole-blueprint searches used `ample pullback`, `characterize-ample`, `nonvanishing`, `nonvanishing loci`, `basis for the topology`, `topological basis`, `01Q3`, and `ample`. None states this general equivalence. The proper-over-a-field `lem-pc-ample-affine-loci-criterion` cannot be applied on the present X or Y. A Proj embedding alone in `lem-sc-ample-proj-open` does not state how the relevant sections correspond, and is not used as that missing statement.

All new Mathlib-search entries are exact msearch.py queries, with the original result records retained. Both semantic phrasings of the new criterion returned results about structure-sheaf basic opens and quasi-affineness. `Scheme.IsQuasiAffine.isBasis_basicOpen` assumes quasi-affineness and concerns O_X, not arbitrary invertible modules; the denominator-clearing hits concern functions and cannot be a one-line specialization to this criterion. Loogle and the targeted Mathlib grep return no IsAmple result. The separate item queries return immersion/base-change facts, not ampleness. No service failure was treated as absence.

## Review by Q02

For step 1 I checked that the definition node explicitly includes quasi-compactness of X, and that the new criterion states the forward implication for exactly an arbitrary quasi-compact scheme and invertible module. That justifies using it on X with no finite-type or field assumption.

For step 2 I reopened `lem-weil-pbc-invertible-pullback-tensor`: clause (1) gives invertibility of i^*L; clause (2) gives the tensor comparison, which is iterated on the n factors; clause (3), applied to L^n, gives the residue-fibre section formula. Each assertion is in the quoted statement, not inferred from its proof. Preservation of a nonzero vector under a field extension is written out using a basis coefficient. This proves the exact equality of nonvanishing sets, rather than merely one inclusion. The conventions and openness of these loci are in the ample definition node.

For step 3 I reopened both immersion definition nodes. They explicitly identify their sources with closed and open subspaces. Their composite therefore has the subspace topology; the proof writes an arbitrary open V as i^{-1}(W) and then applies the preceding basis refinement to i(y) in W. This is the elementary two-subspace argument, with no unmentioned theorem about schemes and no assumption of an affine preimage. Tensor-power sections constructed in step 2 are among all positive-power sections, so having the former refine every neighborhood proves the criterion for the latter as well.

For step 4 I checked the reverse implication in the new statement and the quasi-compactness hypothesis Y actually has. Invertibility was established in step 2 and the basis refinement in step 3, so this is a valid application of 01Q3 to Y. The proof establishes both clauses of the item. There are no steps longer than 2000 characters and no hidden comparison lemma: the only geometric comparison used is already explicitly in the closed fibre/tensor node.

For the new node I checked its whole statement against 01Q3(1),(3), and that every introduced scheme, invertible module, tensor power, quasi-compactness and nonvanishing locus is defined inline or by its actual definition node. It remains statement-only, with empty proof and proof_deps. It does not cite a proper-over-field definition of ampleness. I checked every listed dependency in the item by verbatim citations.json quotations.

Small cases: for empty X or Y the pointwise basis condition is vacuous and quasi-compactness holds; the conclusion is still correct. Nilpotents do not affect the residue-field nonvanishing computation and no reducedness was used. For the quasi-compact open immersion A^2_k minus the origin into A^2_k, the preimage of the whole affine target need not be affine, confirming why the basis route is needed. A non-Noetherian affine base is allowed throughout. The new node's quasi-compact hypothesis is essential: an infinite discrete union of copies of Spec(k) has O_X with characteristic-function nonvanishing loci giving a basis, but is not ample in the definition that requires quasi-compactness. It is therefore retained explicitly, and nowhere inferred just from a cover by nonvanishing opens.

I checked delivery-errors B--E: the sole new node is self-contained, sourced by the correct tag and label, searched before creation, and is neither an elementary topology fact nor a duplicate nor a restatement of the item. Every non-elementary step cites its actual statement-level input; the one elementary step contains its full argument. The hypotheses are carried at each use. I corrected no imported statement and used no SGA source.

## Not duplicates

- lem-sfb-ample-nonvanishing-basis-criterion vs lem-trf-affine-eventual-power-immersion: the existing statement constructs projective immersions for eventual powers over an affine base under a local-finite-type hypothesis; the new statement is an intrinsic basis equivalence without a base or finite type.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-pc-very-ample-ample: the existing statement starts with a closed immersion into finite projective space over a field; the new statement is a topology criterion for any quasi-compact scheme.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sfb-ample-curve-first-jet-interpolation: the existing statement interpolates first jets on smooth proper integral curves; the new statement has no curve or field hypotheses and no interpolation conclusion.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sfb-linearized-ample-eigen-affine-cover: the existing statement constructs invariant eigensection affine neighborhoods for a linearized torus action on a normal finite-type scheme; the new statement concerns all nonvanishing loci without an action or affineness requirement.
- lem-sfb-ample-nonvanishing-basis-criterion vs def-sc-ample: the existing definition uses very ample powers on proper schemes over a field; the new result equates absolute ampleness with a basis condition on arbitrary quasi-compact schemes.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-weil-pbc-coherent-twist-global-generation: the existing statement gives eventual global generation of twisted finite-type quasi-coherent modules; it does not assert the basis condition or its converse.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-weil-pbc-formal-systems-graded-vanishing: the existing statement is graded cohomology vanishing over a complete Noetherian base, not an intrinsic basis characterization.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-weil-pbc-vanishing-projective: the existing statement is H^1 vanishing for a coherent formal system on a proper scheme over a Noetherian ring; it does not give either topology-basis implication.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-ample-proj-open: the existing statement provides an open embedding into some Proj for an ample scheme; its statement gives no correspondence between homogeneous standard opens and nonvanishing loci and no converse basis criterion.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-ample-pullback-ideal-affine-section: the existing statement assumes the pullback is already ample and produces an ideal-supported affine section; it does not detect ampleness from a non-affine basis.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-ample-ideal-section: the existing statement produces a section in an ideal twist at a point outside its support; it neither states a general open-neighborhood basis nor the reverse implication.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-reduced-dim-le-one-ample: the existing statement constructs some ample module on a reduced Noetherian separated curve; the new statement detects ampleness of a given line on any quasi-compact scheme.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-component-supported-affine-section: the existing statement produces a section near a point on exactly one component of a reduced Noetherian scheme; the new statement has no component or reduction hypotheses and includes a converse.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-sc-ample-finite-affine-cover: the existing statement gives a finite affine nonvanishing cover, not refinement inside every open set or the converse from an arbitrary nonvanishing basis.
- lem-sfb-ample-nonvanishing-basis-criterion vs lem-pc-ample-affine-loci-criterion: the existing node assumes properness over a field, assumes affine covering loci, and concludes the very-ample-power notion; the new theorem has neither properness nor a field, does not require affine basis loci, and includes both implications.

## Unfinished work

The new basis criterion is deliberately unsplit, as required for a one-level split. No part of the item's proof remains implicit. Server dry-run results will be recorded below.
