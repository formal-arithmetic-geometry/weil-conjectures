# Stage-1 worker report: lem-sfb-finite-quotient-generic-fields

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-generic-fields.json: existing statement, split into eight proof steps, no exact Mathlib match for the whole statement.
- citations.json: one verbatim statement quotation for each of the fourteen step/node citations.
- report.md: this report. Searches are retained in searches.jsonl.

No new nodes; zero new Mathlib leaves. Only the sandbox was written. No Lean files, compilers, Lake, builds, repository git commands, launcher modifications or agents were used.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, quotient/generic-field terminology and invariant/fraction-field terminology found no declaration stating the whole item. The nearby inertia, strict-henselian invariants and generic-fibre quotient declarations concern different objects or stronger hypotheses. Mathlib's IsFractionRing.isInvariant, RingTheory/Invariant/Basic.lean:510, concerns fraction fields after a fixed-subring hypothesis has already been established for a single factor. It supplies neither the component-orbit bijection nor the reduction to the component stabilizer, and is not an attachment. Its short denominator argument is written explicitly in Step 8 rather than made into an elementary new node.

## WANTED

None. The proof is agent-written from the stated assumptions, with the supporting Stacks sources present locally. The item source explicitly describes an agent-formulated consequence of 03BK; it is not itself a theorem stated verbatim in 03BK. No SGA source is used.

## Original node and blueprint audit

The original node was unsplit and had no proof or Lean audit attachment. Its statement is unchanged, including normality, Noetherianity, invariant finite surjectivity, geometric orbit fibres, the actual sheaf inclusion of invariants, the canonical residue-field map and the nonfaithful/disconnected clauses. No statement dispute was found. Equality of structure sheaves is interpreted through the canonical map q-sharp, as in the original statement and its source, not as the existence of an unrelated ring isomorphism.

The current chapter and unit records were read. This is an auxiliary node below the alteration branch used in the direct-image argument, not the statement node of the unit. I read main-20261015's det-thm-sf-ctf-stability-direct-images proof, paragraph (3), and retained the inherited route and via list. The blueprint ancestor command returns None for this auxiliary ancestry; I kept from.node=null and the detailed inherited place rather than inventing an ancestor. Whole-blueprint searches for generic fields, component orbits, finite quotient, normal components, invariants and fraction field found no node stating this whole item. Existing generic tools from other units are declared individually in split_report.tool_uses; no unit proof step is replaced.

The geometric-fibre orbit hypothesis is retained, although the affine invariant-sheaf hypothesis already gives the necessary point-orbit assertion through 03BL. There is no freeness assumption, and normality is applied to X and Z themselves, never to a possibly nonnormal quotient of a ring.

## Not duplicates

There are no new-node/existing-node pairs: no new node is proposed. The existing general normal-component, affine quotient-fibre, affine clopen, finite-closed-map and affine function-field nodes are reused directly. In particular no clone of 033M, 0357, 03BL, 00EE or 01RV was created. The elementary product evaluation and denominator calculations remain proof steps, avoiding D1/D2 restatements of the item's clauses.

## Review by NM

I checked the item source in literature/stacks-project/groupoids.tex, Tag 03BK, label lemma-invariants-base-change, especially the statement of (3) and its equalizer/flat-base-change proof. That theorem genuinely applies to constant finite action groupoids and does not require the order to be invertible. Rather than hide the component reduction inside the phrase generic localization, the delivered proof carries the reduction itself and computes the fixed field by a product of conjugate denominators. I also read 03BL, label lemma-points, for the point-orbit assertion; properties.tex 0357 and 033M for normal components; morphisms.tex 01WN for finite closedness and 01RV for generic stalks; schemes.tex 01IS, 01I3 and 01HV for generic points and affine principal opens; and algebra.tex 00EE for clopen idempotents. There are no new nodes requiring additional sources.

For Step 1, I opened lem-sc-affine-noetherian-underlying-space and lem-trf-normal-topologically-noetherian-components and checked their full statements. The former gives Noetherian topology on each of the finitely many affine charts in the hypothesis; stabilization on finitely many charts is the displayed elementary finite-cover argument. The latter assumes exactly normal local rings and Noetherian topology, and explicitly gives finite disjoint clopen integral components, including the empty scheme. It does not require extra excellence or an integral X.

For Step 2, I opened def-weil-finite-integral-morphism, lem-weil-pbc-finite-affine-coproduct-spectrum and lem-a1-affine-groupoid-orbit-fibres. Finiteness really includes affine inverse images; the coproduct theorem really identifies the finite union of copies with Spec of the product; the groupoid node really gives point-orbit fibres, not just geometric point orbits or existence of a quotient. The constant action groupoid has source the identity on each copy and target an automorphism on each copy, hence both are finite locally free; its structure identities are the actual group laws. The assumed sheaf equality gives its invariant ring on these affine charts. I did not use the relation-quotient theorem 03BM: its monomorphism/equivalence-relation hypothesis would exclude nonfree actions.

For Step 3, I opened lem-weil-pbc-finite-closed-map-finite-fibres. Its statement explicitly gives closedness for every closed subset, which is what this step needs; I use neither a generic-point theorem nor an unstated flatness theorem from it. The rest is written as a set argument: a component-orbit union is saturated, its image and the image of its complement are closed, and its image is the irreducible image of any one component. The normal component decomposition already established in Step 1 turns this nonempty irreducible clopen into a full target component. Saturation also gives disjointness of different images, and surjectivity gives coverage.

For Step 4, lem-sc-scheme-sober explicitly gives existence and uniqueness of generic points for components. The two closure inclusions are displayed; closedness is from Step 3. Taking closures and uniqueness prove that the point stabilizer equals the component stabilizer. Thus the group used subsequently is the exact D in the item, not the quotient by its ineffective kernel.

For Step 5, I opened lem-weil-pbc-spec-clopen-idempotent, lem-weil-pbc-affine-open-section-vanishing-prime and lem-sc-integral-function-field-affine-fraction. The first identifies the clopen with D(e), the second explicitly states scheme affineness of D(e), and the third states that the coordinate ring of a nonempty affine open of an integral scheme is a domain. I deliberately did not cite lem-weil-pbc-spec-localization-away-basic-open for affineness: its statement gives only a homeomorphism of underlying spaces, which would be C4 here. Every W_k is nonempty because the preceding component calculation gives q(X_k)=Z_j. The sheaf product map is restriction and its inverse is disjoint-open gluing; its action compatibility is inverse pullback, with h sending B_k to B_hk.

Step 6 is the explicit elementary argument: the tuple determined by a in B_i^D has entry h(a) at hi, independent of the representative since h inverse h-prime belongs to D. The same formula proves invariance, and projection is its inverse as a ring map. Nothing beyond the product construction of Step 5 and the sheaf hypothesis is used. This proves the actual image A=B_i^D, rather than assuming it or putting it into a new node that restates the item.

For Step 7, the affine function-field node explicitly supplies the fraction-field identifications and the germ maps. def-weil-residue-field says the field map comes from the local morphism; def-weil-open-immersion identifies stalks under restriction. The generic local rings are fields, so their maximal ideals vanish. I checked that the maps agree on sections and then on fractions by uniqueness of extending a map with invertible nonzero denominators. This identifies the map required in the statement, not just some field isomorphism.

Step 8 is the explicit elementary denominator calculation. For x=b/c fixed by D, the product d of all g(c) is nonzero in the domain and invariant by permutation of the factors. The numerator xd=b times the product over g not equal to 1 is an actual element of B_i; since x and d are fixed, it is invariant. Step 6 therefore puts both numerator and denominator in the image of A. This proves the reverse inclusion of fixed fields without invoking an additional lemma, without averaging, and without assuming the action is faithful. I read Mathlib's IsFractionRing.isInvariant and isInvariant_of_isIntegral as cross-checks; the whole item is not a one-line specialization of either.

I checked B--E against the actual files: the statement remains self-contained and unchanged, every non-elementary input is a cited node whose statement was opened, citations.json copies those statements literally, the elementary steps include their entire calculations, and no source tag stands in place of a DAG citation. All eight steps are shorter than 2000 characters. No cycle-producing dependency on the parent Sylow or alteration result is introduced.

Small cases checked: the empty scheme (all clauses vacuous); a trivial group (the sheaf inclusion gives identity on coordinate rings); two identical components exchanged (the invariants are the diagonal and the factor stabilizer is trivial); several disjoint component orbits (handled separately); a nontrivial group acting trivially on a component (the product repeats the denominator, which stays nonzero); and characteristic dividing the group order (no division by the order occurs). A disconnected trivial quotient has a separate target component for each source component, as Step 3 requires. None needs a generically free action or a connected source.

## Unfinished work

No mathematical part of this one-level split remains. The existing cited nodes retain their existing stage status; this delivery does not claim their pending Lean proofs are finished. The initial server review_split check passed. The required deliver.py dry run and push are the final delivery steps.
