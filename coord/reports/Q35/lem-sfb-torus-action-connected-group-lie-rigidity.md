# Stage-1 delivery: lem-sfb-torus-action-connected-group-lie-rigidity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-action-connected-group-lie-rigidity.json`: item split, statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-subgroup-identity-stalk-detection.json`: one new statement-only node, unsplit; no Mathlib match. It has no proof, proof dependencies, or proof sketch in its statement.
- `citations.json`: one verbatim statement extract for each step/node citation.
- `report.md`: this report. `prepare.py` is sandbox-only preparation, and `searches.jsonl` is the search tool's unedited log.

## Attachments

None. Searched the project source `lean/WeilConjectures/` by the item id, torus, rigidity, connected/Lie and subgroup-neighbourhood/stalk notions. The matrix-group Lie comparison declarations require characteristic zero and reduced matrix groups or smooth subgroups; the sheaf rigidity declarations concern other objects. No project declaration states the entire item with a finished proof. No Lean file was written or compiled.

## Wanted literature

WANTED: local copy of B. Conrad, *Reductive Group Schemes*, Proposition 3.3.8, printed p.102, for the item. The primary PDF https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf was read online at the proof paragraph invoking CGP Corollary A.8.11; the local literature catalogue has no copy.

WANTED: local copy of Conrad--Gabber--Prasad, *Pseudo-reductive Groups*, Corollary A.8.11, for the item. I do not claim to have read CGP. The delivered proof is marked agent-origin and uses the locally available Milne finite-jet argument instead of treating Conrad's citation as a proof. No SGA source is used.

## Audit findings and route

No statement dispute. Conrad explicitly invokes tangent detection for a connected finite-type group which can be nonreduced. The statement carefully means triviality of the full torus representation, not zero differential. Those two assertions are different in positive characteristic, and neither is silently substituted for the other.

The imported node had an empty proof. Its existing Mathlib searches, source, creation metadata and blueprint ancestry were retained; searches from this session were appended. The source of the proof is explicitly agent-origin. The new lemma is the general local-to-global subgroup criterion, independent of torus actions, tangent spaces and weights. The substantive tangent-to-all-jets argument remains in the item's own proof. The smooth fixed-point theorem and the smooth connected variety finite-jet detection theorem are deliberately not cited because their smoothness hypotheses are unavailable here.

Read the chapter record, the recorded unit, and the current `literature/blueprint/latest/` unit and direct-images proof (3). The supporting node serves the already present reductive-group/alteration prerequisite. Its inherited nearest blueprint ancestor is null, exactly as `tools/blueprint_refs.py ancestor` reports; the new node retains this ancestry, with the item prepended to `via`. No chapter or unit route or realization was changed.

## Intended proof of the new statement-only node

This is an agent-formulated consequence of the homogeneity argument in Milne 1.8, printed p.9; it is not claimed to be a numbered theorem in that source. I read that argument, Milne's discussion of scheme points and nilpotents in 1.4--1.10, and Stacks Tags 0478 (`varieties-lemma-locally-finite-type-Jacobson`) and 00FV (`algebra-theorem-nullstellensatz`) in the local source. Here is the complete proposed proof for the later worker.

Write G = Spec A and K = Spec(A/I). The finite-type algebra A is Noetherian, so I has finitely many generators. The identity-stalk isomorphism says I localized at the identity maximal ideal is zero. Choose a single f outside that maximal ideal annihilating all the generators. Then U = D(f) is an open neighbourhood of the identity that factors scheme-theoretically through K. Let V be the union of the open subschemes xU as x runs over K(k). Translation by x is a scheme automorphism, with inverse translation by x inverse (Milne 1.8). Each xU factors through K because K is a subgroup, and V contains every rational point of K, since the identity belongs to U. The closed subset |K| minus V is empty: if nonempty it would have a closed point, whose residue field is k by 0478/00FV and algebraic closedness. Thus |K| = V is open in |G|, and it is also closed. It contains the identity, so connectedness makes it all of |G|. Finally the xU cover G and the defining ideal vanishes on each, hence I = 0 as a sheaf, and K = G as schemes. This last open-cover argument retains nilpotents; equality of rational point sets alone is not used to conclude scheme equality.

## Not duplicates

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-field-groupoid-open-image-closed: the latter starts with an already open topological image and only proves it closed; it does not infer a scheme isomorphism from a single local-ring isomorphism.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-finite-type-group-identity-subgroup: the latter constructs the identity component as an open and closed subgroup; it does not identify an arbitrary closed subgroup from its identity stalk.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-group-neutral-component-translates: the latter describes connected components and translations, without the closed-subgroup local-ring criterion.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-lft-field-group-neutral-component: geometric irreducibility and base change of the canonical neutral component do not state the arbitrary-subgroup criterion.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-smooth-subgroup-full-tangent: that result requires the subgroup to be smooth and only assumes a surjective tangent map. The new criterion assumes an isomorphism of local rings and allows nonreduced subgroups in any characteristic.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-ag-equal-dimension-subgroup: that blueprint node is for reduced matrix groups over an algebraically closed characteristic-zero field and uses equality of dimension, whereas our statement allows arbitrary characteristic and nonreduced schemes and assumes identity-stalk equality.

lem-sfb-closed-subgroup-identity-stalk-detection vs lem-sfb-torus-action-connected-group-lie-rigidity: the new lemma has no torus, action, tangent representation, or tangent-detection assertion. The item proves the local-ring hypothesis using weights, finite jets and Krull intersection, then uses the general subgroup lemma.

## Mathlib and duplicate searches

Ran the prescribed `msearch.py` command with Q35 and this item. For the new identity-stalk node, ran LeanFinder twice (local-ring and identity-neighbourhood formulations), LeanSearch, Loogle with `"GrpObj", "IsClosedImmersion"`, and two source grep patterns. Read the returned signatures and inspected `Mathlib/AlgebraicGeometry/OpenImmersion.lean:490-493`, `Topology/Algebra/OpenSubgroup.lean:268-275` and the `AlgebraicGeometry/Group/Abelian.lean` grep hits. The open-immersion theorem needs every stalk and an open embedding; ordinary topological subgroup theorems do not handle the scheme structure or nilpotents, and the Zariski group is not in general a topological group for the product topology. None is a one-line specialization of the new assertion.

For the item, ran LeanFinder, LeanSearch, Loogle and grep. The returned abstract Lie-module theorem means vanishing brackets; the definition at `Algebra/Lie/Abelian.lean:39-45` confirms it is not the full torus representation. The other hits concern Galois categories and ordinary representation actions. The earlier item searches also contain a second natural-language formulation. All session records use exactly the query text in the tool-created `searches.jsonl`; no unavailable service is recorded as absence.

Before creating the new node, searched the entire DAG and blueprint with `tools/blueprint_refs.py search` for `open subgroup`, `subgroup identity`, `closed subgroup`, `torus action`, `torus tangent`, `fixed jets`, and `tangent cotangent`, and source/DAG grep for the same notions. Read the candidate statements listed above. The item and new lemma have `same_as: []` because no blueprint statement says either in equivalent form. The new source names no Stacks tag as the statement of the full criterion; Stacks 0478/00FV above are inputs to its future split.

## Review by Q35

I checked delivery-errors B--E against both JSON files, the cited statements, and the sources. For the item I read Conrad's primary proof paragraph online, Milne Theorem 7.1 (printed pp.138--139), Proposition 8.9's jet construction (p.150), Theorem 12.12 and Remark 12.13 (pp.234--235), and Lemmas 13.4/13.6 (pp.255--256). For the new node I read Milne 1.8 and the local Stacks 0478/00FV statements and supplied the full intended subgroup argument above. The node is statement-only, rather than a disguised proof or a second copy of the target. No new source theorem is attributed a false tag or number.

Step 1 uses the universal fixed-subscheme node for representability and its universal fixed meaning; the subgroup definition applies because fixed elements are closed under product and inverse over every algebra extension. The rational-point thickenings statement supplies Noetherianity and residue k. The torus local-ideal/jet statement gives the actual local quotient R/J and finite rational jet representations. I read each of these statements: neither the local-ideal node nor the rational-point thickenings node assumes smoothness. Affineness gives separatedness via the coordinate diagonal. The identity is a rational fixed point because each action automorphism preserves the group identity.

Step 2 uses exactly the naturality clause of rational tangent/cotangent duality, applied to each actual k-automorphism fixing the rational identity. Finite-dimensionality needed to recover a map from its dual was established in step 1. This is ordinary dual-vector-space separation, not an unproved comparison of Lie algebras.

Step 3 uses the full coaction form of the multiplicative-group weight-basis node. Restricting a torus to each factor and comparing the Laurent coefficients gives simultaneous weights and weight-preservation of equivariant maps. The local-jet node supplies the equivariant surjection needed to take the weight-zero component of a preimage. I wrote out the finite degree-raising generation argument, so no Nakayama or regular-parameter assertion is used without a node. In particular the u_i need not be a regular system of parameters. Only the images w_i in the finite jet need be invariant; no claim that the whole local ring is a rational representation is made. Each proof step has fewer than 2000 characters.

Step 4 uses the exact Krull-intersection statement for a Noetherian ring, an ideal in its Jacobson radical and a finite module. Here R is Noetherian local, the ideal is its maximal ideal, and R is cyclic as a module. Thus all three hypotheses hold. All t-differences vanish in every jet, so the concrete ideal J is zero, including its nilpotent elements.

Step 5 applies the new subgroup criterion with K = F and G = H, checking every one of its hypotheses from the item and steps 1/4. The fixed-subscheme node's restricted-action equality then yields equality of morphisms, hence equality on all algebra-valued points. Step 6 uses the tangent-space definition, whose tangent map is composition on dual-number points; differentiating an actual identity after each base change is the identity. No theorem about differential injectivity is presumed.

I tested the original item on r = 0, H = 1, a nonreduced infinitesimal group such as alpha_p or mu_p, and the positive-characteristic action t.x = t^p x on G_a. In the last example the differential of the representation is zero but its full character is nontrivial, so it is correctly excluded by the hypothesis. When the cotangent space is zero, degree-raising makes every jet just k and the same proof works. For the new node, the identity inclusion and nonreduced connected groups satisfy the criterion; a proper infinitesimal subgroup with identical underlying points still fails the stalk-isomorphism hypothesis. Dropping connectedness would allow the identity component of a disconnected finite group, which explains why connectedness is retained. The finite-generation and rational-closed-point hypotheses in the proposed proof hold because the groups are finite type over an algebraically closed field.

The only off-unit statement tools are rational tangent/cotangent duality and Krull intersection, declared in split_report.tool_uses with their role. No external unit route is substituted. I corrected no statement and introduced no Lean or compiler changes.

## Unfinished work

No gap is left in the item's assembly argument. The new general identity-stalk criterion is intentionally unsplit for the next stage-1 item, as required by one-level splitting; its full intended proof is above. Zero Mathlib leaves were found. Delivery validation and push results are recorded below after the required tool completes.

## Validation

The first dry run exited with a citation-length diagnostic for the short Krull-intersection conclusion. Replaced that excerpt by the whole verbatim statement. The second dry run exited successfully: `OK (not pushed)` at ae7f5562058, with server preflight passed. No concurrent deliver invocation was launched.

The local reading of Milne Proposition 8.9 also confirms why its final assertion about a closed subscheme of an irreducible scheme is not imported here: without reducedness that assertion does not follow merely from containing an open neighbourhood. The item uses only its jet construction and Krull argument, then the separately stated subgroup criterion whose proof retains the nilpotent structure by translations and an open cover.
