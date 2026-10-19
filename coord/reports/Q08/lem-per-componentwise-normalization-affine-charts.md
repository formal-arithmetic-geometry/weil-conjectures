# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-componentwise-normalization-affine-charts.json`: statement item, split into seven steps. No exact Mathlib match for the whole statement; the finite affine coproduct part reuses an existing Mathlib leaf.
- `citations.json`: one verbatim statement quote for each citation in each proof step.
- `searches.jsonl`: search-command log. The original item's four search records were retained and their exact queries rerun through msearch for this delivery; five additional queries test a second phrasing and the relative-normalization candidates.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. I searched WeilConjectures in the read-only slopmaster2 source by the exact item id, componentwise normalization, and affine normalization phrases. The source file WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean treats integral-source relative normalization and function-field normalization; it does not state the finite-minimal-prime componentwise formula of this item. In particular its finiteness results require hypotheses irrelevant to the present formula and cannot be attached here.

The proof reuses the existing closed node `lem-weil-pbc-reduced-induced-closed-subscheme`; its recorded attachment is `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`. No attachment field was edited.

## WANTED

None. All source material used is present locally.

## Problems and changes

The item had no proof. Its statement is correct, and I kept it unchanged, including the empty-open case. I did not cite 035P as a black box restating the item or introduce a node for one of the item's clauses. Instead I wrote the componentwise argument underlying 0CDV. The integral affine-chart construction already appears explicitly in `def-fin-normalization-extension`, for L=K; no duplicate integral normalization chart node is needed.

The statement's use of 'a mod p_i' denotes its image under A -> A/p_i -> B_i. Step 6 spells out the inclusion into B_i and checks the structural map by its projections. No change to the statement was required.

The blueprint ancestor is `lem-per-artin-gabber-affine-curve`, through the existing normalization/dualizing chain recorded on the item. I read the chapter and perverse unit records and the current main-20261015 chapter/unit sources. This is a generic normalization calculation supporting that chain, not a change in the Fourier/perverse proof route. The item is not a unit key node; no unit record is edited. The existing precise blueprint.from.place is retained. Whole-blueprint searches for normalization, integral closure and components open found the existing integral normalization definition but no second blueprint statement equivalent to this item, so same_as remains empty.

## Unfinished work

None in the one-level split. Existing dependencies keep their own status; they are neither silently proved nor edited here. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. Searches across all dag/nodes for 035P, 0CDV, minimal primes, component restriction and normalization charts located the nodes cited in the proof. In particular the finite product spectrum fact is already `lem-weil-pbc-finite-affine-coproduct-spectrum`, not a new node.

## Review by Q08

I read Morphisms Tag 035P, label lemma-description-normalization, all four parts and its proof; Tag 0CDV, label lemma-normalization-in-terms-of-components, with its proof; and the affine sheaf integral-closure construction of Tag 035F and definition 035H. For the integral normalization chart interface I also read the current blueprint `def-fin-normalization-extension` and its DAG statement, whose explicit affine clause applies to arbitrary integral schemes and whose L=K specialization is named. The source's normalization-localization lemma 035K explains the restriction being used. No new source nodes need statement checks.

Step 1 cites `pqf-lem-affine-open-locnoeth` for exactly A being Noetherian, `lem-sc-finite-minimal-primes-over-ideal` with I=(0) for finiteness, and `lem-weil-pbc-spec-irreducible-components-minimal-primes` for the V(p_i) component list. I opened all three statements: none requires A to be finite type over a field. Local Noetherianity is sufficient, and no excellence hypothesis is added.

Step 2 uses only the stated injective open-restriction map in `lem-sc-components-open-injection`; I did not pretend that this node states surjectivity. Surjectivity is written out: an irreducible component C of U remains irreducible in X, is contained in an X-component by `lem-sc-irreducible-components-cover`, and maximality gives equality after restriction. I opened the covering node, which covers arbitrary irreducible subsets, not just points. Thus a component of X meeting U cannot occur twice, and components disjoint from U disappear.

Step 3 uses the explicit radical-ideal and affine-quotient clauses of `lem-weil-pbc-reduced-induced-closed-subscheme`. For V(p_i) the radical ideal is p_i. The definition `def-weil-pbc-reduced-normalization` supplies the integral reduced structure on each global component. The full statement of `lem-sc-integral-function-field-affine-fraction` applies to arbitrary integral schemes, with a nonempty affine open; both hypotheses hold for Z_i and Spec(A/p_i). It gives the field identification over A/p_i, not just an abstract field isomorphism. This matters for the canonical structural map.

Step 4 applies the existing definition `def-fin-normalization-extension` to L=K, a degree-one finite field extension. Its statement gives the affine integral-closure chart and expressly identifies L=K with `def-sc-normalization`; I used neither a proof hidden in that node nor a finiteness theorem. The chart is taken on Z_i, not on X assumed integral. This avoids confusing reducible absolute normalization with Mathlib's arbitrary relative normalization.

Step 5 unfolds `def-weil-pbc-reduced-normalization` and uses the actual disjoint-open-cover clause of `lem-weil-pbc-scheme-coproduct-family`. Restricting that disjoint open cover and its structure sheaves gives the coproduct of the restricted schemes. The inverse image on a component disjoint from U is empty. This is marked elementary because it is just restriction of a disjoint union after Steps 2-4 have identified all summands. The two maps composing on each summand are specified, so their ring map is A -> A/p_i -> B_i.

Step 6 reads `lem-weil-pbc-finite-affine-coproduct-spectrum`, which states both the finite-family isomorphism and that coprojections are Spec of coordinate projections. Its finiteness hypothesis comes from Step 1. Together with the full-faithful affine Spec correspondence in `def-weil-affine-spectrum`, it identifies the structural map coordinate by coordinate. I checked that the direction of the Spec maps is contravariant and that these are isomorphisms of U-schemes.

Step 7 handles the empty index set directly using the sheaf axiom on the empty open, the absence of proper primes in the zero ring, and the coproduct universal property. This is elementary. I also tested the domain case t=1 (the usual integral closure chart), the normal domain case (B=A), a disconnected reduced affine scheme (product factors remain separate), and the nodal reduced ring k[x,y]/(xy) (two quotient-domain branches, normalization k[x] x k[y]). These tests distinguish irreducible from connected components and do not assume finiteness of normalization. Non-quasi-compact X is allowed: only its chosen affine U and the components meeting it enter the finite list.

For C1/C4 I copied the entire relevant statements verbatim into citations.json, including the hypotheses, and reread each against the exact use above. Off-unit generic tools are declared in split_report.tool_uses where required. For B/D there are no new nodes, no new duplicate definitions, no clause of the item moved into a fresh lemma, and no unsupported new statement to test. The longest step is below 800 characters, so no step exceeds the 2000-character review threshold. The proof_deps are exactly the union of the step uses. I retained the original statement, created metadata and blueprint fields; the only additions concern the split and the actually run searches.
