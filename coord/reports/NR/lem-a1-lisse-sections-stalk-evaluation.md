## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-lisse-sections-stalk-evaluation.json: statement, split into eight steps; no Mathlib match. The statement and all original metadata and searches were retained.
- citations.json: verbatim statement quotations for every cited node in every step.
- searches.jsonl: actual msearch.py searches in this sandbox. No new nodes; no Mathlib leaves.

## Attachments

None for the whole item. I searched WeilConjectures for the exact blueprint tag and the notions, and read WeilConjectures/WeilSheaf/Stalk.lean:383-468 and StalkFrobeniusPow.lean:175-235. The former detects sections at finitely many arbitrary geometric points, and the latter intertwines powers at a point satisfying an explicit semilinear return. They do not themselves state the finite family of closed points on the model together with all the item's clauses. Their proofs contain no textual sorry, but I make no transitive-axiom attachment claim.

## WANTED

None. The needed literature is present.

## Findings and changes

The sandbox initially contained only brief markers, with no item, report, search log, or delivery output to reuse. No delivery had been started in this continuation. I copied the current item by constructing its sandbox JSON, preserving the mathematical statement, which already includes the maintainer's correction that repeated closed points with different lifts are allowed.

The imported proof was empty. The finite-type hypothesis, rather than locally finite type alone, is essential for finite detection: infinitely many disjoint points with the constant rank-one sheaf give an infinite product of sections. The proof uses connected geometric components, not connected components of the model. In particular Spec(F_{q^2}) has two geometric components but a single closed point on the model. No smoothness, geometric connectedness, nonemptiness, purity, or semisimplicity is used or added.

The Frobenius calculation uses ordinary sections throughout; I did not apply lem-a1-proper-sections-semilinear-germs, whose properness assumption is absent here. Nor did I use the finite-coefficient degree-zero lemma as if it already asserted a rational formula. The global mate calculation is on whole coefficient systems via lem-coef-semilinear-derived-sections, before localization, then uses the existing normalized lisse realization. It does not infer equality of system maps from their reductions and does not choose a Weil-stable integral lattice.

## Not duplicates

No new nodes. The whole-DAG searches included finite/noetherian connected components, closed-point residue fields, section evaluation, semilinear germs, point transport and Frobenius powers. tools/blueprint_refs.py was used for the item's ancestor and searches including global sections stalk, semilinear germs, sections pullback, evaluation Frobenius and Noetherian topology. The existing finite component node, closed-point existence node, residue-field criterion, and lisse fibre equivalence suffice. The proper-sections and finite-Weil-sections nodes have stronger base hypotheses and are not used. The topological locally-constant zero-locus lemma concerns sheaves on Zariski open sets and does not apply to lisse adic sheaves; it is not used either.

## Review by NR

I read the chapter and unit records, the current main-20261015 parent lemma and its proof, and the parent node's review. The unit's use of a closed-point degree-power comparison is exactly what steps 5-8 realize; steps 1-4 supply finite stalk detection needed by the parent's generalized finite-type formulation. The chapter and unit route are unchanged.

For sources I read Deligne, Weil II, (0.1), (1.1.1), (1.1.6)-(1.1.14), printed pp. 144-153: the Noetherian separated convention, lisse coefficient categories, the faithful fibre equivalence, geometric rather than arithmetic Frobenius, Weil structure as an invertible pullback map, and the degree-normalized local operator. I also read Bhatt-Scholze, Lemma 6.8.2, Definition 6.8.3, Proposition 6.8.4 and Proposition 6.8.14/Remark 6.8.15, printed pp. 58-62. These support the existing lisse realization tool's comparison of module-sheaf and rationalized models; the tool's stronger normalization clauses are explicitly agent formulations, not attributed verbatim to the paper. For the geometric selection I read Stacks morphisms.tex labels lemma-base-change-finite-type and lemma-finite-type-noetherian (01T4, 01T6), properties.tex lemma-Noetherian-topology (01OZ), and topology.tex lemma-Noetherian, lemma-locally-connected, lemma-locally-Noetherian-locally-connected and lemma-quasi-compact-closed-point (0052, 04ME, 04MF, 005E). There are no new statements to compare with sources.

I opened every cited node and read its statement. Step 1 uses exactly separated/finite-type base change from lem-pod-separated-finite-type-base-change, Noetherianity from lem-weil-pbc-finite-type-over-noetherian, its topological consequence from lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, and finite/open components from lem-sfb-noetherian-connected-components-open. I corrected the first draft to cite the existing scheme/topology lemma instead of leaving the Noetherian topology assertion implicit. The remaining restrictions to an open-and-closed component follow directly on affine charts and from the diagonal definition.

Step 2 uses lem-sc-quasi-compact-kolmogorov-closed-point only after checking the component is nonempty, quasi-compact and Kolmogorov. Lem-kun-closed-point-field(a) is applied first over k to obtain a k-rational point and then over k_0 to its image, using the residue-field injection into the algebraic extension k/k_0. This avoids any unsupported claim that an arbitrary scheme morphism carries closed points to closed points.

Step 3 uses the faithful fibre functor in cor-galois-lisse-representations(2), with connectedness, Noetherianity, separatedness and invertibility of ell all verified on C_i. The unit-to-sheaf morphism defined by a section has zero fibre exactly when its value is zero; faithfulness makes that morphism zero. Gluing on the component open cover is elementary. Step 4 takes finite-dimensionality of the fibres from the same statement and writes the elementary linear independence argument giving the bound on sections. I have not cited only a definition of a fibre functor for its faithfulness.

Step 5 expands the specified global operator using def-weil-global-geometric-frobenius, def-weil-frobenius-cohomology-transport and the actual direct-image mate in def-weil-frobenius-square-exchange(1). The statement of lem-coef-semilinear-derived-sections supplies the needed units, counits, composition and ordinary mate-pasting identities as identities on systems, not merely finite evaluations. Lem-tw-lisse-rational-realization supplies the composition/unit/pullback and point-transport normalizations after rationalization and common-stage extension. The unit-counit cancellation is the elementary adjunction calculation, and applies to the ordinary structure morphism without properness. Step 6 writes the base and induction calculation for T^r explicitly; the recurrence and composition comparisons are those of def-weil-local-frobenius-trace and the normalized lisse realization. The finitely many maps in an equation are represented at a common coefficient field, with no assumption that theta preserves an integral lattice.

Step 7 uses the actual invertibility statement in lem-weil-frobenius-cohomology-transport-iso(3) at Qlbar, then functoriality of cohomology on the Weil isomorphism to obtain invertibility of T. Step 8 uses the exact local composite and return equation in def-weil-local-frobenius-trace, the restriction/insertion definition of def-weil-frobenius-point-transport, its naturality theorem lem-weil-frobenius-point-transport-natural(2), and the point/pullback normalization in lem-tw-lisse-rational-realization. It evaluates the section morphism on 1; naturality gives the displayed equality, and composition with z^*theta^[d] gives exactly F_y. This is a direct substitution in the cited constructions, not a new local-power comparison theorem or an invocation of the proof of another node. I checked the types: b goes from (h^d)^*z^*G to z^*(g^d)^*G, so the final map lands in the original stalk. The return is g^d z = z h^d, never g^d z = z.

Small cases: the empty scheme gives A=0 and the empty family; rank zero is harmless; on Spec(F_q), T and F_y are the same arbitrary invertible scalar or matrix, including non-unit ell-adic eigenvalues; on Spec(F_{q^2}), a rank-one sheaf needs two different lifts of the same closed point, and T permutes their coordinates with T^2 the local return; disconnected schemes use one lift per geometric component. Nilpotents require no reducedness assumption anywhere. All step lengths are below 2000 characters. The longer calculations use existing generic mate/realization statements and contain the explicit application, rather than hiding an uncited comparison lemma.

The C1/C4 audit was performed against the opened statements; citations.json quotes them verbatim. I checked B1-B10 (no new unsplit records, no new duplicate, no Mathlib leaf claimed), C1-C8 (all non-elementary tools cited and off-unit generic uses declared), D1-D5 (the item carries the proof, no clause moved to a new node or circular dependency), and E1-E7 (hypotheses, directions and edge cases above). No SGA source is used. No Lean file was written, no compiler or build tool was run, and all writes are in the assigned sandbox.

## Unfinished work

None in the mathematical split; server checks and delivery are recorded by the delivery command.
