# Stage-1 report: lem-sfb-scheme-m-pseudocoherent-summands

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-m-pseudocoherent-summands.json`: statement, split; fixed-m summand proof from Stacks 08CE. Mathlib searches found no exact match.
- `citations.json`: one verbatim statement quotation for each of the 20 citations in the seven proof steps.
- `searches.jsonl`: searches actually run by the required msearch command. Earlier searches in the repository node were retained as historical source records, and the new logged searches were appended to the node.
- `report.md`: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searching WeilConjectures by the item tag and by m-pseudo-coherence and summands found no declaration stating this assertion on arbitrary scheme module sheaves. `AlgebraicGeometry.Scheme.pseudoCoherent_of_isIso_biproduct` in AlgebraicGeometry/PseudoCoherentSummand.lean:132 assumes full pseudo-coherence, and its definition uses local bounded-above finite-free models. The fixed-m ring theorem `DerivedCategory.mPseudoCoherent_summand` in Algebra/Homology/RingPseudoCoherentSummand.lean:88 is about ordinary ring modules. Neither states this item. No compiler or Lean-writing tool was used.

## WANTED

None. All sources used are present.

## Audit findings and corrections

The item statement is correct as written and is unchanged. Its empty proof needed a local upper bound, the explicit cone of the idempotent projection, a shift calculation, a base case, and downward induction at the same m. The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor. I retained that metadata and its complete via chain, and explained the precise supporting place in split_report.blueprint. The latest blueprint unit and chapter were read, as were GOAL.md and the three-level rule. There is no change of the direct-image route. The unit record is not edited.

The full pseudo-coherent scheme summand node and its Lean declaration do not discharge a fixed-m statement. The existing `lem-sfb-ringed-site-m-pseudocoherent-triangle` DOES give all three shifted triangle assertions without quasi-coherence, so it is reused in place of creating a duplicate scheme-only 08CD node. Its application to the site of opens is explained in step 1 by restricting coverings to intersections. The existing finite-sum-triangle and split-triangle Mathlib leaves cover the two purely triangulated inputs.

## Not duplicates

No new nodes. Existing `lem-pc-pseudo-coherent-summand` concerns full pseudo-coherence, whereas this item assumes only one fixed approximation degree. Existing `lem-sfb-ringed-site-m-pseudocoherent-triangle` is the general triangle tool needed here and is cited directly. The whole DAG was searched for 08CE, 08CD, 08CC and the key notions; the imported blueprint was searched with blueprint_refs.py for pseudo-coherent, cone-pseudo-coherent, summands and 08CE. No exact blueprint statement was found.

## Review by Q26

I read Cohomology of Sheaves, cohomology.tex, Tag 08CE (lemma-summands-pseudo-coherent), its proof, Tag 08CB (definition-pseudo-coherent), Tag 08CC (independence of representative), and Tag 08CD (lemma-cone-pseudo-coherent). I also read sites-cohomology.tex Tag 08FT and the independent-representative lemma, and Tag 08FV, statement and proof, to check the general ringed-site triangle input. Finally I read derived.tex Tag 05QS (lemma-direct-sum-triangles). No new node needs another source. The proof follows 08CE rather than an affine quasi-coherent or ring-module reduction.

Step 1 uses the definition of m-pseudo-coherence for the local approximation, the perfect-complex definition for the finite upper support bound, exact slice restriction for the functor, exact-functor-derived-factorization for its termwise triangulated extension, and exact-functor-complex-cohomology for persistence of cohomology isomorphisms and epimorphisms. I opened each cited statement. The ringed-site triangle statement explicitly has the same strict-perfect approximation notion. On the site of opens, taking intersections of a covering with an arbitrary open proves the agreement of its local definition with the scheme definition; no comparison theorem or quasi-coherence assumption is hidden. H^i of a summand is a retract of H^i(E) just by applying a functor to the inclusion/projection identity, so the vanishing claim does not require a separate cohomology-biproduct theorem. The upper bound is local, not uniform across the scheme.

Step 2 uses the two definitions and the derived-category shift formula only. I checked the direction: T[r] is a-pseudo-coherent iff T is (a+r)-pseudo-coherent. Raising the threshold weakens the condition, with a surjection at the old threshold and an isomorphism at every larger one. The same witnesses prove this directly, so no shift or monotonicity node was created.

Step 3 uses the cone formula from the abstract derived-category statement and the identity triangle from the triangulated-category definition. On a representative, the cone of zero has exactly diagonal differential (d,-d), so it represents B plus B[1] with the correct sign. The finite-sum-triangle node states the componentwise biproduct assertion and its additive-shift identification for any finite set, including the two-element set used here. Thus the map on the first two vertices really is id_A plus zero_B, and its cone really is B plus B[1].

Step 4 uses clause (1) of the ringed-site triangle node. Its first-term hypothesis is (m+1)-pseudo-coherence, obtained from m-pseudo-coherence in step 2, and its middle-term hypothesis is exactly the given m-pseudo-coherence. Shifting C by a nonnegative t is justified by first raising its threshold to m+t and then shifting. This proves the same fixed-m assertion for all C[t] used later; it does not invoke the item recursively.

Step 5 is the zero-approximation base case from definitions. Choosing n at least 1 with m+n>N makes every H^i(B[n]) vanish for i at least m, so the zero map is also surjective in degree m. Strictness of the inequality matters: vanishing only above m would not give that surjection. There is no assumption of a globally bounded representative.

Step 6 cites the split-triangle leaf, whose statement is exactly X to X plus Z to Z to X[1], and clause (1) of the ringed-site triangle theorem. Substituting X=B[j], Z=B[j-1] gives the displayed triangle. Its middle object is the exchange of C[j-1]; j is at least 1, so the nonnegative shift assertion of step 4 applies. The first object is (m+1)-pseudo-coherent by monotonicity. The induction starts at j=n and stops at j=1, so its conclusion is B[0].

Step 7 uses only the local approximation definition to assemble the local coverings. Exchanging the two summands repeats the actual proof for A, under the same hypotheses already verified. Taking the union of local witness coverings proves the global conclusion without choosing a single upper cohomological cutoff.

I checked B--E of delivery-errors.md against these files: no new statement-only or duplicate-node issue; every proof citation has its statement open and a literal quotation; no cited proof is substituted for a statement; no ring-only or quasi-coherent result is applied to arbitrary sheaves. All non-elementary inputs have node citations. The elementary calculations are written out, not moved to auxiliary nodes. No step exceeds 2000 characters. I checked dependencies do not return to the item. The off-unit exact-restriction node is declared in split_report.tool_uses as generic infrastructure; no maintainer-owned tool_uses field is set.

Small cases checked: the empty scheme uses the empty cover; zero summands use zero approximations; a complex concentrated in degree d with m>d is already approximated by zero; when m=d, the proof still requires the stated surjection at m; negative m and arbitrary integer shifts satisfy the same i+n formula. Disjoint unions with increasingly high cohomological cutoffs are handled by separately choosing N and n on each approximation open. None of these checks introduces Noetherianity, quasi-coherence, quasi-compactness or a global upper bound.

## Unfinished work

None for the stage-1 split. Existing supporting nodes remain the DAG dependencies; no claim is made to have proved their Lean statements.
