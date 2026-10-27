# Stage-1 report: lem-sfb-epp-weak-solution-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-epp-weak-solution-descent.json: statement, split into seven proof steps; no full Mathlib match.
- citations.json: all twelve step/node citations, with verbatim excerpts verified against the current node statements.
- report.md and searches.jsonl: this review and the recorded searches.

There are no new nodes and no Mathlib leaves. The sandbox's write_split.py only prepares the item and citations; it is not a delivery file.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for weak solution, solutions-go-down and related expressions; no declaration states the item. Read the related DvrGaloisNormalizationRamificationDvd.lean: it concerns divisibility in a finite Galois normalization, not this statement.

## WANTED

None. All mathematical source passages used are present locally.

## Issues found and corrections

The imported item was statement-only, not a proof. Its source gives descent along an upper DVR tower but does not itself state the expanded successive-coefficient assertion of this node. The latter is proved here using explicit reduced tensor identifications and transitivity of integrality, so proof_origin is agent, with the exact Stacks sources recorded.

Part (ii)'s assumption that K_1 is a weak solution for A to B is redundant once the weak-solution assumptions for A_1 to every branch of C_1 are imposed. This is harmless: the proof establishes the stated implication without removing any hypothesis or changing the statement. A weak solution is never asserted to persist under an arbitrary coefficient extension. In particular the final single-parent clause does not make a claim about other parent branches.

The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports, despite the long historical creation chain. Retained this maintainer provenance and the existing precise historical from.place. Read the latest blueprint unit and its direct-images proof (3); this no longer contains an Epp assertion. Recorded the supporting historical scope in split_report.blueprint, without inventing a current blueprint match. Searches of the whole DAG and blueprint for weak solution, ramification, normalization and 09EM found no exact blueprint duplicate. Existing normalization results are reused.

## Not duplicates

No new nodes. In particular lem-sfb-dvr-algebraic-normalization-structure supplies finite-case local DVR structure and nonempty field factors; lem-per-complete-dvr-finite-normalization supplies complete finite coordinate normalizations and their uniqueness. Neither states weak-solution descent. The existing item lem-sfb-epp-normal-base-branch-conjugacy requires normal coefficient extensions and concerns automorphism orbits, and cannot replace our argument for arbitrary finite extensions.

## Mathlib search review

Retained the live item's existing searches. Ran the five new queries recorded in searches.jsonl with msearch.py: two semantic phrasings via LeanFinder, one LeanSearch query, a Loogle query for Ideal.ramificationIdx_tower, and a source grep for ramificationIdx_tower|weak.?solution|weakly.?unramified. All services answered. Read the returned hits. Mathlib's current ramificationIdx_tower (RingTheory/RamificationInertia/Ramification.lean:218) assumes a given ring tower and flatness; it does not construct normalized branches or cover them. Read TensorProduct.toIntegralClosure_bijective_of_tower (RingTheory/Smooth/IntegralClosure.lean:59): it assumes the two base-change bijections rather than proving arbitrary normalized reduced-base-change compatibility. The valuation-extension hits also lack the conclusion. None is an exact match or a one-line specialization for this item. No new node was needed for the uniformizer calculation: it follows directly from the existing uniformizer-power lemma and localness.

## Review by Q67

I read Stacks more-algebra.tex, Tag 09ES (lemma-solutions-go-down), including the normalized tower, spectrum-surjectivity argument and descent proof; Tag 09EM (remark-construction), especially the field factors, local DVRs and complete/Nagata cases; algebra.tex Tag 00GN (lemma-integral-transitive) and Tag 00PD (lemma-characterize-dvr). I checked the tag-to-label mapping in tags/tags. I read the chapter and unit records and the current latest blueprint text before using its historical provenance. No SGA source is used.

In step 1 I opened both cited nodes. The finite case of lem-sfb-dvr-algebraic-normalization-structure really gives nonempty field factors, maximal contractions and local DVRs, without a separability assumption. The complete-normalization node really gives finiteness, completeness and fraction fields for an arbitrary finite extension. The fields here are finite because the tensor algebra has the finite spanning set from K_i/K. I wrote the coordinate monic-polynomial product argument rather than assuming integral closure commutes with products. For a finite product of local rings, localization at the maximal ideal of one factor is that factor: the corresponding idempotent becomes 1 and all other idempotents become 0. No extra normalization lemma is hidden here.

In step 2 I checked the uniqueness clause of lem-per-complete-dvr-finite-normalization: B is complete, M/L is finite, and the given C is a DVR dominating B with fraction field M, exactly its hypotheses. Thus C is integral over B. The explicit linear retraction gives injectivity of the tensor map; reduction preserves this injection because nilpotence is reflected. I checked each of the four algebra citations: transitivity proves C_1 integral over B, lying-over produces a prime above each maximal ideal of B_1, the prime-over-maximal node makes that prime maximal, and the maximal-contraction node gives the converse contraction condition. These are statements of the nodes, not facts borrowed from their proofs. Integral elements over B_1 remain integral over C because B_1 elements already satisfy monic equations over B contained in C. All maps in the resulting local tower are injections.

In step 3 the only additional cited statement is the unit-times-uniformizer-power lemma. Injectivity keeps the image of a uniformizer nonzero, and localness keeps it a nonunit, giving positive exponents. Substituting the two factorizations and cancelling t proves that ef cannot exceed 1. This writes the full multiplicativity/descent calculation rather than appealing to an uncited ramification theorem. Completeness or a separable residue extension is not secretly used at this point. The branch-surjectivity of step 2 ensures that this checks every lower branch, not just a selected one.

In step 4 I checked that the tensor-product definition states the universal property used. Compatible maps into an arbitrary reduced ring kill nilpotents and give inverse maps by the explicit pure-tensor formula. Tensoring a reduced ring is not assumed to remain reduced, which is essential in inseparable characteristic. In step 5 the same definition checks the coordinate-idempotent maps, and the finite case of the normalization-structure node applies to A_1 into each complete branch DVR, with fraction fields K_1 into F_j and finite coefficient extension K_2/K_1. This proves nonemptiness and identifies the parent of every final field factor.

In step 6 I reread the integrality-transitivity statement. Each intermediate coordinate normalization is integral over the original upper DVR. Therefore integrality over it implies integrality over the original base; the converse uses the identical monic equation with its coefficients included. This gives equality of the actual normalization subrings inside each field H, and equality of the lower normalization with A_2. In step 7 the weak-solution hypothesis is applied to these identical rings, not to an unexplained isomorphism of localizations. Steps 4–6 respect all structural field maps by their displayed formulas, so the lower ideal is exactly the ideal in the conclusion. The same argument restricted to one coordinate proves the last clause without affecting the other branches.

I tested trivial extensions K_1=K and K_2=K_1, B=C, and A=B=C. The argument gives the expected identity branch and no false propagation of weak unramifiedness. For split tensor products the idempotents retain every parent; for a purely inseparable extension nilpotents are killed before comparing the fields. Finite products are nonempty here, since the field embeddings and finite nonzero coefficient extensions give nonzero tensor algebras; the zero-ring product issue therefore never deletes all branches. No new statement, new definition, or hidden field/perfectness hypothesis was introduced. No step exceeds 2000 characters; the elementary steps are explicit universal-property, monic-equation or uniformizer arguments from cited nodes and earlier steps. I checked delivery-errors B–E for statement completeness, actual citation strength, duplicate and Mathlib reuse, absence of cycles, and all hypotheses.

The complete-normalization node is an off-unit generic commutative-algebra tool, declared in split_report.tool_uses; it does not replace the unit's proof route. No unit file is changed because this item is not the unit key node.

## Unfinished work

No mathematical part of the requested split remains. The new dependencies are existing DAG nodes, whose future splitting or Lean proofs are outside this delivery's one-level scope. No Lean was written and no compiler, Lake or build tool was run.
