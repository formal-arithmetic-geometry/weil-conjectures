# lem-sfb-dilating-weight-nakayama — stage 1, NB, 2026-10-24

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dilating-weight-nakayama.json`: existing statement, now split by six elementary proof steps; not a Mathlib match.
- `citations.json`: `[]`, because every proof step expands definitions and the hypotheses directly, and no proof step cites a node.
- `report.md`: this report. The search command also wrote `searches.jsonl`; all its records were read and retained verbatim in the item's search results.

New nodes: 0. New Mathlib leaves: 0. No Lean file, unit, chapter, repository file or launcher file was written.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` by the exact item id, dilating weight, graded Nakayama, weight divisibility, semilinear and Frobenius/weight terms. Read the closest `RingTheory/GradedNakayamaGeneration.lean:29-76` and the description/declarations of `LinearAlgebra/SemilinearFrobenius.lean`. The former requires a finite module over k[x_0,x_1] with additive degree shifts; the latter concerns Frobenius fixed points and scalar extension. Neither states this item, which allows arbitrary dimension, arbitrary unital coefficient endomorphism and multiplicative lattice-weight dilation. There is no exact project declaration to attach.

## WANTED

None for this item. This is expressly an agent-formulated refinement, and the existing source does not claim a literature theorem for it. No missing textbook result is used in the proof, and no Stacks tag is asserted.

## What was wrong or changed

The item was unsplit and had no proof. Its statement is true as written, and it is unchanged. The source's suggested p-divisibility-height induction can be implemented more directly with the natural-number size d(nu) = sum |nu_a|. This is the same descending-weight argument: if nu = p mu is nonzero, d(mu) < d(nu). The change avoids an unnecessary auxiliary node for existence of a finite divisibility height.

Read Milne, *Algebraic Groups* iAG2017, printed p.296 (PDF page 308), Proposition 14.50 and the adjoining skew-polynomial discussion. It states left-ideal principality and ungraded freeness of submodules of finite free skew modules. It does not state the present weight-dilating result; the source already says so, and `proof_origin.by` is `agent`. The proof above is independent of that freeness theorem, not an attribution of an invented assertion to Milne.

Read the latest blueprint unit `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially clause (3), and the current chapter/unit records. Read the parent's statement and all five proof steps: it invokes exactly this statement on the nonzero-weight summand in its step 3. This split stays in that supporting algebraic route. The inherited blueprint ancestor is null (`blueprint_refs.py ancestor` prints `None`); retained that existing field and its full supporting-input place rather than inventing an imported ancestor. Whole-blueprint searches for Nakayama, semilinear and homogeneous found no equivalent blueprint statement.

## Mathlib search assessment

All fresh Mathlib searches ran through the required `msearch.py NB lem-sfb-dilating-weight-nakayama` command. Ran LeanFinder with two distinct conceptual phrasings, LeanSearch with the precise quotient-span formulation, Loogle, and grep in LinearAlgebra and RingTheory/GradedAlgebra. The two initial Loogle queries contained unknown identifiers; their records explicitly say query rejected and are not absence evidence. The corrected quoted-name query `"span", "iterate"` ran successfully and found only the Chebyshev derivative span theorem, which is unrelated.

Read the hit signatures printed by the services. LeanFinder's first list concerns profinite Nobeling spans, root-system spans and lattices; its second list concerns homogeneous submodules and finite-type graded algebras. LeanSearch's plausible hits are `LinearMap.map_span` and `Set.MapsTo.submoduleSpan`; read `Mathlib/LinearAlgebra/Span/Basic.lean:64-99`. The former requires surjectivity of the coefficient map, unavailable here; the latter establishes stability of spans and gives no generation conclusion. Step 1 instead writes the finite-sum calculation explicitly. Read `RingTheory/GradedAlgebra/FiniteType.lean:20-51` and `Homogeneous/Submodule.lean:50-96`: their algebra-generation or homogeneity assertions do not give the item's semilinear generation theorem. They are not matches. All actual queries, including rejected patterns and the extra candidate-reading greps, were appended to `mathlib_searches` with the exact query text and original logged result. Existing inherited search records were preserved.

## Not duplicates

There are no new-node/existing-node pairs to justify. For completeness, the two closest existing nodes were opened and their statements compared:

- Item vs `lem-sfb-graded-nakayama-connected`: that node requires finite generation over a commutative nonnegatively graded connected algebra and additive degree shifts; this item is an arbitrary-dimensional vector space with a semilinear operator multiplying lattice weights by p. Neither identifies with the other in one line.
- Item vs `lem-sc-p1-graded-nakayama-generation`: that node specializes the finite-module commutative polynomial-ring setting to k[x_0,x_1]. It does not imply this arbitrary semilinear weight-dilation statement.
- `lem-sfb-torus-equivariant-frobenius-module-basis` is the parent, requiring finite free skew-module structure and concluding a homogeneous free basis. The present item is its weaker generation prerequisite, not a duplicate.

No arithmetic-size lemma, stability-of-span lemma or component-projection lemma was created: each calculation takes two or three lines from definitions and appears in the item's own proof. This follows the explicit elementary-node exclusion in the brief.

## Review by NB

I read the item against its parent's actual use, Milne p.296, and the latest blueprint route. There are no new nodes requiring separate sources. I checked delivery-errors B through E in both copies of those sections. The statement introduces the field, endomorphism, grading, subspaces, operator, quotient, generators and iterates explicitly; the field's definition node was opened and remains the only statement dependency. All other notions used here are defined inline. The proof does not depend on a mere definition node for a theorem.

Step 1 uses no cited statement: an element of the defined span has a finite linear expansion, and applying the stated additivity/semilinearity gives the displayed formula. This proves T-stability without assuming sigma is onto and without identifying image with image-span. Step 2 also uses no cited statement: adding or scaling finite decompositions and invoking their given uniqueness proves linearity of each component projection. Applying T to the finite decomposition gives the component formula; p >= 2 implies multiplication by p is injective on the integer lattice, so at most one predecessor contributes. T(0) = 0 follows from additivity, including missing components.

Step 3 uses no cited statement: spanning the explicitly defined quotient means that x minus a finite generator combination is in J; membership in J means a finite k-linear combination of T(v_i). Projecting the resulting equality and using step 2 gives each displayed formula. The homogeneity assumption on every b_j is used exactly here. It is not assumed that an arbitrary element of J is a single T-image or that its scalar coefficients are sigma-images.

Step 4 uses no cited statement: finite coordinate arithmetic gives d(p mu) = p d(mu), and a nonzero integer lattice vector has a positive sum of absolute coordinates. This supplies the explicit strictly decreasing induction parameter, including negative coordinates and composite p. Step 5 uses no cited statement: it states its strong-induction claim for every weight of a fixed natural-number size, proves size zero using the assumed V_0 = 0, and treats the two projected-expression cases. The only predecessor has smaller size, so the induction is not circular. Step 1 and closure of a span under finite linear combinations then finish the inductive step. Step 6 uses no cited statement: the given finite homogeneous decomposition assembles membership in W. All six steps are elementary direct calculations/ordinary natural-number induction, with no hidden structure theorem or generic graded Nakayama assertion. The longest step is 581 characters; none crosses the 2000-character review threshold. `proof_deps` and the union of step uses are both empty, so the empty `citations.json` is intentional, not missing quotations.

I checked the hypotheses and small cases explicitly. For s = 0 only the zero weight exists, hence V = V_0 = 0. For m = 0 the induction proves V = 0 from V/J = 0. For T = 0, J = 0 and the conclusion is the assumed span of the b_j; the proof handles this without injectivity. For negative weights, d(-p) = p and d(-1) = 1, so the induction has the same strict decrease. For a nonperfect coefficient example, k = F_2(t), sigma(a) = a^2, p = 2, V = direct sum over n >= 0 of k e_n with weight(e_n) = 2^n and T(a e_n) = a^2 e_(n+1): J is the entire span of e_n for n >= 1 even though T(V) need not be that span. The single coset of e_0 generates V/J, and its iterates give every e_n. This infinite-dimensional example checks both the absence of finite-dimensionality and the nonsurjectivity issue.

The restrictions are necessary in elementary boundary examples: if V_0 != 0, V = k in weight zero with T = identity and the empty family has V/J = 0 but fails to generate V. If p = 1 were allowed, the same example in weight 1 would fail with V_0 = 0. Both are excluded by the actual item; no statement dispute is needed. No hypothesis, coefficient category, functor, finite-generation assumption, or injectivity assumption was silently changed. There are no proof-citation C4 obligations because the proof cites no nodes; the existing statement dependency defines precisely the only externally referenced notion. No SGA source, new dependency cycle, off-unit proof tool or chapter/unit change is involved.

## Unfinished work

None in the mathematical split. Delivery validation is performed by the required server dry run and push after this report is written.
