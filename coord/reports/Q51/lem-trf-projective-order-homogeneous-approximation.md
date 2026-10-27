# Worker report: Q51

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-projective-order-homogeneous-approximation.json`: item, split in six steps; statement unchanged, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-order-triangular-coordinates.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-order-completed-normal-form.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-order-filtered-syzygy-lifting.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: exact statement excerpts for all six proof-step citations (including the two citations of triangular coordinates).

## Attachments

None. Searches in the live `lean/WeilConjectures/` for the item's blueprint tag, homogeneous approximation, projective order, Hironaka, coefficient fields, syzygies and the new ids found no declaration giving these assertions. No Lean files or compiler/build tools were used.

## Literature wanted

WANTED: Heisuke Hironaka, *Certain numerical characters of singularities*, J. Math. Kyoto Univ. 10-1 (1970), 151–187, archival local copy, for the item and all three new nodes. Read online at https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf . The source's original Lemma 18 and its proof on printed pp.174–175 were read, together with (13.2) on p.168, Lemma 14 and (14.1)–(14.2) on p.169, Lemma 15 on pp.170–171, Remarks (16.1)–(16.2) on pp.171–172, and Lemma 17 on pp.172–173. The ILO PDF recorded by the parent nodes is only the historical VIII 2.3.13 motivation. No Stacks tag states these specialized coordinate and relation assertions. The source metadata explicitly distinguishes this from a claim that ILO proves them. As the actual paper is absent from the local literature directory, the item's expanded proof is marked agent-written, following the source read online. Nothing was downloaded or written into the repository.

## Corrections and scope

No statement dispute. The original statement is exactly the homogeneous approximation and the two consequences in Hironaka's Lemma 18 (with order at least t expressed as membership in N^t). Its own input forms need not minimally generate an ideal; the new filtered-syzygy statement makes no such assumption. The item formerly had no proof. It now exposes the source's structural inputs instead of hiding them behind the words 'descending induction' or 'by Lemma 17'.

The chapter and unit files, GOAL.md, SETUP.md's three levels, the stage-1 brief and delivery-errors B–E were read. The newest blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.{md,proof.md}`. Its current proof follows contracting correspondences; this item belongs to the historical resolution branch already recorded by its ancestors. This delivery only splits that assigned algebra input and makes no route replacement or change to chapter/unit records. It is not the unit key node.

## Searches and reuse

The sandbox initially contained only dispatcher marker files, with no node, report, citations or searches. The live item was copied once. The whole DAG was searched for Hironaka, Lemma 17, (13.2), (14.2), (16.2), triangular additive coordinates, weighted normal forms and approximate syzygies; the blueprint searches included `triangular`, `triangular additive`, `homogeneous approximation`, `weighted monomial`, `syzygy`, `homogeneous order` and `coefficient field`. Broad matches concern other coefficients or unrelated geometry. The ancestor command confirms `lem-trf-local-term-locality`.

All Mathlib searches were run with the required msearch.py command and their literal tool/query records are preserved in searches.jsonl and in the appropriate node's mathlib_searches. Each new node has LeanSearch, LeanFinder, Loogle and source grep, with a second phrasing. Services answered. The item has fresh searches as well as its preserved older search records. Returned signatures and relevant sources were read: homogeneous polynomials, MvPowerSeries.Order, WeierstrassPreparation, Submersive presentations, and MonomialOrder/Groebner. `MonomialOrder.sPolynomial_decomposition` (MonomialOrder.lean:1249) decomposes cancellation of polynomial leading terms; it does not give exact relations in a completed local ring with the stated filtration bounds. `MonomialOrder.div_set` (Groebner.lean:232) gives ordinary monomial-order division and is not the item's local approximation theorem. WeightedOrder results describe a given power series; they do not establish the special normal-coordinate expansion or identify local N-order with its weights. Abstract projective lifting is unrelated. None is an exact or one-line match for a new node.

## Not duplicates

lem-trf-projective-order-triangular-coordinates vs lem-trf-projective-order-algebra-additive-generators: the existing node says only that the order algebra is generated by its additive elements, in the homogeneous-prime formulation. The new statement gives finitely many triangular pure-power generators, their degrees, algebraic independence and the bounded-exponent free polynomial normal expansion; none of this is a clause of the existing statement.

lem-trf-projective-order-completed-normal-form vs lem-trf-projective-order-initial-minimality: the existing node concerns initial forms of minimal generating lists; the new node gives coefficient fields, shifted parameters, completed monomial expansions, the full weighted order formula, and the coefficient comparison even when k is not contained in the coefficient field. Minimality alone does not state these facts.

lem-trf-projective-order-completed-normal-form vs lem-trf-adic-evaluation-homogeneous-preimages: the latter gives a surjective power-series evaluation under quotient-surjectivity assumptions for arbitrary complete rings. It provides neither these local coordinates nor uniqueness of normal expansions nor the weighted order formula.

lem-trf-projective-order-filtered-syzygy-lifting vs lem-trf-projective-order-initial-minimality: lifting arbitrary approximate coefficient relations to exact ones includes redundant generating families and is not minimality of initial generators.

lem-trf-projective-order-filtered-syzygy-lifting vs lem-trf-normal-flat-chart-relation-removal: the latter is an intersection of ideals in a parameter blowup chart under finite-jet and normal-flatness hypotheses. The new node concerns the completed affine polynomial local ring and one filtration level of coefficient relations, without a blowup or those hypotheses.

## Review by Q51

I checked the proof against the source and delivery-errors B–E with the statements open. Each new node introduces its field, polynomial ring, prime, localization, order, forms and all additional data; completion and formal power series cite their actual definition nodes. The three new nodes have statements only, no proof or hidden proof sketch. They are structural and relation inputs rather than restatements of the approximation conclusion: none constructs the requested C_j. Their blueprint fields record the exact ancestral place and searched same_as lists. No Lean attachment is claimed from a sorry-containing declaration.

Step 1 uses the new triangular-coordinate statement: its U=k[sigma] clause puts every phi_j into the weighted polynomial subring, and its unique homogeneous expansion supplies precisely the basis and degree bounds used. The generators fix X_0 and only permute the other variables, so the affine chart is preserved. Step 2 uses the same statement's algebraic independence and homogeneous expansion. I wrote the finite elimination: each leading exponent is reduced by a weighted homogeneous element of the ideal, with coefficients extracted in degree q.A. The resulting coefficients have degree (d-q.A-|beta|)+|beta|+(q.A-e_j)=d-e_j. The finite bound q.A+|beta|<=d proves termination; no polynomial division black box is hidden.

Step 3 uses both the completed-normal-form and filtered-syzygy statements. The first explicitly preserves orders of elements of L; the second applies to an arbitrary, possibly redundant list, with q=m and sum of order s>m. Its exact relation permits replacement without altering the sum, and its congruence raises the minimum coefficient-plus-generator degree. The iteration is finite, ending at s; an empty sum cannot have finite s. Coefficients stay in the completion, as allowed by the two statements, so no unsupported descent of completed coefficients is invoked.

Step 4 uses the full normal-form statement: f_A,beta dehomogenizes to an element of L_0, t=z+a only decreases beta, and expanding those coefficients in F[[omega]] does not change A. The weighted-order formula detects a nonzero degree-s part. The epsilon_0 coefficient comparison in that same statement gives an error of order e_j+1; multiplying by coefficients of order at least max(0,s-e_j) gives order at least s+1. This explicitly handles the coefficient-field subtlety stated in Remark (16.1). I verified that all needed assertions are in the node's statement, rather than relying on a definition of completion to imply them.

Step 5 is an explicit finite linear-algebra argument: a basis of the span of finitely many coefficients proves preservation of leading exponents under k-to-F extension. For a fixed nonzero (beta,gamma) block of weight s, its polynomial in rho belongs to the extended generator ideal; hence its leading A lies in E, contradicting the zero coefficients established in Step 4. This supplies the source's final contradiction in full, without introducing a new node that merely rephrases the item. Step 6 reads the existing initial-minimality statement literally and applies only its singleton case: nonzero psi-star has degree d>=1, lies in U_d, and is not in the zero ideal of the empty list. That statement gives exact order d, contradicting t>d. I did not take the stronger unproved claim that every degree-d polynomial has order at most d from a definition.

The edge cases checked were b=0 (hypothesis itself is the approximation, and t>d forces psi=0), r=0 (prime zero, N=0, no nonzero positive-degree inputs in U), e=0 (U=k, so the positive-degree input list is empty), psi=0, redundant/repeated generators, e_j=d (constant correction coefficients), q_i=1 in characteristic zero, and a purely inseparable point in characteristic p. For k=F_p(a), p=(t^p-a), the order algebra has no positive generator in that variable and the completion's coefficient field cannot be assumed to contain k. The new normal-form statement intentionally avoids that false assumption. For a rational point all q_i=1 and the bounded beta list is just zero, recovering ordinary Taylor degree reduction.

Every cited statement has a verbatim excerpt in citations.json. The new inputs and reused singleton minimality say what the steps require (C4), and all non-elementary inputs are cited (C1). The remaining polynomial subtraction and finite basis comparison are written out as elementary steps. Every non-elementary step is under 2000 characters; no long step conceals a separate lemma. The report records the reasoning and source checks, not just mechanical validation.

## Unfinished work

No portion of the assigned split remains unwritten. The three new nodes are intentionally unsplit for later stage-1 work. There are zero new Mathlib leaves. The required server dry run and delivery results follow below.

## Dry-run repair

The first full dry run rejected the two triangular-coordinate citation excerpts for being shorter than 40 characters. I replaced both with the full relevant conclusion, including the coordinate formulas and the unique homogeneous expansion. The mathematical citation is unchanged.
