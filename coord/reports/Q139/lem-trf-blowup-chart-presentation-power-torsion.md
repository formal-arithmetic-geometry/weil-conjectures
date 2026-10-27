## Files written

- dag/nodes/sec-trace-formula/lem-trf-blowup-chart-presentation-power-torsion.json — statement, split; no Mathlib match. The statement is unchanged, four elementary proof steps have been supplied, and localization and quotient definitions have been added to statement dependencies.
- citations.json — twelve verbatim statement excerpts, one for each cited node in each proof step.
- searches.jsonl — actual searches recorded by the required search command; their queries and results are reflected in the item.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The exact blueprint-tag search and the concept searches under lean/WeilConjectures found no declaration stating this quotient presentation and its power-torsion kernel. Blowup/Affine/ChartAlgebra.lean identifies a homogeneous Rees localization with the chart; StrictTransformChart.lean proves a kernel theorem for a tensor-product base-change chart. Neither has the polynomial quotient as its source, so neither is an attachment of this item.

## WANTED

None.

## What needed repair

The seeded item had a correct statement and source but no proof. I retained its statement, source, original searches, provenance and blueprint reference, and supplied the direct finite-support argument advertised in its source field. Its notation uses a ring quotient and a principal localization; I added the existing definition nodes for those notions. No statement dispute was found.

The Stacks proof of Tag 0G8S has a harmless notation typo: its final sentence says P → A although the map introduced there is P → R. This delivery does not use that base-change argument. Its proof_origin is agent because the explicit direct calculation is supplied here rather than copied from the Stacks proof.

## Unfinished

None for the requested one-level split. No Lean was written, compiled or built, and no shared repository or launcher file was edited.

## Not duplicates

No new nodes were created. DAG searches for Tag 0G8S and lemma-affine-blowup-quotient-description found the item and its regular-sequence parent. The parent assumes a regular sequence and proves an isomorphism; it uses this arbitrary-ring torsion-kernel calculation and cannot be cited back without circularity. Existing power-torsion/localization nodes were read, but their assertions are unnecessary because the fraction equivalence in def-weil-ring-localization-away gives the precise zero criterion directly. Blueprint searches for quotient-description and a-power torsion found no blueprint statement of this general presentation. The broader blowup search located the chart definition and the base-change chart results, whose source objects differ.

## Review by Q139

I read coord/delivery-errors.md sections B–E in both copies, the stage-1 brief and stage document, the three levels in SETUP.md, GOAL.md, the chapter and unit records, and the current blueprint locality statement and proof under literature/blueprint/latest. The calculation belongs below the fixed unit route: it supplies the coordinate-chart input recorded in the existing ancestry, without changing the contracting-correspondence proof. I checked that no repair note reopens some different plan and that the sandbox initially contained no node or report to preserve.

For the item's source I read algebra.tex at lemma-affine-blowup-quotient-description and its preceding polynomial example, verified Tag 0G8S against tags/tags, and read the construction and fraction equivalence at definition-localization, Tag 00CO. I did not invoke the preceding example's omitted torsion-freeness proof, nor the Stacks base-change theorem. There are no new nodes needing sources. The alternative direct proof is explicitly labelled agent-written.

Step 1 uses the statement of def-weil-pbc-mv-polynomial-ring for evaluation and its algebra-homomorphism universal property; def-nagata-blowup-chart-ring for the subalgebra containing the generator fractions; def-weil-ring-localization-away for fraction arithmetic; and def-weil-pbc-algebra-hom-quotient for the quotient map and its kernel J. I opened each node and checked its statement. Well-definedness is proved directly: any element of J is a finite sum of polynomial multiples of the displayed relations, each of which evaluates to zero. There is no appeal to an uncited quotient comparison theorem.

Step 2 uses precisely the chart's generated-subalgebra definition and fraction arithmetic. The ideal-membership expression x=r_1 a+sum r_i a_i shows every generating fraction lies in the image, while Step 1 already places the image inside B. Thus no unproved theorem about generators is used, and the coefficients r_i are in the given arbitrary ring R.

Step 3 uses the polynomial node's finite monomial expression, quotient arithmetic from the quotient node, and fraction arithmetic from the localization node. I checked the exact identity a^|alpha| [y^alpha]=product (a[y_i])^alpha_i=product a_i^alpha_i and the finite sum defining b. The integer d bounds the total degrees of all monomials actually present, so every exponent d-|alpha| is nonnegative. This establishes an equality already in Q, not just after localization. It uses no cancellation or injectivity of R → Q. The identical calculation in R_a identifies b/1 with a^d phi(z); no hidden denominator-clearing lemma is being quoted.

Step 4 uses the localization statement's literal equivalence of fractions: b/1=0 gives a^k b=0 in R. Multiplying the equality from Step 3 then kills z by a^(d+k). In the converse direction only the invertibility of a in R_a and the inclusion of B as a subalgebra of R_a are used. I did not assume a is invertible in B or nonzero in R. The quotient node justifies passing the equality a^k b=0 to Q. All twelve cited step/node pairs have excerpts checked to be literal substrings of the node statements in citations.json.

I tested the degeneracies explicitly. If s=1, Q=R and the assertion becomes the ordinary localization zero criterion, with d=0 for constant polynomials. If a=0 or a is nilpotent, R_a and B are zero, and every element of Q is killed by a common power of a; the proof still applies, including the zero ring. If a is a unit, J eliminates each variable and phi is an isomorphism, as the formula requires. With R=Z/4Z, a=2, a_2=0, the target is zero and a^2 kills Q; with R=Z, a=2, a_2=0, Q=Z[y]/(2y) has a genuine nonzero torsion kernel and y maps to zero. These check that no regularity hypothesis was silently introduced and that the kernel need not vanish.

Against B–E: no statement-only node is being passed off as a proof, no new duplicate or clause-node exists, every non-elementary imported theorem has been avoided in favor of displayed elementary algebra, and every cited statement supplies exactly the notion used. The four steps are each shorter than 500 characters, and the whole proof is shorter than 3000 characters. The finite-support calculation is routine arithmetic in the item's own rings rather than a hidden comparison theorem with separate hypotheses. I read the actual Mathlib search results and the relevant sources: ReesAlgebra.lean:39–96, Extension/Generators.lean:116–119 and its generator constructions, Extension/Presentation/Basic.lean:206–219, Polynomial/UniversalFactorizationRing.lean:191–197, and Algebra/Polynomial/DenomsClearable.lean:36–79. They provide either different presentations or a univariate denominator identity, not an exact match or one-line specialization of the item. Both semantic phrasings are logged, all recorded searches actually ran, and the prior 2026-10-22 records are retained. No SGA source is used.
