# Stage-1 delivery: lem-trf-normalized-polynomial-prime-lift

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normalized-polynomial-prime-lift.json`: existing statement, now split in six steps; not a Mathlib leaf. Statement and statement dependencies unchanged.
- `citations.json`: 19 exact statement quotations, one for every step/node citation.
- `searches.jsonl`: actual msearch.py results, retained unchanged as logged.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled, no repository writes or direct git commands.

## Attachments

None. I searched the item tag and the coordinate-lifting, prime-lifting and refined-normalization notions in `lean/WeilConjectures/`. The domain-normalization theorem in `NoetherNormalizationOverDomainSurjective.lean` does not give this item's full-polynomial map over an arbitrary base, its prescribed inverse-image prime, or its coefficient lifts. It is not an attachment. Existing declarations with sorry would not qualify.

## WANTED

None. The relevant Stacks source is present locally.

## Findings and corrections

The existing item is unsplit, with no proof or project Lean attachment, and no sandbox item, report or citations existed to resume. There was no delivery process from this attempt to repeat. The imported statement is correct and is retained. I expanded the coefficient lift and inverse-image ideal arguments that Stacks 0520 abbreviates. I corrected a draft localization tag from 00CM to 00E3 before delivery; the final source cites the actual lemma-spec-localization.

The split uses existing lem-trf-refined-noether-normalization-prime for Stacks 051P, rather than creating another normalization node. The finite transcendence-degree bound uses the existing Mathlib leaf lem-sfb-algebraic-adjoin-transcendence-bound. The remaining calculations are elementary and are written explicitly; none was turned into a redundant node.

## Mathlib and blueprint searches

I ran msearch.py with LeanFinder, Loogle, grep and LeanSearch for the item's coordinate lifting statement. A second semantic phrasing asked about the transcendence-degree bound for a polynomial residue field, and a second grep looked for the associated algebraic-independence facts. The results are preserved in searches.jsonl and appended exactly to the node's previous searches. Ordinary Noether normalization, at Mathlib/RingTheory/NoetherNormalization.lean:236, maps into a quotient and does not prescribe this full polynomial-ring inverse-image prime or lift the map over R_f. Polynomial residue-field maps from the search likewise do not state the item. I read Algebra.IsAlgebraic.trdeg_le_cardinalMk at Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:469: it is the existing bound leaf's general statement, so I cited that leaf.

DAG searches for 051P and lemma-refined-Noether-normalization found the existing normalization node. Searches for coordinate lifting and transcendence degree found the existing scalar-extension, fibre-prime, localization and algebraic-adjoin nodes. Blueprint searches for Noether normalization, refined, transcendence and polynomial found no exact equivalent of the item. `blueprint.same_as` is therefore empty. The ancestor command gives lem-trf-local-term-locality, as the retained blueprint.from already records. I read the current latest blueprint's locality statement and proof, the chapter and unit records, and the inherited 0520 affine-chart prerequisite. This is work below that prerequisite, not a replacement of the unit's contracting-correspondence argument.

## Not duplicates

No new nodes. The existing field normalization is reused. The common-denominator lifting is a polynomial construction in Step 3; the inverse-image ideal computation is Step 6, not an auxiliary restatement of the item.

## Review by O1

I read Stacks algebra.tex Tag 051P (lemma-refined-Noether-normalization) and the whole proof of Tag 0520 (lemma-refined-quasi-finite-over-polynomial-algebra). For the prime calculations I also read Tag 00E3 (lemma-spec-localization), Tag 00E6 (remark-fundamental-diagram) and Tag 0H9M (remark-local-ring-fibre). No new node needs a separate source review. No SGA source is used.

Step 1 uses the actual bijection in lem-weil-pbc-fibre-ring-primes-residue-fields, not merely a residue-field definition. Its hypotheses hold for R -> E and q' lying over p. Its kernel clause proves j^{-1}(Q)=q'. The polynomial scalar-extension node gives the specified fibre algebra. I checked the localization definition to identify kappa(Q) with Frac(k[t]/Q). For the bound, the cited algebraic-adjoin statement applies to the domain field kappa(Q), with s the images of the n variables: the generated subalgebra is B=k[t]/Q, and bT-a is a nonzero polynomial for each fraction a/b. Thus it gives precisely r <= |s| <= n, including finiteness; finite-cardinal comparison is elementary. The bound leaf is a generic Mathlib tool, not a route change.

Step 2 uses the exact statement of lem-trf-refined-noether-normalization-prime. The field k, polynomial prime Q and finite integer n meet its hypotheses, and it gives both the finite k-algebra map and its coordinate inverse-image ideal. I do not use any construction hidden in its proof. This node is in the item's own unit.

Step 3 uses only the cited definitions of localization at a prime, localization away from an element, and polynomial rings. Every residue coefficient has a representative a/b with b outside p. There are finitely many coefficients, so their denominator product f is outside p, and a/b has the explicit lift a(f/b)/f. I checked that no surjectivity of R -> k, no domain assumption on R, and no torsion-free assumption is used. The empty product covers zero polynomials and n=0. This is a finite coefficient calculation, not a missing lifting theorem.

Step 4 cites the polynomial universal property to construct psi, then proves finite type from the explicit n generators t_i over its source. This is exactly what the cited finite-type definition requires. The scalar-extension statement sends constants and variables to the stated constants and variables, so the two maps over k agree on generators. Finiteness of the scalar extension is inherited from the already cited normalization statement, not incorrectly asserted for psi over R_f.

Step 5 uses the localization-prime statement, whose prime-correspondence clause really does prove q'D is prime. I verified f is outside q' because its contraction to R is p. The identification D=E_f is written in fractions, and j(f) is a nonzero element of k. Testing G/f^m explicitly therefore identifies delta^{-1}(Q) with q'D using Step 1. Equality delta psi = varphi rho is checked on constants and variables. No residue-field map is silently assumed to be surjective, and no generic finite-type hypothesis is silently strengthened to finite presentation.

Step 6 expands the kernel of R_f -> k and the monomial coefficients, proving both containments of P=(pR_f,x_{r+1},...,x_n). This remains valid even though R_f -> k need not be onto. The localization-prime node's residue-field clause identifies kappa(pR_f) with k; its algebra compatibility is explicitly part of that node. The fibre-prime node's bijection, with C as the algebra over R_f and this contracted base prime, then identifies the unique fibre prime as I, because rho^{-1}(I)=P. Thus the statement's last clause uses a theorem actually stated by the citation. Every used node has a verbatim statement quote in citations.json; I read all those statements, including the definition nodes, before constructing the proof.

For delivery-errors B I checked self-contained unchanged statement, notion citations, TeX escaping, source tags and actual logged searches; there are no new nodes or invented Mathlib matches. For C I checked every cited statement as above, declared the two off-unit generic tools in split_report.tool_uses, and used no descendant of the item or proof-only construction. For D the six steps construct and calculate the requested objects instead of relocating the item into new clauses. For E I checked the hypotheses, fraction equalities, the difference between fibre-ring and residue-field maps, and zero and extreme coordinate cases. No step is longer than 2000 characters.

Edge cases: n=0 forces r=0, the normalization map is the identity on k, and f=1 works with P=p. For r=0, I is all variable generators and the coefficient criterion retains only the constant term. For r=n, I=0 and P=pC, since every monomial is retained. Finite base fields cause no difficulty because the existing refined normalization works over every field; the lift argument needs only fractions. Zero divisors in R are allowed by the localization equality relations and the primality tests. A zero ring R admits no prime q', so supplies no overlooked counterexample.

## Unfinished work

None for this one-level stage-1 split. The dependencies already in the DAG retain their own work status. No unit realization fields are changed because this auxiliary item is not the unit's key statement.
