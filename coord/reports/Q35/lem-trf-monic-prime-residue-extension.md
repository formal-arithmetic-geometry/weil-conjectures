## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-monic-prime-residue-extension.json`: statement, split; five proof steps, all using existing Mathlib leaves. The statement and its four statement dependencies are unchanged.
- `citations.json`: nine verbatim statement excerpts covering every proof-step citation.
- `searches.jsonl`: authentic output records from the prescribed search command, retained with all results read.
- `report.md`: this report and direct-delivery self-review.

New nodes: 0. New Mathlib leaves: 0. The proof reuses eight existing nodes (nine step citations).

Attachments: none. Searching `lean/WeilConjectures/` by the exact blueprint tag and by monic/prime/residue notions found no declaration giving this entire statement. `exists_monogenic_residue_polynomial_model` concerns a normal Nagata domain and constructing a relation after localization, rather than the residue field and the given-degree spanning set here; it is not an attachment.

WANTED: none.

The imported node had a precise and correct statement but no proof. Tag 051P asserts finiteness and unchanged transcendence degree in its polynomial-chart induction, while omitting the monogenic residue argument. The split supplies that argument over the item's arbitrary commutative coefficient algebra. No hypothesis was added or dropped. In particular, the proof never assumes that B is a domain, Noetherian or of finite type. There is no statement dispute.

Unfinished work: none for the one-level split. Existing Mathlib leaves supply every non-elementary ingredient.

## Sources and blueprint

Read `literature/stacks-project/algebra.tex`, Tag 051P, label `lemma-refined-Noether-normalization`, especially the sentence beginning “Note that kappa(p) ... is finite” and its equal-transcendence-degree conclusion. Read the local-rings paragraph identifying kappa(p) with Frac(R/p), and the following induced-residue-map paragraph. Read Tag 04GG, `lemma-characterize-henselian`, proof of 10=>1, where R[T]/(f) is finite free; Tag 00GK, `lemma-finite-is-integral`; and `literature/stacks-project/fields.tex`, Tag 09GG, `lemma-finite-is-algebraic`, and Tag 030H, `lemma-transcendence-degree-tower`. These sources justify the route, while Q35's explicit assembly is marked agent-written because 051P does not state the arbitrary-B power-spanning refinement itself.

Read the chapter and unit records `sec-trace-formula` and `sk-i-curve-zero`, and the latest blueprint's `lem-trf-local-term-locality.proof.md`. The item's nearest blueprint ancestor remains `lem-trf-local-term-locality` and the inherited via chain is retained. This is the already-recorded affine polynomial-chart ingredient in the refined-normalization branch, not a change to the chapter or unit argument. Whole-blueprint searches for monic, monic polynomial, power basis, residue field and finite-dimensional domain found no blueprint node stating the item. In particular the residue-field search returned etale/strict-henselian and geometric-stalk statements, not this monic polynomial assertion. The node's `same_as` is empty and its precise existing `from.place` is retained.

## Mathlib searches

Read all hits from the six searches performed with msearch.py. The first natural-language search and its second phrasing were both run. Loogle `Polynomial.Monic, Submodule.span` finds `Submodule.span_range_natDegree_eq_adjoin`; the second LeanFinder phrasing confirms it. Its statement in `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:86` gives the power span of a generated subalgebra, but does not identify that subalgebra with a residue field. The existing monic quotient leaf provides exactly the same ingredient without creating another node.

The first LeanFinder result `Polynomial.residueFieldMapCAlgEquiv` was read in `Mathlib/RingTheory/LocalRing/ResidueField/Polynomial.lean:35`: it assumes the polynomial prime is the extension of the coefficient prime and identifies its residue field with a rational function field. That hypothesis is not the monic-relation case here. The residue integrality and quasi-finiteness hits also do not include the specified monogenic presentation and power span. LeanSearch found `AdjoinRoot.powerBasis'`, which is already represented by `lem-weil-pbc-monic-quotient-free`; it supplies an ingredient, not the complete item. The final logged grep of the residue polynomial file was read as printed (the single-file grep's file/line labels are imperfect); the actual source was separately opened above. Every new `mathlib_searches` entry is taken from its real log, with the exact query and tool. Existing search evidence from the live node is preserved.

## Not duplicates

No new nodes were created. DAG searches by title, statement, monic/power-span wording and the candidate Mathlib names found the reusable fraction-lift, prime-residue-field, monic-quotient, finite-dimensional-domain, finite-algebra-integrality and transcendence-degree-tower leaves. A more specialized new adjoin-span node would be unnecessary. The existing simple algebraic extension power-basis node uses the extension degree, whereas this item needs the possibly larger degree of the given monic polynomial; the proof therefore uses the existing monic quotient basis.

## Review by Q35

I opened the statement of every cited node, rather than relying on its title or proof. I checked the item against the exact 051P residue-extension sentence and the additional explicit power-span assertion against the monic quotient theorem. There are no new-node sources to review. I checked delivery-errors B through E as follows.

Step 1 uses `lem-weil-pbc-prime-residue-field-algebra` specifically for its clause (b): residue fields are fraction fields of the prime quotients, and the quotient injections are injective. It uses `lem-weil-pbc-fraction-field-lift` for the extension, its formula and injectivity. The argument explicitly checks primality of the contraction and the kernel of A -> D, so the lift's domain hypothesis is satisfied by B/p, not assumed of B. The equality on coefficients gives the k-linearity that the abstract ring-hom lift alone does not mention. The fraction formula is written rather than hidden in “transport”.

Step 2 uses `def-weil-pbc-mv-polynomial-ring` for evaluation and finite polynomial expressions, `lem-weil-pbc-monic-quotient-free` for the precise basis of F[T]/(g), and `def-weil-finitely-generated-module` for finite generation over a field meaning finite dimensionality. I checked that the monic quotient leaf states the powers up to the polynomial's own degree, not merely an unspecified basis or an extension-degree basis. The mapped leading coefficient stays one in the nonzero field F, so no degree can drop. The evaluation quotient map and its surjectivity are written explicitly: multiples of g vanish, and S consists of polynomial evaluations. Taking the images of a finite basis directly gives a spanning family; no exactness, flatness or tensor-product lemma is being assumed.

Step 3 applies `lem-weil-pbc-finite-dimensional-domain-is-field` only after verifying that S is a nonzero commutative domain inside E and is finite dimensional by step 2. Its statement gives the needed inverses. The second citation, `lem-weil-pbc-prime-residue-field-algebra`, says that E is a fraction field of D, so every element is a fraction of classes of polynomials. Both numerator and denominator lie in S by their polynomial formulas. The denominator remains nonzero by the quoted injection; its inverse in S is its field inverse in E by multiplying the equality vv'=1. This proves E=S directly. No assertion that the quotient F[T]/(g) is a field is made: g may be reducible.

Step 4 uses `lem-weil-pbc-finite-algebra-is-integral`, whose actual statement says every element of a module-finite commutative algebra satisfies a monic polynomial. Steps 2 and 3 verify its module-finiteness hypothesis. Over F, a monic polynomial is nonzero, giving exactly the item's definition of algebraicity. This avoids citing a definition of algebraicity as though it proved finite extensions algebraic.

Step 5 uses `lem-kun-transcendence-degree-tower`, whose statement includes both the cardinal tower formula and the equivalence of algebraicity with relative transcendence degree zero. The competing `lem-sbc-transcendence-degree-tower` contains only the formula; I chose the former to avoid an uncited zero-degree criterion. Step 1 verifies the compatible k -> F -> E maps. Cardinal addition, rather than subtraction or finite numerical dimensions, gives the result even for infinite transcendence degree.

For B1-B10, no statement-only child is needed; the item remains self-contained, its TeX and statement are unchanged, and its blueprint and genuine search evidence are retained. No proof is hidden inside a new statement, no Mathlib result is duplicated, and no clause of the item is moved to a child. C1-C4 are addressed by the preceding step-by-step statement readings and the nine verified verbatim excerpts in citations.json. C5-C8 cause no problem: all reused results are Mathlib leaves, none depends on the item, and no off-route unresolved tool is introduced. D1-D5 are addressed by the actual quotient/evaluation/fraction argument. No step exceeds 2000 characters (lengths 631, 671, 659, 288, 370), and none hides a separate comparison theorem.

For E1-E7, I checked the relevant small cases. With d=1 the quotient has basis {1}, so E=F, including arbitrary coefficients. A reducible f in a prime q gives a spanning set, not falsely an independent family. With B=k[epsilon]/(epsilon^2) and q=(epsilon,T), the proof passes to B/p=k and still works; it does not use cancellation in B. For B=k and an irreducible inseparable monic polynomial, the extension is algebraic without a separability claim. The zero ring B has no prime q, so there is no unhandled field-of-fractions construction. If f=1 the hypotheses cannot hold because q is proper, consistently with d>0. Taking B to be a polynomial algebra on an infinite set and q=(T) checks that the argument never requires finite transcendence degree. No source error or statement correction was necessary. During review I replaced the tentative plan to introduce an adjoin-span helper with the already-existing monic quotient leaf, and replaced a tower-formula-only citation with the existing node that also states the algebraicity criterion.

## Validation

The prescribed server dry run exited successfully: `OK (not pushed)` at `05d7af32d41`, with server preflight passed (including check_dag and review_split). No repair was requested. After recording this result, the final report version is validated once more before the direct push. No Lean file was written and no compiler, Lake or build tool was run.
