## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-laurent-vector-evaluation-test.json` (statement, now split; not a Mathlib leaf), `citations.json`, and this report. `searches.jsonl` records the six searches actually run by Q34. No new nodes or new Mathlib leaves.

Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint tag, `funext_set`, and Laurent/subspace terminology found no declaration proving this item. The project hits concern unrelated Laurent descriptions of projective-space sections.

WANTED: none.

The statement is correct as written. I retained its hypotheses, source and existing provenance/search records. The prior node had no proof. Milne's Proposition 1.11 and Remark 1.14 (printed p.10, PDF p.22) discuss scalar/base-algebra coefficients; I have marked the vector-space and quotient argument as agent-written rather than attributing the whole formulation to Milne. I corrected no statement and introduced no hypothesis. Nothing remains unfinished in the split.

## Sources and reuse

I read the chapter and unit records, the current blueprint's corresponding chapter/unit text, and the current `sk-thm-sf-ctf-stability-direct-images.proof.md`. Its paragraph (3) gives the proper/open compactification assembly. This item is a descendant algebraic prerequisite in the recorded alteration/torus-fixed-ideal refinement, rather than a replacement for that unit route. The inherited ancestor tool reports `blueprint.from.node = None`; I preserved the established `from` record and its detailed place and via chain.

Whole-blueprint searches for `Laurent` and `dual separates` found no equivalent statement: `def-sc-gm-ga` defines the multiplicative group and its coordinate ring, and `prop-duality-reciprocity` concerns Frobenius duality. DAG searches found and reused `lem-sfb-mvpolynomial-infinite-evaluation` and `lem-weil-pbc-vector-space-dual-separates`. Their statements were opened in full. Both are existing Mathlib leaves, so their use is a generic tool and creates no unit-route departure.

I read Mathlib `Algebra/MvPolynomial/Funext.lean:57–86` and `LinearAlgebra/Dual/Lemmas.lean:196–209`. Two differently phrased semantic searches, Loogle, LeanSearch and source grep returned scalar polynomial extensionality, scalar evaluation, coefficients-in-submodule definitions, and dual separation. These do not directly state the arbitrary-vector Laurent assertion. The exact queries and returned summaries are copied from the new search log into `mathlib_searches`; inherited records remain identified by their original dates/results.

## Not duplicates

No new nodes. Scalar extensionality and arbitrary-dimensional dual separation already have nodes and are cited directly. Exponent shifting, coset arithmetic, and closure under finite linear combinations are elementary steps, not additional nodes.

## Review by Q34

I read Milne Proposition 1.11 and Remark 1.14 on printed p.10 to check that joint injectivity is the intended source input. Its algebra-coefficient discussion is not itself a vector-valued statement, so the proof explicitly reduces to scalar coefficients using linear functionals and records agent origin. No SGA source is used. There are no new-node sources to audit.

Step 1 defines the quotient concretely as cosets, so its linearity and the equivalence `[v]=0` iff `v` belongs to `W` follow directly from that equivalence relation. Applying the quotient map to the finite evaluation sum uses only linearity. Empty support is settled before any maximum is needed. It cites no non-elementary theorem.

Step 2 uses exactly the statement of `lem-sfb-mvpolynomial-infinite-evaluation`: equality at every assignment over an infinite integral domain implies equality of polynomials. A field supplies a nonzero commutative domain; the stated infinitude supplies the remaining hypothesis. I wrote the shift explicitly with every shifted exponent at least one. This ensures vanishing even on coordinate hyperplanes; on nonzero tuples the displayed integer-power factorization gives vanishing. Thus the cited theorem is applied on all of affine space, which its statement requires, rather than incorrectly treating its domain as just the torus. The injectivity of translation of exponent tuples identifies each scalar coefficient without collisions. This is one finite-sum computation and the cited extensionality application, with no hidden geometric-density lemma.

Step 3 uses exactly the statement of `lem-weil-pbc-vector-space-dual-separates`: a nonzero vector in any vector space over a field admits a linear functional nonzero on it. I checked that there is no finite-dimensionality restriction. Applied to the quotient vector space, it contradicts the scalar vanishing from step 2. The resulting zero cosets give the required membership, including zero coefficients off the support. Both citations use their nodes' statements, not arguments hidden in their proofs; `citations.json` quotes those full statements verbatim.

Step 4 is the reverse implication by the defining closure conditions for a linear subspace. I checked the empty sum, `r=0`, `V=0`, `W=0`, and `W=V`. For `r=0` the scalar polynomial is a constant, there is one assignment, and no zero-coordinate case is needed. For a single negative exponent, such as `u=-2`, the chosen shift is `a=3`, giving the ordinary exponent `1` and the required vanishing at zero. Infinitude is necessary: over the two-element field, the scalar Laurent polynomial `z-1` vanishes at the only nonzero point but has nonzero coefficients.

Against delivery-errors B–E, I checked all notions in the statement are either explicit or have the existing field dependency; TeX is singly escaped; there are no new nodes needing statement-only, source-tag or leaf checks; both non-elementary inputs are cited and introduce no cycle; no clause is simply outsourced to a new node; and each hypothesis of both reused results holds. Every proof step is below 2000 characters (459, 954, 410, 401). The exponent shift is written out instead of saying only “clear denominators.” The statement, source and maintainer-owned fields are preserved.
