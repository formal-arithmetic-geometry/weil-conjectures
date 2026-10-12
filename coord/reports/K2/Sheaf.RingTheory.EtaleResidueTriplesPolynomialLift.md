## What changed

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_polynomial_lift` in
`lean/Sheaf/RingTheory/EtaleResidueTriplesPolynomialLift.lean`, preserving its signature
and existing docstrings. Updated the existing node proof steps 3 and 6 and
`proof_origin` to match the actual Mathlib APIs; `proof_deps` is unchanged. Added the proof-only import `Mathlib.Algebra.Polynomial.Lifts`.

The proof follows all six steps of the existing node. The image subring is closed under
inversion: zero is handled separately, and for a nonzero image `hunit` supplies a unit
whose inverse maps to its inverse in the field. Compatibility at the identity triple
puts the canonical image of `R` in the range. Using `Spec.residueFieldIso` and
`IsFractionRing.div_surjective` for `R / p` puts the entire residue-field image in the
range, without assuming that `R → κ(p)` is surjective or that `ψ` is injective.
`Polynomial.lifts_and_natDegree_eq_and_monic` lifts the mapped minimal polynomial,
and `Polynomial.Separable.eval₂_derivative_ne_zero` proves the simple-root condition.

Searches: LeanFinder via `msearch.py` for monic simple-root coefficient lifting found
`Polynomial.lifts_and_degree_eq_and_monic`; Loogle via `msearch.py` confirmed the type of
`Polynomial.Separable.eval₂_derivative_ne_zero`. Local `rg` searches of Mathlib and both
library roots found the monic-lifting API and examples, but no existing theorem proving
the item directly. Both APIs were read in the pinned Mathlib source.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.etaleResidueTriples_polynomial_lift`
(node `lem-weil-pbc-etale-triples-colimit-polynomial-lift`). No holes remain in the module,
no holes were added, and no intermediate statements were split off. This is a complete
proof from Mathlib and the existing definitions, not a decomposition into further holes.

Local single-file compilation passes without warnings. The delivery dry run also checks
the declaration axioms and compiles on the server before running preflight.

## No longer needed

None: no imports, nodes, or modules were removed. The existing DAG route is retained,
including the residue-field identification and minimal-polynomial steps. There is no
new dependency on filteredness, localization-transition lemmas, or other etale stages.
The `hc : IsColimit c` hypothesis is mathematically unused by this argument; a local
binding retains its reference to avoid an unused-variable warning without changing
the theorem signature.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The residue-field step can use Mathlib's fraction-field
instance for `R / p`, instead of separately lifting a residue class to `R_p`; this is the
same fraction argument and covers nonmaximal primes. The derivative step is already
available as `Polynomial.Separable.eval₂_derivative_ne_zero`.

The checkout does not contain the untracked `literature/stacks-project/algebra.tex`.
The cited source pages were read online: [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW)
for the triple category and identity triple, and
[Stacks 00UH](https://stacks.math.columbia.edu/tag/00UH) for monic coefficient lifting
in the etale argument. The explicit six-step proof is the existing node's plan;
no new assertion or source-dependent gap has been introduced.


## Second reading by K2

1. **Unchanged interface — pass.** Compared the sole delivered module with the
   repository using `diff`, and checked the docstring and entire declaration signature
   byte for byte. Only the proof and a plain proof-only polynomial-lifting import
   change. No definition, hypothesis, conclusion, target statement, or public import
   changes; no change record is required.
2. **Kernel proof — pass.** Independently compiled the module without errors or
   warnings. Reviewed inverse closure, identity-triple compatibility, fraction-field
   containment, coefficient lifting, and derivative transport. The scratch copy's
   `#print axioms` verifies the theorem's trust basis. No `sorry`, forbidden declaration,
   or hollow definition occurs in the delivered module.
3. **Split statements — pass, none.** No helper declaration, new statement, new node,
   or new hole was introduced. Checked the zero-inverse branch, nonmaximal primes
   (fraction-field containment does not require quotient-to-field surjectivity), and
   the degree-zero edge of the monic-lifting API; the minimal polynomial's root and
   separability give precisely the needed derivative inequality.
4. **Shortest route and pruning — pass.** Searched both library roots for polynomial
   lifting and simple-root arguments and read the pinned Mathlib lifting and derivative
   APIs. Related residue-polynomial and henselian results have different hypotheses
   and do not replace this proof. The proof-only `Lifts` import is used; the existing
   public imports support the statement. Every old proof dependency remains represented:
   field, triple, identity etaleness, residue-field identification and ideal residue
   field, separable algebraic extension, polynomials and separability. No module is
   pruned. Read `dag/units/sk-thm-p1.json`: this item is below its realized nodes;
   its route and all unit statement/step realizations remain intact.
5. **DAG agreement — repaired and pass.** The existing Step 3 described lifting
   through the localization, while Lean directly uses `IsFractionRing (R / p)` for
   the same ideal residue field. Updated that step to the quotient-fraction argument,
   added the precise derivative API to Step 6, and recorded the route in
   `proof_origin`. Kept the original `proof_deps`: in particular the localization
   node records `Ideal.ResidueField`, which the code still uses. No new nodes need
   validation.

Second reading changed only DAG proof bookkeeping and this report; the Lean proof
was correct and was retained. Holes closed: one,
`AlgebraicGeometry.Scheme.etaleResidueTriples_polynomial_lift`; holes added: zero;
split off: zero.
