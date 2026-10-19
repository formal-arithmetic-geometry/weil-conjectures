## Worker report

Repair of returned head `96d617e65684`: the theorem previously quantified over arbitrary
`Algebra` instances and extra monomial-map hypotheses.  It now uses canonical data from the
statement. `nodalDivisorialBaseEvaluation α ε` evaluates `(n,p)` as
`((ε ^ n : Aˣ) : A) * α p`; `nodalDivisorialCoefficientAlgebra` is the corresponding
`MonoidAlgebra.lift` algebra; `nodalDivisorialMonoidAlgebraBaseAlgebra` is induced by
`MonoidAlgebra.mapDomainRingHom ℤ (nodalDivisorialBaseMap a)`; and
`nodalDivisorialTensorAlgebra` gives the canonical tensor-product `A`-algebra.  The helper
`nodalDivisorialTensorMonomial` renders all pure monomials in the three image clauses.

The first three theorem clauses are respectively fine saturation, injectivity of the
Grothendieck-group base map, and the multiplicative quotient equivalence to
`Multiplicative ℤ`.  The final clause quantifies only over `A`, `[CommRing A]`, `α`, and
`ε`, and asserts the `A`-algebra equivalence with relation
`X 0 * X 1 - ε * α a`, together with the two branch-generator images and every canonical
base-monomial image.  No arbitrary algebra structures or compatibility hypotheses remain.

Dependency used: `def-trf-fs-log-blowup`, declaration
`AlgebraicGeometry.IsFineSaturatedMonoid` from
`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`.  The existing quotient, branch, base, and
group-map definitions are retained.  Mathlib declarations used are `Con.Quotient`,
`Algebra.GrothendieckGroup`, `MonoidAlgebra.lift`, `MonoidAlgebra.mapDomainRingHom`,
`TensorProduct`, `Algebra.TensorProduct.includeLeft`, `MvPolynomial`, and `Ideal.Quotient`.

Edge cases checked: `P = 0`, `a = 0`, nonzero `a`, negative integer exponents, `A = 0`,
`α a = 0`, and zero branch exponents.  The canonical evaluation and base map remain
well-defined in all cases.

Searches: `msearch.py` leanfinder/loogle for nodal pushouts, fs monoids, Grothendieck
cokernels, and monoid-algebra base change; `rg` over `WeilConjectures/` and `lean/Sheaf/`
for nodal/chart/pushout declarations; and direct Mathlib source inspection of the canonical
monoid-algebra and tensor-product constructors.  No existing declaration states this node.

Compile evidence: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NA
lem-trf-nodal-divisorial-chart lean/Sheaf/TraceFormula/NodalDivisorialChart.lean` completed
for sandbox and library copies with no errors or warnings.  The expected theorem `sorry` is
the only postponed proof.

Second reading: NA reread the node, dependency signature and docstring, source proof, and
revised signature.  It checked that the coefficient algebra is forced by `α, ε`, the pushout
algebra by `nodalDivisorialBaseMap`, and all image clauses use the canonical tensor terms.
The returned extra-instance and extra-hypothesis defect is repaired without changing the
node's mathematical clauses.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
