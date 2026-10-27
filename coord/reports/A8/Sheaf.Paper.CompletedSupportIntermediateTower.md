## What changed

Proved `finiteOpenTensor_isIso` and `finiteRingUnit_isIso` without changing their
statements, definitions, attributes or imports. All changes to Lean are in the
assigned module. Updated its three attached node proof records to match the proofs.

The open tensor comparison is a double inverse mate. Mathlib's
`iterated_mateEquiv_conjugateEquiv_symm` identifies it with conjugation of the
restriction/pullback isomorphism, which preserves invertibility.

For the ring unit, `rho_unit` transports its scalar restriction to the
constant-coefficient unit. The existing `strictUnits` theorem gives invertibility
after constant reduction. A proved private homology argument establishes that
exact conservative scalar restriction remains conservative on derived categories.
Transport through `rho` proves the full strict-tower assertion; evaluation and
quotient scalar restriction give the finite assertion. The same private argument
simplifies the existing proof of `ringReducedUnit`.

Validation: the complete module compiled on the server in 33.0 seconds before the
final proof-docstring updates. The delivery command checks the final packet.
The proofs use existing declared dependencies, including their postponed theorems;
this delivery does not assert that the target import closure is axiom-free.

## Proved and sorry left

Closed two of the module's three original holes:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteOpenTensor_isIso`
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteRingUnit_isIso`

One original hole remains unchanged:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.strictFiniteCoherence`

Added zero holes and zero split-off statements. All three new private helpers
(`exactDerivedReflects`, `restrictionReflects`, `ringTowerUnit_isIso`) are proved.
The remaining theorem concerns strict proper/open evaluation and scalar
normalization equations, beyond the two invertibility subcalculations closed here.

## No longer needed

No imports, whole modules or nodes are withdrawn. The finite-open proof no longer
needs the earlier proposed equivalence of open adjunctions. Its direct proof
requirements are the scalar-extension and open adjunctions and the canonical
restriction/pullback isomorphism; the finite-constant transport and ordered
exchange coefficient-comparison nodes are removed from this subproof's
`proof_deps`, but retained wherever the existing module and statements use them.

The finite-ring proof uses the already stated strict-unit theorem and normalized
coefficient data instead of a new quotient/Koszul computation. Its previous direct
proof dependencies on finite-constant transport and the higher-level ordered
exchange coefficient-comparison node are replaced by the actual ambient strict-unit,
coefficient-data, scalar-restriction and reduction-evaluation nodes. No whole-library
pruning is claimed.

The existing `ringReducedUnit` proof no longer calls `finiteUnits` or reconstructs
tower invertibility from every finite evaluation; it follows directly from the
normalized full-tower argument.

## Where the brief, the DAG or earlier work was wrong

The finite-open node's previous proof said the open adjunctions were equivalences
and inferred that the inverse mate of an isomorphism was invertible. Open extension
and pullback are not equivalences on the ambient module categories, and a single
mate need not preserve invertibility. The specified reduction comparison is itself
a scalar-adjunction mate, so the double-mate/conjugation identity supplies the
correct proof without changing any statement.

The main node still described several holes already relocated or proved by earlier
deliveries. Its implementation paragraph now records the current remaining hole
and the proof route used here. No shared definition or target statement changes.

The required searches found no direct completed-support theorem: leanfinder
returned ordinary adic-completion tensor results, and loogle returned no match for
mate invertibility. Reading Mathlib's adjunction-mates implementation located the
iterated-mates identity used in the proof.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
