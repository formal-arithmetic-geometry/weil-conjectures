## What changed

Replaced the sorry in `Sheaf.Paper.DiagonalLimitEndpoints` with a proof of the unchanged
statement from one strictly smaller ordinary source-limit assertion. The root-limit
comparison is lifted sectionwise to constant Z_l-linear maps using prime-power torsion.
Quotient and root transitions are epic. The Milnor/Roos comparison identifies the
canonical ordinary-to-derived limit maps with the unit of a normalized total right derived
limit.

Proved all four completeness assertions directly: the difference endomorphism on the
countable power of a prime-power-torsion object has a finite geometric inverse. This
passes to limits, through scalar restriction, and through the single-complex embedding
because countable products are exact. Product preservation uses the proved
`DerivedCategory.isLimitFanQ` and its instance in
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`. Maps from an ell-invertible
object then vanish. Shifts and the canonical derived restriction comparisons transport
this orthogonality to the stated endpoints.

The generic arguments follow the existing proved helpers in
`DiagonalTraceOrdinaryLimitEpi`, `DiagonalTowerLimit`, and
`DiagonalCompletedLineCompleteAux`. Those modules import the final diagonal theorem, so
importing them here would create a cycle. Their necessary generic arguments are proved
locally or in the new proved generic module, using the existing Milnor, Roos,
exact-products, root-transition, and right-derived-functor declarations. All imports added
to the item are private proof imports; the original public import and theorem signature
stay unchanged. Generic comparison and completeness helpers, and the root-transition lemma
for an abstract scheme, keep type checking from expanding the concrete completed scalar
functors. The product-comparison proof uses explicit projection equations. Scalar
forgetting is compared through an explicit natural isomorphism instead of conversion of
the entire functor structures; the diagnostic check of this preservation instance fell
from about 19 seconds to 0.45 seconds, and the completed-category specialization checks in
about one second. Constructing normalized derived-limit data retains its existing
`toDiagonalRightDerived` parent directly, instead of reconstructing all inherited fields
with a record update. A private specialization shares scalar-restriction instances before
inserting the concrete surface and endpoints. No existing definition, public instance, or
other module is changed.

The final assembly uses specialized, proved derived-limit existence and comparison
helpers. Its existential witnesses stay inside the theorem proof; it introduces no
new data definition. The four completeness properties are passed as one conjunction.
The unchanged characteristic and completion hypotheses are unused by this route;
the unused-variable linter is disabled only for the original theorem.

Validation: `lcompile.py --all` passes for all four modules. The clean run checks
the ordinary-source statement in 1.7 seconds, the proved auxiliary module in
37.0 seconds and the unchanged endpoint theorem in 53.2 seconds. The generic
orthogonality module passed in 7.8 seconds on its uncached compile and is reused
in this run. No diagnostic options or scratch Lean modules are delivered.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.diagonal_limit_endpoints` (node
`lem-sfb-diagonal-limit-endpoints`). The item module has zero sorries.

Added one hole in `AlgebraicGeometry.ProEtale.diagonal_supported_ordinary_limit`, in
`Sheaf.Paper.DiagonalSupportedOrdinaryLimit` (node
`lem-sfb-diagonal-supported-ordinary-limit`). It concerns only the ordinary supported
quotient-tower limit and its generator projections. It makes no root, derived-limit,
comparison-isomorphism, or orthogonality assertion. The parent proves those parts in Lean.
The statement uses only an ordinary reduction presentation and a scheme, rather than any
of the parent's derived, root, completion, or finiteness data. Its empty-scheme and
level-zero cases agree with the construction.

One original hole closed and one strictly smaller hole added: this is a **decomposition**,
with net zero holes closed, not a claim that the whole endpoint theorem is free of sorry
dependencies. All private helpers are proved.

Also proved `AlgebraicGeometry.ProEtale.DiagonalEndpointsProof.root_limit_iso`
(node `lem-sfb-diagonal-root-limit-linear`), with zero holes.

Also proved `CategoryTheory.finite_tower_limit_orthogonality` in
`Sheaf.Algebra.Homology.FiniteTowerLimitOrthogonality` (node
`lem-sfb-finite-tower-limit-orthogonality`), with zero holes.

## No longer needed

No previously present import was removed: the item originally imported only its interface.
The actual proof does not need these planned proof dependencies:

- `lem-sfb-constant-principal-complete-orthogonality`
  (`Sheaf.Paper.ConstantPrincipalCompleteOrthogonality`);
- `lem-weil-pbc-constant-completion-equivalence`
  (`Sheaf.Paper.ConstantCompletionCore`);
- `lem-weil-pbc-flat-ringed-ideal-complete-equivalence`
  (`Sheaf.Paper.FlatRingedIdealCompleteEquivalence`).

Finite-torsion telescopes prove the required orthogonality directly, in both coefficient
categories, so none of those complete-object equivalences is used. The planned dependency
`lem-pur-twist-sheaf-locally-free` is replaced by the smaller proved root-transition
epimorphism theorem and finite root torsion. The broad
`det-prop-sfb-qlbar-colimit-x-integral-limit` comparison is not used as a proof lemma:
here the completed coefficient sheaf is already defined as the finite-ring limit. Its
module remains publicly imported by the unchanged interface, so this delivery does not
claim to remove it from the import closure.

Closed direct-image exactness and the normalized finite source quotient remain needed by
the ordinary supported-source calculation in the new node. No unit, source-library
declaration, module, or DAG node is withdrawn. The three unused complete-object lemmas are
removed from this node's proof dependencies; other parents may still need them.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The unit's ordinary-limit, canonical comparison, and
intrinsic-completeness steps remain. The original node proposed using
DiagonalCompletionSpec and flat complete-object equivalences to prove orthogonality. That
is unnecessary for these two finite-torsion tower limits: the exact-product telescope
argument proves it directly. The hcompletion hypothesis remains verbatim in the public
theorem, although this proof does not use it. The existing ordinary source quotient
theorem supplies finite levels, but does not assert their completed ordinary limit with
all generator equations; that precise remaining calculation is the new node.

## New nodes

`lem-sfb-diagonal-supported-ordinary-limit`, module
`Sheaf.Paper.DiagonalSupportedOrdinaryLimit`, isolates paragraph (1)'s ordinary supported
source limit, including every generator projection. Its docstring and node give the
scalar-extension, finite cokernel comparison, transition, limit-preservation and
coefficient-unit argument. It is strictly one part of the parent's argument.

`lem-sfb-finite-tower-limit-orthogonality`, module
`Sheaf.Algebra.Homology.FiniteTowerLimitOrthogonality`, is a fully proved generic
finite-torsion telescope lemma with no new sorry. It supplies all four orthogonality
conclusions under exact countable products and conservative, product-preserving exact F.
Its shift is arbitrary. The cases l=0 and l=1 are valid as well. This packages the
independent categorical argument without changing any shared definition. After reducing
definition expansion with local irreducibility and explicit projection equations, this
self-contained part is checked in its own module. No change record is needed: only the
item proof, its proof-route node, and these new modules and nodes are changed.

`lem-sfb-diagonal-root-limit-linear`, module
`Sheaf.Paper.DiagonalLimitEndpointsAux`, proves the linear lift of the prescribed
abelian root-limit comparison, with zero holes. The remaining helpers in this
module are proved and private; the endpoint assembly imports them explicitly
with `import all`. They cover Milnor/Roos comparison, total derived-limit
normalization, scalar restriction and the completeness specialization. The root
comparison has its own full sourced proof and node.

## Related modules compiled before delivery

11 related module(s) compiled against this delivery by deliver3.py: 11 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.FiniteTowerLimitOrthogonality": "9cbde975820f462cecbd1acbf3ff468f16e1eef1", "Sheaf.Paper.DiagonalLimitEndpoints": "0ab1b1f906209458f23790547c56b4ea190a6ba5", "Sheaf.Paper.DiagonalLimitEndpointsAux": "0c0504c7d6fd8a8bf50b0054786f868bedfe4ae7", "Sheaf.Paper.DiagonalSupportedOrdinaryLimit": "cb86f3e20269ecacdf4b4f102c580f4f55ff6539"}, "results": {"Sheaf.Paper.CompletedChernNormalizedUnique": {"hash": "5fe0ad5979586a46eaa39c0e0d1c61bbbaf3ac55", "status": "OK"}, "Sheaf.Paper.CompletedCoefficientSectionAction": {"hash": "c82ab8f2bed87a1d43f1de0991c2e00c6aafe9db", "status": "OK"}, "Sheaf.Paper.DiagonalCompletedChernSplitting": {"hash": "101bf3c096b9d0529c703a05c9e8092d62c3e4d0", "status": "OK"}, "Sheaf.Paper.DiagonalCompletedLineCompleteAux": {"hash": "6b576f5a4b06aa5dfa31c5e4a47ad15be5325867", "status": "OK"}, "Sheaf.Paper.DiagonalFiniteIntegralEndpoint": {"hash": "504ce95d706b70088177fff074d18f305f97024e", "status": "OK"}, "Sheaf.Paper.DiagonalLimitCompletedData": {"hash": "5e8add3ef53b70a2da962199a2365343e74e27e6", "status": "OK"}, "Sheaf.Paper.DiagonalTraceComparisonLimitIsos": {"hash": "5aac1874e0d339c10a2e8f8a15d10c2b17e44547", "status": "OK"}, "Sheaf.Paper.DiagonalTraceComparisonPartial": {"hash": "d4dc322a23b1c516f8287c6e54ca6e20c3152518", "status": "OK"}, "Sheaf.Paper.DiagonalTraceResidueRestriction": {"hash": "b192a8222ffb34acd9e26180a906c1cbfa02ee03", "status": "OK"}, "Sheaf.Paper.DiagonalTraceRestrictedPushAcyclic": {"hash": "26a884e80ee4dd07255c540f71a9f059dc6e8e4b", "status": "OK"}, "Sheaf.Paper.DiagonalTraceUnitComparisonIso": {"hash": "1d902293b63b161eefa4a0561ade90a3ba12533f", "status": "OK"}}, "seconds": 201, "time": "2026-10-28T13:30:24+0800", "transitive": 10, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
