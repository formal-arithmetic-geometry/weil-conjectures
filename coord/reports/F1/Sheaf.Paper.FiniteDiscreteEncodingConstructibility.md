## What changed

Completed `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_constructibility`
in `Sheaf.Paper.FiniteDiscreteEncodingConstructibility`, preserving its complete signature
and public imports. Added proof imports of `FiniteDiscreteEncodingPullbackFixed`,
`FiniteDiscreteScalarConstantModels`, and the source-library derived `ExactFunctor` API.
All six private helpers are proved. No definition or instance was changed.

The local-model proof retains the same cover and uses the existing scalar-cover comparison,
normalized pullback comparison and scalar constant-model equivalence. The comparison then
uses the same finite stratification and, for non-qcqs schemes, every affine open. Finally
homology comparison and preservation/reflection of boundedness prove the derived clause.
The original blueprint unit statement and route remain intact. Updated only the item's
node proof, proof_deps and proof_origin to describe this argument.

Validation: lcompile.py compiled the entire delivered Lean module successfully, exit 0,
without errors or warnings. Import-direction checks passed for both new Sheaf proof imports.
LeanFinder found the general mapDerivedCategory API; Loogle and Mathlib grep found no
complete comparison. Local search found the existing scalar-model and pullback results,
and the proved source-library homology and boundedness API, which the proof uses directly.
No new mathematical statement requires an edge-case assumption: zero rings, empty schemes,
zero modules and arbitrary schemes are retained by the existing comparisons and predicates.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_constructibility`
(node `lem-sf-finite-discrete-encoding-constructibility`).
Added 0 holes; split off 0 statements. There are no remaining sorry declarations in the
item or elsewhere in this delivery.

## No longer needed

No original import was removed and no module is withdrawn. The item's old direct proof
edges to `lem-sf-finite-discrete-encoding-naturality`,
`sk-def-sfb-module-pushforward-pullback`, `def-weil-pbc-proetale-operations`,
`def-sfb-finitely-presented-module`, and `def-weil-pbc-sheafification` are replaced by
applications of the existing proved comparison lemmas. Their underlying APIs can remain
transitive dependencies of those comparisons; no declaration or module is claimed globally
unnecessary. `sk-def-sfb-constructible` remains a direct dependency.

The tools `lem-pe-finite-discrete-encoding-pullback-fixed`,
`lem-pe-finite-discrete-scalar-constant-models`, and
`det-def-sfb-constructible-local-model` come from the coefficient unit and are reused here
for the identical normalized encoding and scalar-cover formulation. The source-library
`lem-weil-pbc-exact-functor-bounded-below` API provides the homology isomorphism and the
proved boundedness lemmas. Reusing these results avoids duplicating their proofs; no unit
step is bypassed. Maintainer tool approvals, if required, are left to the reviewer.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The original DAG plan described the correct
argument, but its direct dependency list predated the existing proved pullback and finite
scalar-model comparisons. The proof now uses those declarations rather than reconstructing
their scalar-action and presentation arguments.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
