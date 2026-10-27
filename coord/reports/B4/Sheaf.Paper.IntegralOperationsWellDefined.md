## What changed

Proved `WeilConjectures.integralOperationsPullbackTransition_existsUnique` in
`Sheaf.Paper.IntegralOperationsWellDefined`. The canonical finite reduction transition
is semilinear over the quotient map; adjunction mates construct the finite pullback
transition. Local surjectivity of the completed coefficient projection and the
adjunction unit prove uniqueness from its generators. The restored helper module
`Sheaf.Paper.IntegralReductionTransitionSemilinear` proves the semilinearity theorem.

Every existing public definition, statement signature and public import is retained.
The new proved zero-map and finite totalization interfaces keep private declarations
out of public definition bodies. The retained complete invariance and descent proofs
reuse the existing cone quasi-isomorphism theorem, independent-coefficient reduction
object/map equations, functorial flat resolution, and exact pro-etale products theorem.
Local instance choices and irreducibility annotations control expansion. The named
base-change continuity proof and generic countable-totalization proof avoid
repeated concrete instance searches. Exact products also supply the derived-product
instance directly.

Change record: `coord/changes/integral-transition-semilinearity.md`.
Validation: the complete partial module compiled in 59.3 seconds, recorded in
`scratchpad/partial-explicit-instance.log`. Delivery checks are run separately.

## Proved and sorry left

Original holes: 2. Holes closed: 1. Holes added: 0. Holes remaining: 1.

- Proved `WeilConjectures.integralOperationsPullbackTransition_existsUnique`.
- Retained the original `sorry` in
  `WeilConjectures.integralOperationsTensorTransition_existsUnique`
  (node `lem-pur-integral-operations-well-defined`). Its statement and proof plan
  remain unchanged in the Lean module.
- Proved `WeilConjectures.unrestrictedIntegralTransition_smul` in the restored helper;
  that module contains zero holes.

No unfinished theorem is split off. The final well-definedness theorem and all
previously complete proofs remain complete.

## No longer needed

Removed direct proof imports `Mathlib.Algebra.Homology.BifunctorFlip` and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`: the existing
independent-coefficient left and right tensor quasi-isomorphism helpers provide
these comparisons. Removed direct imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` and
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`: the existing
functorial-resolution theorem supplies their former local uses. Their source
statements and transitive dependencies remain in the library.

The local cone-triangle proof, exact-products epi proof, and flat-resolution
construction are replaced by existing proved library theorems. No module is
withdrawn, no node is pruned from the unit route, and no adopted source declaration
is removed. The unfinished tensor transition still requires its tensor argument;
no pruning of that argument is claimed.

## Where the brief, the DAG or earlier work was wrong

The final well-definedness theorem was already proved. The two original holes were
its pullback and tensor transition characterizations. The returned R2 archive
supplied their argument. A complete native version of both transition proofs
compiled earlier in 53.8 seconds (`scratchpad/native-private-final-set.log`), but
fresh whole-file checks repeatedly exceeded the current 60-second limit. The
byte-identical current repository module also timed out. After extensive profiling,
proof reuse and definitional-opacity changes, this partial delivery passes the
limit while preserving one original hole. No compile timeout is reported as a
broken tool, and no proof is split into files to evade the limit.

The session began on 2026-10-22. Provider-error resumptions retained its work; the
dispatcher reset its reference clock to 2026-10-23 04:19:59 UTC. No budget metadata
was edited. The original safety stop passed during compile-service failures and
subsequent proof optimization. No target statement is weakened.

## New nodes

`lem-pur-integral-reduction-transition-semilinear`, restored from the repair archive,
records scalar compatibility of the canonical finite reduction transition.
Its theorem is fully proved, with zero new holes. Source: Stacks Tag 03EK.
The three search kinds are recorded in its node. The main node records the completed
pullback argument, the remaining tensor step, and the library results used by
invariance and descent.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
