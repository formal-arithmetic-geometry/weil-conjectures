## What changed

Restored the completed J4 proof from commit
151ca122b777a5ab448db2bcea176f435bbd4a6e, as requested by the current D5 return
entry. That entry records that the delivery was removed only by the now-fixed
transitive-importer rollback rule. This packet restores its Lean proof and merges
its three proof-related DAG fields into the current node, preserving current
statement and review metadata.

The module proves projection_isIso from the existing finite-ring proper projection
formula and hasProjectionFormulaOfCompactification_of_comparison. The ordinary
shifted Tate coefficient is bounded in [-2,-2]; exact chart pullback and open
extension preserve boundedness. The finite Tor interval of Ke bounds the required
proper-factor tensor below. The canonical comparison reduction proves the actual
projection component invertible, and the two signed symmetries preserve this.
The four proved private generic helpers keep concrete coefficient definitions
out of expensive elaboration. primeUnit uses coefficientPrime_isUnit_stalk and
the ringed-space local criterion for units.

Added the private proof import
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula.
All existing public signatures, public imports and non-theorem constructions
are preserved. No definition repair or consumer adaptation is required.

## Proved and sorry left

Closed 2 of 2 original holes, both attached to
`def-pur-affine-line-purity-comparison`:

- AlgebraicGeometry.ProEtale.AffineLinePurity.projection_isIso
- AlgebraicGeometry.ProEtale.AffineLinePurity.primeUnit

No sorry remains in the item, no hole is added, and no statement is split off.
All four private helpers are proved. Existing holes in imported modules are
unchanged. This is restoration of J4's completed work, not an additional pair
of proofs beyond that earlier delivery.

## No longer needed

No imports removed; no nodes or modules withdrawn. The specialized
AlgebraicGeometry.Etale.isIso_finiteCompactProjection wrapper is unnecessary:
its general comparison reduction applies directly to the finite coefficient
ring, requiring boundedness rather than constructibility of the first input.
No finite-field coefficient transport is needed. This retains the compact-support
projection step of sk-prop-an Step 5(c).

The existing public imports remain part of the preserved interface and are
already reexported through AffineLinePuritySource. The finite-Tor comparison,
standard charts, Noetherianity and dimension bounds are not additional proof
obligations of these two lemmas; their roles in the unchanged definitions and
applicability conventions are preserved. No closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The current return explicitly authorizes restoration of the finished J4 version;
there is no mathematical repair requested. The current base again has the two
original holes and an empty proof plan, so the prior completed proof and its
three DAG steps are restored. The proof uses fewer hypotheses than the public
projection theorem, retaining every geometric applicability parameter unchanged.

Ran leanfinder, loogle and grep searches through msearch, followed by direct
source searches. Mathlib has the local unit criterion; the adopted source
library supplies the projection comparison reduction. Read the current blueprint
comparison display and sk-prop-an Step 5(c). The empty base and zero or shifted
coefficient complexes require no exceptions: boundedness, exact inverse image
and the projection theorem apply uniformly.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
