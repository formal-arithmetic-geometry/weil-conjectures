## What changed

Proved `AlgebraicGeometry.Etale.vectorIntegration_identity_unit` in
`Sheaf.AlgebraicGeometry.VectorIntegrationIdentityUnit` with the existing statement
and canonical comparisons unchanged. Added private proof helpers for the
constant-sheaf identity with general abelian coefficients and exact derived
identity coherence on a degree-zero object. The former generalizes the proved
argument in `WeilConjectures.AlgebraicGeometry.ConstantPullbackIdentityCoherence`;
the latter uses the already proved `SheafExactDegreeZero.unit_id`.

Added a proof-only import of `Sheaf.CategoryTheory.ExactDegreeZero`. The original
public import already supplies the underived coherence API through
`EtaleFiniteTwistPullback`, so an extra direct coherence import was removed.
Updated the node's proof and proof dependencies to record this implementation.
The local instance priorities reuse the existing abelian and derived-category
proof constants captured by `DerivedCategoryModule`, as in
`OrdinarySupportedKummerSystem`. This avoids expensive kernel conversion between
proof constants. No mathematical data, definition body, public signature,
public import or target changes.

Validation: `lcompile.py` compiled the proof with no warnings or errors in
47.9 seconds, below the 60-second file limit. The initial compile exceeded that
limit; profiling identified kernel conversion between category-instance proofs.
Aligning the existing instance proofs resolved it. The redundant direct coherence
import was then removed; delivery performs the final compile and axiom probe.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.vectorIntegration_identity_unit`
(node `lem-pur-vector-integration-identity-unit`). Zero holes added, zero holes
left in the delivered module; both private helpers have complete proofs.

## No longer needed

Removed the redundant direct proof import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`, which is already
publicly available through the original import. Both original declared
dependencies remain necessary for the canonical maps in the statement.
No original import, node or module is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing generic exact degree-zero identity API already proves the derived
coherence needed here. Its `unit_id` equation avoids another decomposition of
this obligation. The earlier constant-pullback identity theorem is specialized
to abelian groups, so its proof is generalized locally to the module coefficients
of this item. No statement defect was found; the proof imposes no finiteness,
nonzero-ring or nonempty-scheme hypothesis.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
