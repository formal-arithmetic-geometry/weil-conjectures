## What changed

Proved `AlgebraicGeometry.ProEtale.pullback_constantModelConstructible` in the assigned
module, preserving every existing public signature and the canonical stratification
definition. Added proof imports of
`Sheaf.AlgebraicGeometry.ScalarPresentationCokernel` and
`Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage`.

Five proved private helpers reconstruct a finite scalar matrix from a presentation,
identify pullback of its scalar-extension cokernel with the same scalar model,
compare restrictions over a commuting square, assemble two commuting squares, and
specialize to the canonical base-changed cover. The private assembly theorem reuses
the already proved private `pullback_constructible` from
`Sheaf.Paper.UnboundedLocalizingPullback` through a proof-only `import all`.
The module and DAG graph checks show no path from that dependency to this item.
Its first-clause proof uses `pullback_finiteConstantLocalModel` and the canonical
stratification pullback. No coefficient admissibility case split is needed.

Added the elementary public predicate `HasScalarModelOnRestriction`, defined as
the existing isomorphism condition for a twice-restricted module and the specified
scalar model. `ConstantModelPullbackStatement` now uses that predicate for both
local-model clauses. Its mathematical meaning, all quantified input data and
hypotheses, and the canonical cover/stratification remain unchanged. The public
theorem signature and `constantModelPullbackStratification` are verbatim.
The named predicate prevents repeated expansion of inverse-image module objects
inside the isomorphism type during kernel conversion. The original spelling
consistently exceeded 60 seconds even with fully typed square comparisons; the
named predicate made the comparison checks fast at a diagnostic 10,000 heartbeats.
No compiler limit is raised. The local elaboration/transparency attributes are
not exported. The predicate is an additional elementary Lean attachment of the
existing node; no new mathematical statement or node is introduced.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.pullback_constantModelConstructible`
(node `lem-sfb-pullback-constant-model-constructible`). Added 0 holes. No `sorry`
remains in the delivered module. This is a proof from existing declarations, with
no split-off statement and no new node.

Validation: the complete named-predicate proof compiled cleanly on the server.
The final item and the unchanged external consumer
`Sheaf.Paper.RationalClosedSupportConstructible` also compiled together in import
order against the sandbox build (exit 0 for both). The temporary consumer copy
was removed before delivery; it is not an adaptation. Delivery checks independently
record compilation and axioms.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`:
the canonical typed `Scheme.Cover.pullback₂` already supplies the full pulled-back
cover. Removed its node `det-pe-topos-functoriality-inverse-image` from proof dependencies
and the obsolete top-level tool-use entry. The replacement is the existing pro-etale
site and cover construction, not a different stratification or cover.

Also removed redundant private imports of
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Sheaf.Paper.CartesianCoefficients`,
`Sheaf.Paper.CondensedConstantConstructibility`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`. The statement
and proof APIs that remain used are already supplied through retained imports.
No source-library declaration or module is withdrawn. The finite scalar
presentation and matrix inverse image dependencies remain needed. The constructible preimage result remains used
inside the existing canonical stratification pullback construction.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The rework table still lists this
item as quarantined, but its current source is present in `lean/`; this delivery
starts from that current source and retains its attachments and public definitions.
The DAG did not record that the first clause already has a complete private proof
in `UnboundedLocalizingPullback`; this delivery reuses that proof.
The public proposition is definitionally the same after unfolding the new
predicate. The external consumer is `Sheaf.Paper.RationalClosedSupportConstructible`;
its source uses the same theorem and constructibility clause. The unit route
remains intact.

Proof-context change record:
`coord/changes/C3-constant-model-pullback-proof-context.md`.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
