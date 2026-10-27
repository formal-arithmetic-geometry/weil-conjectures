## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.qcOpenExtension_constantModelConstructible_finiteTor`
in `Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor`, with its entire signature unchanged.
The proof uses affine-local finite constant stratifications, the source library's
`Scheme.Stratification.openClosed`, the open adjunction unit, disjoint-support vanishing,
exact-functor derived homology, and the support projection formula. All helpers are private
and proved. No definition, target statement, instance, or public import was changed.

The zero-model proof supplies additivity of the point pullback on modules locally,
using its composite adjunction and preservation of finite coproducts.

The dependent reindexing of an open-closed stratification is checked first for an abstract
predicate on scheme morphisms. Specializing that proved helper avoids the kernel timeout
caused by expanding internal coefficient-module functors under a dependent sum. Local
irreducibility attributes keep those functors and their composition comparisons abstract.

Updated the existing node's proof and dependencies to match the actual proof. No other
module was edited. The existing source file is present despite its historical quarantine
row; it was copied intact before filling the proof, preserving its attachment and statement.

Validation: the cleaned proof compiled through lcompile.py in 10.9 seconds with no
errors or warnings. A text comparison verified that the complete public theorem signature
and every public import are unchanged. The delivery gate performs the final compilation
and axiom checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.qcOpenExtension_constantModelConstructible_finiteTor`
(node `lem-sfb-qc-open-extension-ctf`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. This is a proof from the existing dependency
interfaces, including whatever holes those dependencies already contain; it does not claim
their transitive axiom closure is finished.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
- The ordinary import of `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`
  is replaced by `import all` for its already proved private open-unit helper.
- `Sheaf.Paper.CartesianCoefficients`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` (already available
  through the unchanged statement imports).
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Topology.Spectral.Basic`.

The proof does not separately use the planned nodes
`def-constructible-stratification`, `det-def-sfb-constructible-local-model`,
`def-weil-closed-immersion`,
`def-weil-constructible-subset`, `def-weil-derived-cohomology-sheaves`,
`lem-weil-pbc-qcqs-scheme-spectral`,
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`,
`lem-weil-pbc-constructible-image-retrocompact-open`, or
`sk-prop-sfb-cartesian-coefficients`. The source `Stratification.openClosed` already proves
the constructible-image geometry; the exact support inverse image already handles F[0].
The reduced-complement node remains cited for its vanishing-ideal construction, while its
large aggregate characterization theorem is not imported or needed.
Removed obsolete top-level `tool_uses` approvals for
`sk-prop-sfb-cartesian-coefficients`, `lem-weil-pbc-qcqs-scheme-spectral`,
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`, and
`lem-weil-pbc-constructible-image-retrocompact-open`; the remaining approvals retain their
original order.
No whole-library withdrawal is claimed: these modules and nodes may have other consumers.
All public imports were retained to preserve the existing interface.

## Where the brief, the DAG or earlier work was wrong

The blueprint plan is mathematically valid. Several steps are already implemented in the
source library and the proved helpers of the Zariski-locality and derived-localization
modules, so no new intermediate statement is necessary. The DAG now cites these actual
interfaces, including the existing open-closed stratification and exact derived-functor
nodes. The unit's statement and route are unchanged.

Edge cases: the proof allows empty opens, empty complements, zero modules and zero scalar
rings. The complement model uses the empty finite presentation on the identity cover;
there is no nonemptiness assumption or Noetherian/field assumption. No new statement needs
an independent edge-case justification beyond these explicit constructions.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
