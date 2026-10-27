## What changed

Proved `AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization` with its
signature unchanged. The isomorphism composes the proved `globalCoefficientIso` with the
source library's `padicAlgClSheafIsoAdicConstantSheaf`; its ring law follows from their
existing `IsMonHom` instances. Four proved private helpers identify the finite-field
comparison with the actual adjoint chart, compute the native finite-field inclusion,
prove naturality of the coefficient mate, and compare finite-field inclusions under
scheme direct image. The ring-colimit extensionality of
`completedCondensedAlgebraicClosure` combines them into the required square. The
monoidal comparison between direct image followed by coefficient forgetting and
coefficient forgetting followed by direct image identifies the two target ring
structures; its underlying morphism is the identity.

Added proof imports of `Sheaf.Paper.CondensedQbarCoefficientConstruction`,
`Sheaf.Paper.ContinuousChartSchemeNaturality`, and
`WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing`. Updated the item's node
proof, proof dependencies, and proof origin to this reuse route. No public interface,
source-library declaration, definition, or target statement changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization`
(node `lem-sf-locally-finite-coefficient-ring-realization`).
Added 0 holes; split off 0 statements. There are no remaining `sorry`s in the item or
in any added file. All four private helpers are completely proved. The complete module compiled through
`lcompile.py` in 29.9 seconds with no errors or warnings; the original theorem
signature was compared verbatim and is unchanged.

## No longer needed

Removed these proof imports from this item:

- `Sheaf.Paper.FiniteSubextensionsDirected`: the native comparison already proves local
  factorization through a finite field.
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`: the existing finite-field comparison
  already provides the required isomorphism.
- `Sheaf.Paper.ProfinitePointPullback`: scheme naturality uses the proved continuous
  chart naturality theorem and the existing coefficient-mate definitions.

The corresponding direct proof dependencies are no longer needed:
`det-def-sfb-qlbar-condensed-subextensions`, `lem-weil-l-adic-extension-absolute-value`,
and `lem-weil-pbc-profinite-point-pullback`.
Also removed the direct proof use of `def-weil-pbc-proetale-site`: the source native
isomorphism already proves the required local gluing. The obsolete top-level
`tool_uses` entries for those three nodes were removed, retaining the continuous
coefficient realization and completed-coefficient colimit approvals. These are local
dependency removals; no assertion is made that a module has no other library consumers.
No module is withdrawn.

Retained `Sheaf.Paper.CompletedCondensedCoefficients` and
`sk-prop-sfb-qlbar-colimit-x` as required by the unit route. Delivery preflight
identified this route requirement; the packet now preserves it.

## Where the brief, the DAG or earlier work was wrong

The planned local gluing argument is valid, but the adopted source library already
contains its complete implementation in `PadicAlgClSheafIso` and its ring compatibility
in `PadicAlgClSheafRing`. Reusing those and the existing bounded realization is shorter.
The unit statement and route are preserved. Empty schemes, the zero function, and
non-quasi-compact schemes are covered by the existing sheafification comparison; the
proof never assumes that a sheaf colimit is computed objectwise on arbitrary schemes.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
