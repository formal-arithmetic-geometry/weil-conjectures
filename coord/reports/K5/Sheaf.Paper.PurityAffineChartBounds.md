## What changed

Proved `AlgebraicGeometry.Scheme.sf_purity_affine_chart_bounds` with its original
signature and every existing definition unchanged. All new helpers are private and proved.
The proof uses the published fixed-scalar étale library directly: compute the
coefficient exponent, obtain the finite dimension bound, prove cohomological bounds by
smooth duality and the closed-support triangle, use the existing chartwise Tor theorem,
glue along the supplied finite chart cover, and transport through the exact pro-étale
comparison. The empty source is handled by the empty finite cover.

The final common interval is exactly `[a-2D,b-2D+c]`; its upper endpoint simplifies
to `b+2*dim(Y)+1` for nonempty X. The finite-Tor clause proves both bounded
constructible membership and the stated Tor interval, testing all module sheaves.
The finite coefficient ring is the actual quotient for the arbitrary supplied E,
not a replacement coefficient field or a chosen arbitrary existence witness.

Added proof imports:
- `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible`;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`.

Updated the existing node's proof, proof_deps and proof_origin to describe this route,
and withdrew its unused ambient-adjunction tool approval. The current unit route is
preserved: closed support, smooth rank-one duality, affine factorization and finite-cover
gluing. No definition or statement repair, consumer adaptation, or new public API.

Validation: the complete module compiled cleanly through lcompile.py (9.1 seconds)
after removing the unused EtaleClosedSupportAmplitude proof import. The unchanged
public declarations and definitions were compared against the current source.
The redundant explicit `Mathlib.FieldTheory.Finite.Basic` proof import was also
removed: it is already publicly available through the comparison dependency.
Searches retained from the earlier attempts include LeanFinder, Loogle, and grep;
reading the actual source signatures found the chartwise Tor theorem. Import-direction
checks accept both new WeilConjectures imports.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.sf_purity_affine_chart_bounds`
(node `cor-pur-general-admissibility-datum`).

Added 0 holes; split off 0 statements. There are 0 remaining `sorry`s in the delivered
module. This is a proof from existing declared dependencies, not a decomposition.
The smooth-duality and comparison results used from the existing library retain their
own prior proof dependencies; no claim is made to close those separately assigned items.

## No longer needed

Removed these original proof imports:
- `Sheaf.AlgebraicGeometry.OpenComplementCondition`;
- `Sheaf.Paper.OpenComplementUnconditional`;
- `Sheaf.Paper.PurityGeneralAdmissibility`.

The unit-route imports `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals` and
`Sheaf.Paper.FiniteTorAmplitudeSites` are retained as required by preflight.
The removed bundled open-complement interfaces are unnecessary for
this fixed-scalar statement. The proof uses the source-library chartwise Tor theorem
and directly proves the cohomological chart interval. In particular the separate
`thm-pur-general-admissibility`, `thm-pur-open-complement-unconditional`, and
`def-exc-open-complement-bound` proof edges are unnecessary. The standalone intrinsic
`def-weil-constructible-intervals` and `def-weil-finite-tor-amplitude` proof edges are
also unnecessary: the original statement already uses the existing fixed-scalar
predicates. Their statement dependencies are preserved. The
`cor-sf-ambient-adjoint-discharge` proof edge and tool approval are withdrawn: the
proof needs only the defining comparison composite and the comparison unit on bounded
constructible inputs, never an additional adjunction theorem. The
`def-weil-pbc-proetale-site` proof edge is replaced by the empty-cover proof and the
comparison declarations; the underlying site in the statement is unchanged.

These are removed dependencies of this item, not claims that no other parent uses
these nodes or modules. No module is withdrawn. No unit statement or proof step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared `PurityFiniteSetting.general_admissibility` interface is expressed using a
finite intermediate field of a fixed coefficient closure and intrinsic ringed module
categories. This item quantifies over an arbitrary finite extension E and uses the
published fixed-scalar module-sheaf derived categories. Applying that interface would
require substantial extra coefficient transport. The existing source-library
`Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart` already accepts
the actual finite ring with invertible exponent and supplies the exact required chart
bound. Using it is shorter and follows the same mathematical smooth/closed unit route.
For the cohomological clause without a Tor hypothesis, the closed-support triangle,
finite truncation devissage, and flat rank-one smooth duality give the corresponding
bound directly. No statement has been weakened or changed.

The retained draft's final cohomological comparison step asked typeclass search to
recover bounds on an underspecified comparison object. Transporting the complete
`homologyConcentratedIn` property across the same explicit isomorphism resolves it.
There were no missing mathematical steps or new intermediate holes.

Preflight requested preservation of the two unit-route imports and reported the added
top-level opens as an interface change. Both unit-route imports were restored and the
original top-level command context was restored; no change record is needed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
