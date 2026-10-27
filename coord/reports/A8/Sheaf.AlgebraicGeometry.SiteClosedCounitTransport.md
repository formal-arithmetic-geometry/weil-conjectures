## What changed

Proved `AlgebraicGeometry.ProEtale.siteClosedCounitTransport` with its signature unchanged.
The proof uses the supplied normalized comparison-class adjunction directly: comparison-unit
invertibility gives alpha and the allowed etale-origin counit source; naturality gives the
general adjunct formula; source naturality and injectivity give the counit equation.
The two existing compact-support comparison constructions are compared by expanding their
proper/open factors and using naturality of the bounded-below inclusion comparison.
Updated the item's proof plan and dependencies to this route. No definition, instance,
public import, target statement or consumer changes. Proof-local elaboration options
allow the canonical bounded-below inclusions to reduce during this proof only.

## Proved and sorry left

Closed the single existing hole in `AlgebraicGeometry.ProEtale.siteClosedCounitTransport`
(node `lem-coef-site-closed-counit-transport`). No holes added and no holes left in the
item. No split-off statements. Server single-file compilation passed cleanly in 27.4 seconds.
The final delivery preflight also compiles and probes the declarations for axioms.
The proof-context change record is
`coord/changes/A8-site-closed-counit-proof-context.md`.

## No longer needed

The proof does not need `lem-coef-closed-identity-open-hom-normalization` or its module
`Sheaf.Paper.ClosedIdentityOpenHomNormalization`: the given class datum already fixes
the Hom equivalence at the actual compactification, for the exact coefficient universe
and arbitrary supplied ordinary adjunction. The required comparison coherence is proved
directly from the two named constructions.

`lem-exc-closed-ambient` and its direct module import are not needed to construct an
ordinary adjunction: the theorem already takes that adjunction as an argument. Generic
Mathlib naturality and the transpose-of-counit identity suffice for the assembly.
Removed the following unused private proof imports:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` (the ambient-unit theorem is
  already publicly available from the comparison interface).
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate` (already publicly reexported).
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` (constructibility is never used).

Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for compatibility
of the termwise derived natural isomorphism with inversion.

The obsolete `lem-exc-closed-ambient` tool approval is removed from the item's node;
the remaining approvals keep their order. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's extracted normalization dependency is not an immediately applicable Lean
interface: it uses a small coefficient field, a lifted coefficient ring, the chosen
direct-image right adjoint and `specifiedExceptionalHomEquiv`, while this item has an
arbitrary supplied compact-support adjunction and normalized class datum. Its mathematical
normalization is valid, but direct use here would require unnecessary change-of-presentation
and right-adjoint-uniqueness transports. The shorter proof uses the normalization field
already required by this item's statement. No mathematical statement was changed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
