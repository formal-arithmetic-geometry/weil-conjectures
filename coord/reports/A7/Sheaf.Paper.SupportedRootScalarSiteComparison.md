## What changed

Replaced the hole in `AlgebraicGeometry.SupportedRootScalar.supported_root_scalar_site_comparison`
by an adjunction argument from a separate coefficient-Hom naturality lemma. The original
theorem signature is unchanged. The proof constructs the source comparison from its
canonical arrow, proves its adjunct equation, proves scalar-arrow naturality, obtains the
unique coefficient image using the supported-Hom equivalence, and derives the final site
formula. The local root tensor formula follows from linearity.

The new proved `rootScalarEndpointData` uses the existing finite Kummer scalar endpoint
existence theorem and computes the shifted adjunct with the canonical shift comparison.
Its hypothesis is that T is a k-scheme; the assigned theorem already has this hypothesis.
The existing endpoint-existence module needed a private proof import and explicit wrapper
unfolding to compile. Its signatures and data definitions are unchanged.

Moved the generic support-Hom and coefficient-map definitions to the new module
`Sheaf.Paper.SupportedCoefficientHomNaturality`; the item publicly imports it, keeping the
same public names and types. The two degree-zero source presentations are related by
`homPresentation`; `realizationEquiv` packages its equality cast with the existing
identification.
The standalone source transports retain their original equality-transport formulas.
The new theorem expresses evaluation-at-one compatibility
with restriction of scalars and site change independently of all root endpoints.

Change records:
`coord/changes/A7-supported-coefficient-hom-interface.md` and
`coord/changes/A7-p1-endpoint-adjoint-proof-import.md`.

## Proved and sorry left

Original holes: 1. Closed:
`AlgebraicGeometry.SupportedRootScalar.supported_root_scalar_site_comparison`.

Added holes: 1, in
`AlgebraicGeometry.SupportedRootScalar.supportedCoefficientHomNaturality`
(node `lem-pur-supported-coefficient-hom-naturality`). Its proof is exactly `by sorry` in
its own module, with the source and full resolution/evaluation argument in its docstring.
This is a decomposition, net zero holes, not a claim of a net proof closure.

The new `AlgebraicGeometry.SupportedRootScalar.rootScalarEndpointData` is proved.
The endpoint-existence adaptation adds no holes and retains its complete existing proof.
No definitions contain holes. Empty support, empty schemes, zero coefficient rings and
non-flat coefficient maps are included: the remaining coefficient theorem asserts
comparison through acyclic resolutions, not preservation of injectives by restriction.

## No longer needed

Removed these private proof imports from the item:
`Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`,
`Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`,
`Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`,
`Sheaf.CategoryTheory.ModuleRestrictionKernelComparison`,
`Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`,
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, and
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`.

The root scalar endpoint is obtained directly from
`lem-sp-p1-kummer-scalar-endpoint-existence`. Thus the item does not directly use
`lem-pur-derived-change-of-rings`, `lem-pur-etale-closed-constant-tensor`,
`lem-pur-etale-supported-kernel-adjunction`, or
`lem-weil-pbc-independent-bounded-flat-kflat`.
The local tensor formula is proved from the actual generator and linearity, without
`lem-amb-finite-root-site-comparison` as a proof dependency.

The normalization, relative-cone, restriction-kernel and K-injective nodes of the original
plan remain needed by the new coefficient naturality lemma. They are not globally pruned.
No module is withdrawn, and the unit's realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing P1 endpoint-existence proof could not resolve its scalar adjoint helper in
the current compiled overlay. Its direct private import and wrapper unfolding repair are
recorded above. The published root endpoint result makes a separate new root-construction
hole unnecessary. The original seven-step argument otherwise remains valid; its coefficient
naturality step required a separate generic statement in the ordinary coefficient-sheaf
interfaces. The new lemma does not assume that restricted injectives remain injective.

## New nodes

`lem-pur-supported-coefficient-hom-naturality` records the retained coefficient and site
naturality result over an arbitrary finite coefficient ring, independent of root data.
It is the one remaining hole.

`lem-pur-supported-root-scalar-endpoints` records the proved normalized residue root
endpoint and its shifted adjunction computation. Both nodes keep the item's chapter and
unit. The item's proof and proof dependencies now describe the actual Lean combination.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
