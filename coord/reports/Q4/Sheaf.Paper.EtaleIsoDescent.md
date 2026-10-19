## What changed

Proved `WeilConjectures.isIso_of_surjective_etale_pullback` in
`Sheaf.Paper.EtaleIsoDescent`, with its statement, universes, visibility, and public imports
unchanged. The proved private helper `fixedPullback_reflectsIsomorphisms` turns the singleton
surjective étale family into a pro-étale cover, identifies inverse image with localization
restriction, and applies the existing source sheaf conservativity theorem. Reflection then
transports through the two canonical module realization equivalences. The exact-derived
cohomology comparison reflects each cohomology map, and `DerivedCategory.isIso_iff` and the
full-subcategory inclusion finish the argument.

The DAG proof now records this implementation. The auxiliary lemma does not realize any
unit statement or step; the cohomology and local-to-global route of sk-prop-cohsm is preserved.
No new modules, definitions, signatures, or nodes were needed. The existing localization
node remains a tool for identifying actual pullback with restriction.

Validation: the complete proof compiled through lcompile.py (exit 0). Delivery preflight
also checks the final module and its axiom dependencies. The helper works for arbitrary
commutative coefficients at the fixed-scalar level, including zero rings and empty schemes;
only the existing finite coefficient realization needs finiteness. No choice of geometric
points, nonempty scheme, or étale-origin assumption enters the proof.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.isIso_of_surjective_etale_pullback`
(node `lem-pur-etale-iso-descent`).

Also proved the private helper `WeilConjectures.fixedPullback_reflectsIsomorphisms`.
There are zero remaining holes in the item and zero added holes. Nothing was split off.
Existing dependency holes, if any, are unchanged.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

Added only the proof import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative`.
The direct `Open.Defs` import tried during development is redundant with the existing public
import closure and is omitted. The HomologySequence import remains.

The following old direct proof dependencies are unnecessary for this implementation:
`det-pe-morphisms-etale-comparison`, `def-weil-etale-morphism`,
`lem-weil-pbc-flat-lfp-open`, `lem-weil-pbc-affine-scheme-qcqs`, and
`def-weil-pbc-proetale-site`: Mathlib's existing étale-to-pro-étale precoverage inclusion
(node `lem-pur-etale-proetale-cover`) supplies singleton covering membership.
`def-weil-proetale-inverse-image`, `def-pur-localized-ringed-site`, and
`lem-pur-site-restriction-module-adjunction-exact` are unnecessary as separate proof inputs:
the published fixed-scalar localization isomorphism and the exact canonical intrinsic
pullback already supply the interfaces. `lem-weil-pbc-exact-functor-complex-cohomology` is
replaced by the already proved derived natural comparison
`lem-weil-pbc-exact-functor-bounded-below`, which includes naturality on derived morphisms.
The obsolete top-level tool approvals for `det-pe-morphisms-etale-comparison` and
`lem-pur-site-restriction-module-adjunction-exact` are withdrawn.

These are removals from this proof, not assertions that these modules are globally
unreachable: public statement imports and other consumers may still reach them.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original graph/affine-refinement and
section-gluing plan is already implemented by existing Mathlib and source-library APIs;
repeating those constructions is unnecessary. The original proof's complex-level comparison
has an existing derived natural version, which is the interface used here. The theorem
statement and its original source docstring remain unchanged.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
