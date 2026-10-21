## What changed

Closed `WeilConjectures.isIso_of_surjective_etale_pullback` in
`Sheaf.Paper.EtaleIsoDescent`, preserving its signature and all public imports.
Added the private proof import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative`.
The proof constructs the singleton etale cover, applies the existing source
localization comparison and cover conservativity, transports through the canonical
coefficient equivalences, and uses exact derived cohomology and the full inclusion.
Updated the existing node's proof, dependencies and origin to match these steps.
No definitions, source-library files, target signatures or unit routes change.

Validation: the module compiled through `lcompile.py` in 10.8 seconds with no
diagnostics. The delivery tool performs the final compile and axiom probe.

## Proved and sorry left

Closed: `WeilConjectures.isIso_of_surjective_etale_pullback`
(blueprint `lem-pur-etale-iso-descent`), the sole original hole: 1 of 1 proved.
Added: zero holes. Left in this delivery: zero holes. No statements split off.
The proof uses the existing library interfaces as authorized by the stage brief;
this is a complete Lean proof, not a relocation of the original hole.

## No longer needed

Removed private proof imports:

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

Removed planned proof dependencies:

- `det-pe-morphisms-etale-comparison`
- `lem-weil-pbc-flat-lfp-open`
- `lem-weil-pbc-affine-scheme-qcqs`
- `def-weil-proetale-inverse-image`
- `def-pur-localized-ringed-site`
- `lem-pur-site-restriction-module-adjunction-exact`

Mathlib's etale-to-pro-etale covering inclusion incorporates the old openness and
finite affine refinement construction. The source upperStar/restriction comparison
incorporates the explicit comma-category graph calculation. Exactness is already
an instance for the defined intrinsic pullback, so no separate localized-system
exactness interface is needed. The source covering conservativity theorem supplies
the old sectionwise gluing step. These dependencies are unnecessary for this proof;
no claim is made that their modules are globally unused or may be withdrawn.
Removed the obsolete top-level tool approvals for
`det-pe-morphisms-etale-comparison` and
`lem-pur-site-restriction-module-adjunction-exact`; retained the localization tool.
All public imports remain intact.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is mathematically adequate, but its imports and handwritten
construction steps duplicate proved source-library APIs. The shorter proof follows
the same covering and cohomology route and avoids using geometric stalks to detect
arbitrary pro-etale sheaves. Empty source/target schemes cause no exception: the
singleton-cover and sheaf criterion handle them. No new mathematical statements or
hypotheses were introduced. No current rework row or return exists for this item.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
