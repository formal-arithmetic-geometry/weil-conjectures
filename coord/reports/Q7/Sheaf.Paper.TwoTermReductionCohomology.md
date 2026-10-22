## What changed

Filled `AlgebraicGeometry.ProEtale.TwoTermReduction.two_term_reduction_cohomology`
in `Sheaf.Paper.TwoTermReductionCohomology` using proved private helpers. Every
existing public definition, structure, field and theorem signature stays unchanged.
The proof constructs both normalized cohomology isomorphisms from kernel and
cokernel universal properties, computes the actual derived adjunction transition,
and constructs the tensor action isomorphism from the ordinary adjunction counit.
The endpoint case n = 0 is included in all coefficient calculations.
The transition proof retains the homotopy-category comparison maps and uses their
naturality before applying the explicit chain calculation.
Local opacity boundaries are placed after the concrete section formulas, so later
exactness and transition proofs use the established interfaces without expanding
the coefficient functor and the constructed isomorphisms.

The actual coefficient maps are retained: the inclusion is multiplication by the
specified prime power before continuous-function pullback, and the cokernel map
is the specified residue map. Exact internal-module pullback and the section-module
equivalence transport their elementary exactness. Constant sections are used only
for identifying the residue sheaf and detecting its nonvanishing.

Updated `lem-pe-two-term-reduction-cohomology`'s proof, proof dependencies and
proof origin to match this route. Added only private proof imports and helpers;
there are no consumer adaptations or changes to the adopted source library.
The proof-context record is
`coord/changes/Q7-two-term-reduction-proof-context.md`. All four helper interfaces
are proved private theorems registered only as local instances.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.TwoTermReduction.two_term_reduction_cohomology`
(node `lem-pe-two-term-reduction-cohomology`). Holes closed: 1; holes added: 0.
No `sorry` remains in the item and no new modules or split statements are added.
The imported declarations retain their existing proof status.

Validation: the complete item module compiled through the prescribed `lcompile.py`
in 54.9 seconds with no warnings. All existing public definition bodies and the
target signature were compared with the shared source and are unchanged.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlatScalarTowerRealization`
- `Sheaf.Paper.CondensedPointCoefficients`
- `Sheaf.Paper.CondensedPointDiscreteConstantComparison`
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`
- `Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero`
- `Sheaf.CategoryTheory.SiteConstantModuleUnit`

The proof no longer uses these old proof-dependency nodes:

- `def-pc-flat-sheaf-modules`: flatness is expressed by the existing site-flatness API.
- `lem-pe-kflat-scalar-tower-realization`: the mate is computed directly from the
  recorded representative and adjunction-normalization equations.
- `lem-pe-condensed-point-discrete-constant-comparisons`,
  `sk-def-sfb-pulled-back-coefficients`, and `det-pe-condensed-point-coefficients`:
  coefficient maps are calculated directly on continuous functions; the residue
  comparison uses locally bijective constant functions and `constantSchemeIso`.
- `lem-weil-pbc-site-module-presheaf-sheafification-exact` and
  `lem-cbc-constant-ring-module-sheaves`: exact internal-module pullback followed
  by the section-module equivalence transports the kernel and cokernel sequences.
- `lem-sfb-constant-realization-detects-zero`: constant-section injectivity on the
  nonempty identity object proves nonvanishing directly.
- `lem-sf-constant-module-unit-locally-bijective`: locally surjective coefficient
  maps make scalar restriction fully faithful, so the adjunction counit supplies
  the tensor isomorphism.

Statement dependencies are retained, including the discrete comparison cited by
the node's statement. These are unused proof inputs for this item, not requests to
withdraw those modules or any source-library declarations. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No public statement was found false. The planned constant-module equivalence and
simultaneous scalar-tower theorem are unnecessary for this proof. Exact pullback
of continuous internal modules proves the literal coefficient calculation, the
normalization hypotheses determine the actual derived mate, and the counit for
fully faithful restriction gives the required tensor action. These substitutions
preserve the unit route and all specified inclusion, residue, transition and pure
tensor formulas. The original theorem docstring describes the older plan; the
updated node records the implemented proof.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
