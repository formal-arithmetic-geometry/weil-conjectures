## What changed

Proved all three theorems of `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible`,
without changing their statements, visibility, attributes, or public imports. Reordered
those declarations so the main theorem uses the two witness-preservation theorems.
All new helpers are private and proved in this module; no dependency source is changed.

The pullback comparison is the existing `proEtaleRingRestrictionPullbackApp`, specialized
to the canonical constant-ring comparisons. Naturality of those comparisons is proved
from the constant-sheafification unit and the inverse-image counit. A generic private
lemma proves that scalar restriction commutes with simultaneous ring/module
sheafification: the universal lift becomes the identity on the underlying abelian
sheafification. Applying it on localized sites retains the given trivializations.
The stalk proof uses the definitionally unchanged underlying additive colimit carrier.
The main theorem uses the existing exact restriction API and
`Functor.mapDerivedCategoryHomologyFunctorIso`, then proves zero reflection by
faithfulness and transports the original t-structure bounds degree by degree.

Added proof imports of `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` (for
`constantComparison_isIso`) and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (for the natural
homology comparison). The latter comparison is used with its inverse for the displayed
statement. The DAG proof and proof dependencies now describe the implemented argument. The conservative
scope-command check is documented in
`coord/changes/T6-finite-scalar-restriction-private-scopes.md`; downstream analysis
reports zero consumer modules, and no public signature or import changes.

Validation: the complete final Lean module compiled cleanly through `lcompile.py` in
46.0 seconds, with no warnings. New helper statements allow arbitrary coefficient maps;
none require surjectivity, nonzero rings, or nonempty schemes. Covers and the positive
number of strata are copied from the original witnesses. Empty schemes, zero
coefficients, identity maps, and nonsurjective finite-ring maps require no extra cases.

## Proved and sorry left

Closed all 3 original holes:

- `AlgebraicGeometry.Scheme.proEtaleFiniteScalarRestriction_constructible`.
- `AlgebraicGeometry.Scheme.proEtaleFiniteScalarRestriction_sameTrivializations`.
- `AlgebraicGeometry.Scheme.proEtaleFiniteScalarRestriction_sameStratification`.

All three belong to `lem-pe-finite-scalar-restriction-constructible`.
Zero holes remain in the item; zero holes were added; zero results were split off.
This is a proof delivery, not a decomposition.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`: the proof uses the original
  intrinsic local-model definitions already imported by the constructibility interface.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: the canonical constant-sheaf
  comparison is already proved for arbitrary rings by `constantComparison_isIso`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the existing derived
  homology comparison supplies the required natural isomorphism directly.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: the existing
  scalar-restriction API supplies exactness; no separate kernel/cokernel calculation
  is repeated here.

Removed the node's direct proof dependencies and obsolete tool-use entries for
`lem-weil-pbc-module-sheaves-colimits-forgetful` and
`prop-weil-pbc-proetale-constant-ring-map`, for those same reasons. Their declarations
and modules remain untouched; this does not claim they disappear from the whole
library's transitive import closure. All other declared dependencies remain used.
No unit statement or unit proof step is bypassed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan's finite-generation calculation is unnecessary for the actual intrinsic
statement: `IsConstructibleProEtaleModuleSheaf` already assumes finite underlying
stalk sets. Restriction preserves that carrier definitionally, and pullback comparison
transports finiteness by an actual stalk isomorphism.

The existing `Functor.mapDerivedCategoryHomologyFunctorIso` is oriented from
`H^q ⋙ Res` to `D(Res) ⋙ H^q`; the requested statement uses its inverse.
The original proof route is mathematically sound; no statement or definition repair
was needed. The new proof dependencies
`lem-pur-proetale-constant-coefficient-comparison` and
`lem-weil-pbc-ring-sheaf-change-adjunction` are general categorical tools for the
same inverse-image step, not replacements for an integral-criterion unit step.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
