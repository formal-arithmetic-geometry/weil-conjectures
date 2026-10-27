## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.proper_open_boundary_zero` from the
existing complement-square and open-extension theorems and the finite and integral
proper-base-change declarations, and the adopted rational proper-base-change
theorems in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`. The proof applies base change to
`K = j_! A`, substitutes its zero restriction to the inverse-image complement,
and uses preservation of zero objects by the right derived pushforward.

Validation: the full proof compiled in 41.6 seconds; final import cleanup is
checked again by the delivery preflight. The public definition and theorem
signature were compared verbatim against the repository.

Added proved private helpers for transport along condensed ring isomorphisms,
finite discrete coefficient realization, ground-field realization in the fixed
algebraic closure, and the integral coefficient universe lift. These helpers
construct the ring isomorphisms; none chooses an unspecified ring model from a
mere existence statement. The norm and integral-ring helpers reproduce the
proved constructions used in `NormedCoefficientRealization`,
`ProperProjectionFormulaBounded`, and `IntegralCoefficientExtComparison`, whose
helpers are private. No existing public signature, definition body, or public import was
changed. Updated the existing node's proof dependencies to record this glue.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_boundary_zero`.
Zero holes added; zero holes remain in the delivered Lean module. This is a proof
from existing stated dependencies, including the proper-base-change theorems;
it does not claim those dependencies are axiom-free yet. No split-off statements. The rational restricted exchange component is carried to the ambient category
by the full-subcategory inclusion functor.

## No longer needed

Removed these direct proof imports, using the two existing higher-level
complement-square and open-extension declarations instead:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`
- `Sheaf.Paper.OpenExtensionConstantModelConstructible`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.SixFunctors.OpenImmersionTensorProjection`
- `Sheaf.Paper.CartesianCoefficients`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `Sheaf.Paper.ProperBaseChangeRational`

Six of the seven declared proof dependencies of the current five-step DAG plan
remain used. `det-thm-sfb-proper-base-change-rational` is replaced by the already
proved adopted declarations `nt-target-proetale-e` and `nt-target-proetale-qbar`.
They supply the same finite-field and finite-subextension-algebraic-closure
exchange isomorphisms via the source library's named finiteness-coefficient
interface. This avoids the expensive expansion of the conditional preservation
proof in the newer rational interface. The lower-level geometry and extension results remain dependencies of the
two higher-level declarations; no module is withdrawn and no global pruning is
claimed. Removed stale top-level `tool_uses` entries for the lower-level direct
route; retained the finite and integral proper-base-change entries and removed the
rational one because that declaration is no longer used.

## Where the brief, the DAG or earlier work was wrong

The current DAG has five proof steps, while the original theorem docstring still
expands their older six-step version. The mathematical route agrees. The
coefficient-specific declarations use different ring presentations and universe
levels, so applying them requires explicit transport, rather than a direct
`exact` in each admissible case. The finite case uses the constant sheafification
comparison; the integral case uses the spectral-norm description of the unit
ball and its canonical universe lift. The source-library rational proper-base-change route compiles without changing
any adopted declaration or import. The reducedness assumption on the target
complement is preserved, although the base-changed complement need not be
reduced.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
