## What changed

Proved `AlgebraicGeometry.ProEtale.finite_coefficient_derived_model_comparison` in
`Sheaf.Paper.FiniteCoefficientDerivedModelComparison`, with the statement, universes,
public imports, and existing docstrings unchanged. The specified equalities determine
`b` and `beta`; their witnesses and normalization proofs are supplied directly.
For `gamma`, compose the derived composition comparison, the comparison functor's
localization factor, and the localized natural constant-complex comparison, whiskered
by coefficient realization. Component equations for whiskering and functoriality,
followed by reflexivity, prove exactly the required component formula.

The canonical fixed-ring comparison and constant-sheaf constructions already exist in
the adopted source library. Exactness is already supplied by the published functor
instances; no new geometric-morphism lift is required. Updated the item's DAG proof,
proof dependencies, and proof origin accordingly. No definitions, interfaces, or
other modules changed. Explicit local functor types avoid expensive inference.

Validation: the complete proof compiled through `lcompile.py` in 33.7 seconds. The
only diagnostics were three line-length warnings, subsequently fixed by wrapping
those lines; final clean compilation is checked by `deliver3.py`. Searched using
LeanFinder, Loogle, the logged grep service, and repository `rg`; Loogle found the
existing `mapHomologicalComplexCompIso`, and source inspection supplied the exact
canonical comparisons and derived-functor API. No additional mathematical lemma was
needed. The construction works for the zero ring, empty schemes, zero complexes,
infinite modules, and unbounded complexes because it composes existing natural
isomorphisms without imposing any additional hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finite_coefficient_derived_model_comparison`
(node `lem-weil-pbc-finite-coefficient-derived-model-comparison`).

Holes added: 0. Split off: 0. Sorries left in the delivered module: 0.
This is a proof from the existing library API, not a decomposition.

## No longer needed

Removed the following private proof imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.ExactDerivedComposition`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`

The canonical pullback and constant comparisons already come from the retained public
source-library import. The derived composition and natural-isomorphism constructions
come from the retained public exact-functor import. In particular, the separate
uniqueness theorem in `ExactDerivedComposition` is not needed for these witnesses.
The general ringed-module constant comparison need not be converted to the published
fixed-ring presentation: `comparisonUpperStarConstantSheafIso` already constructs
precisely the comparison appearing in the statement.

Removed these direct proof dependencies from the item's DAG node:
`lem-pe-constant-left-module-inverse-image`,
`lem-weil-pbc-etale-base-change-continuous`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, and
`def-weil-pbc-inverse-image`. The existing exact functor instances supply their role
in the original exactness step. Retained the mathematical comparison, constant-module,
exact-factorization, derived natural-isomorphism, and derived composition nodes;
the Lean proof uses their published specialized constructions directly.

No module or declaration is withdrawn. These are imports and direct DAG edges no
longer needed by this proof; no claim is made that the five modules are globally
unreachable. The blueprint unit statement and its realized proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original plan requested generic
geometric-morphism exactness and ringed-module constant-comparison machinery even
though the statement already uses the published exact fixed-ring functors and their
canonical comparisons. Reusing those constructions makes that extra interface work
unnecessary. Initial underspecified witness terms caused expensive elaboration;
using the normalization equalities to choose the first two witnesses and specifying
local functor types removes that inference problem without changing any definition
or increasing a compile limit.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
