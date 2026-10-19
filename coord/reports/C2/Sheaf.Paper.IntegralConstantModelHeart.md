## What changed

Proved `AlgebraicGeometry.ProEtale.integralConstantModelHeart` in
`lean/Sheaf/Paper/IntegralConstantModelHeart.lean`, preserving its statement and the
coefficient-ring definition. The proof transports the existing
`isConstantModelConstructible_serre_padicIntegers` theorem to the arbitrary-universe
coefficient extension through `Shrink` and a condensed ring isomorphism. Private,
fully proved helpers establish transport of finite presentations, local models and
stratifications, zero and isomorphism closure, triangulation, truncations, the
single-functor essential image, abelianness and essential smallness.

Added the proved theorem `AlgebraicGeometry.ProEtale.integralCoefficientRingComparison`
in `lean/Sheaf/Paper/IntegralCoefficientRingComparison.lean`. An algebra embedding
into the fixed algebraic closure has finite field range. Uniqueness of the extending
p-adic norm makes the field equivalence isometric. Its restriction to the two rings
of integers is a continuous ring equivalence, whose sectionwise postcomposition
maps give inverse morphisms of condensed ring objects. No data definition chooses
from a new unproved existence assertion.

The item node now records this route. The unit statement is unchanged; the existing
heart-closure theorem carries the adic local-model argument, while the proved
homology-property API supplies the formal derived-category consequences. The
unit's realized arrays contain no separate required declarations to bypass.

On resumption, checked the retained proof against the current source interfaces.
The required dry run compiled both delivered modules and passed preflight as CODEX.
The downstream query confirms `IntegralConstructibleHeart` is the only direct
consumer; its probe is identical to the current source. The import-direction check
confirms that the heart-closure dependency does not reach this item.

## Proved and sorry left

Original holes: 1. Closed `AlgebraicGeometry.ProEtale.integralConstantModelHeart`
(node `det-lem-int-integral-heart-triangulated`) from existing stated dependencies.
Added holes: 0. Split off: 0. There is no `sorry` in either delivered Lean module.
The new `AlgebraicGeometry.ProEtale.integralCoefficientRingComparison` is proved.
This is a proof from the library's named dependencies, not a claim that their
transitive axioms have all been discharged. The existing
`isConstantModelConstructible_serre_padicIntegers` is now proved in current sources.
`HasFiniteConstantLocalModel.isLocallyFinitelyPresented` remains a named imported
dependency; its remaining obligations are outside this delivery.

The finite field case, zero finite presentation (ranks zero), zero objects, empty
scheme, identity coefficient isomorphism, arbitrary cohomological degrees and
arbitrary coefficient universes are covered by the construction and generic APIs.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.DerivedNakayamaFirstReduction`

The proof does not need these former direct proof dependencies:

- `lem-weil-l-adic-extension-integers-dvr`
- `sk-lem-integral-models`
- `det-pe-derived-nakayama-first-reduction`
- `lem-pur-derived-change-of-rings`
- `lem-weil-proetale-dbc-triangulated`
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
- `det-lem-int-integral-heart-local-model`
- `lem-sf-derived-homology-long-exact`
- `def-weil-abstract-derived-category`
- `lem-weil-pbc-complex-ses-triangle`
- `def-weil-size-convention`
- `def-weil-pbc-proetale-site`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-sheaf-of-modules-category`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-noetherian-stratum-detection`

The residue-completeness and finite-coefficient triangulation argument is already
encapsulated in the existing constant-model heart-closure theorem. Standard
truncation closure follows directly from cohomology, and the general proved
constructible-module smallness theorem replaces a second local-data counting proof.
The removed dependencies may remain needed transitively or elsewhere; no global
unreachability or module deletion is asserted.

Pruned obsolete `tool_uses` approvals:

- `lem-weil-l-adic-extension-integers-dvr`
- `det-pe-derived-nakayama-first-reduction`
- `lem-pur-derived-change-of-rings`
- `lem-weil-proetale-dbc-triangulated`
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-complex-ses-triangle`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-noetherian-stratum-detection`

Retained the concentration and single-functor full-faithfulness approvals. The DVR
membership theorem is used in the new coefficient-comparison node, rather than as
a direct step of the main node.

## Where the brief, the DAG or earlier work was wrong

The main theorem need not rebuild weak Serre closure and smallness from the nine-step
plan: existing declarations supply both, and the source library already proves the
generic homology-property triangulation and truncation API. The distinction between
constant scalar models and arbitrary local finite presentations is preserved: only
the forward implication is used for essential smallness.

The resumed compile exposed invalid zero-object scope spelling, a reversed product
isomorphism, an underconstrained scalar-restriction functor and a missing explicit
Noetherian constructor. These have been repaired without changing any public signature.

Earlier sandbox drafts contained an unused Serre split. It was never delivered and
has been removed. No existing library statement or definition was changed, and no
other group's module was adapted.

## New nodes

`lem-int-integral-coefficient-ring-comparison` records the proved coefficient
comparison theorem. Its source is Mathlib's `spectralNorm_unique_field_norm_ext`
and the continuous-function condensed ring construction. LeanSearch, LeanFinder,
Loogle and grep found norm uniqueness and algebraic-closure tools but no bundled
isomorphism for these two recorded coefficient conventions. The proof constructs
that isomorphism explicitly. The proof-context record is
`coord/changes/C2-integral-constant-model-heart-proof-context.md`; all existing public
signatures and definitions are preserved.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
