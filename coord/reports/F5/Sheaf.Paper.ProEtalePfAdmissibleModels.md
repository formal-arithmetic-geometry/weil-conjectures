## What changed

Proved `AlgebraicGeometry.ProEtale.proEtale_pf_admissible_models` in
`Sheaf.Paper.ProEtalePfAdmissibleModels`, with its existing statement and definitions
unchanged. Four proved private argument helpers supply bounded fixed-module origins, Tor
reflection for each specified witness, the generic tensor calculation, and the complete
model construction. Proved private helpers also supply the existing sheaf weak-equivalence monoidality
instances at high priority, as in the neighboring bounded-tensor module.

The proof descends intrinsically constructible cohomology in fixed-module coordinates,
uses bounded derived descent, and transports Tor bounds through the actual witness
isomorphisms. Mathlib supplies the bounded representative of K0. The source library
supplies the bounded flat representative of L0, geometric inverse-image flatness,
exact-functor localization, and the right-factor K-flat tensor computation. The strict
support bounds on the signed tensor give the asserted lower bounds. Properness supplies
quasi-compactness and quasi-separatedness.

Replaced the private proof imports and updated the node's proof, proof dependencies and
proof origin. Removed obsolete top-level tool approvals without adding or reordering any.
No public signature, definition, public import, source-library file, or consumer changed.
The existing unit route still uses this node as its admissible-input step. The construction
works for zero objects, empty schemes, the zero coefficient ring, and singleton intervals;
no step uses nonzero coefficients, local freeness, or flatness of the scheme morphism.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.proEtale_pf_admissible_models`
(node `lem-sf-proetale-pf-admissible-models`).

Original holes: 1. Proved: 1. Holes added: 0. Split off: 0. Remaining holes in delivered
Lean files: 0. The private helpers `boundedOrigin`, `originTor` and `admissibleModels`
`tensorModel`, `coefficientSheafWIsMonoidal`, and
`proEtaleCoefficientSheafWIsMonoidal` are all proved. Imported declarations retain their
existing obligations; this report claims closure of the item's hole, not axiom-freeness of its entire dependency closure.

## No longer needed

Removed all eleven former private proof imports:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Algebra.Homology.RingedSiteTorFlatModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`

Removed former proof dependencies:

- `lem-sf-proetale-constructible-origin`: use its existing fixed-module sheaf and bounded
  derived descent components directly, avoiding intrinsic coefficient-realization bridges.
- `def-kun-truncations`: use the precise existing Mathlib bounded-representative theorem.
- `lem-sp-ringed-site-tor-flat-model`, `lem-weil-pbc-site-derived-tensor-descent`,
  `lem-pc-kflat-resolution`, `lem-pur-kflat-tensor-quasiiso-independent`: the existing
  generic source flat-model theorem and one-factor tensor isomorphism already work with
  the published derived tensor in the required ordinary module-sheaf category.
- `lem-weil-pbc-independent-bounded-flat-kflat`: use the existing generic categorical
  bounded-above flat criterion in the actual fixed-module presentation.
- `lem-weil-pbc-ringed-pullback-preserves-kflat` and
  `lem-weil-pbc-ringed-topoi-derived-pullback`: geometric stalks preserve termwise
  flatness; bounded support gives K-flatness, and exact localization identifies pullback.
- `def-weil-pbc-extension-by-zero`: its construction remains in the public interface;
  the proof uses its exactness node and exact localization directly.
- `def-weil-finite-type-morphism`: properness already supplies the requested qcqs instances.
- `prop-weil-pbc-comparison-direct-image`: admissibility is its input condition, so proving
  the condition does not require the direct-image comparison theorem.

The eight obsolete top-level `tool_uses` removed are
`lem-sf-proetale-constructible-origin`, `lem-sp-ringed-site-tor-flat-model`,
`lem-weil-pbc-independent-bounded-flat-kflat`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-ringed-topoi-derived-pullback`, `prop-weil-pbc-comparison-direct-image`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-pur-kflat-tensor-quasiiso-independent`.

These are dependencies this argument no longer needs. No module is withdrawn, and no
claim is made that another library consumer has stopped needing any of them.

## Where the brief, the DAG or earlier work was wrong

The previous plan was mathematically valid but unnecessarily changed coefficient
presentations. Its ringed-site flat-model application required a separate derived-tensor
comparison, whereas the existing source flat-model theorem uses exactly the tensor in
the item's Tor test. The fixed-coefficient Tor predicate already contains categorical
Tor amplitude, and the source `torAmplitudeIn_mapDerivedCategory_iff` is the appropriate
fixed-coordinate form of the Tor-comparison node. The general ringed pullback theorem
is also unnecessary for a bounded flat complex under constant-coefficient geometric
inverse image. Finally, no direct-image comparison is asserted by this theorem: the
bounds and properness conditions suffice. These shorter applications preserve the
unit's finite-coefficient admissible-model step. No statement repair was needed.

During development, profiling identified costly unfolding of the categorical Tor predicate
and typeclass searches for the concrete tensor structures. The Tor argument keeps the
predicate folded and applies the published comparison equivalences directly. Model
construction uses explicit cochain-complex types and the bounded-flat K-flatness criterion.
The signed tensor calculation is proved generically in the same module and then applied
to the concrete sheaf category, avoiding repeated expansion of its tensor construction.
The complete delivery module compiles cleanly with `lcompile.py` in 46.1 seconds
(result `95ad67a3f37a8be751b7a926`). All development profiler commands and scratch
experiments are excluded from the delivery. There is no compile-limit increase, public
interface change, or postponed proof.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
