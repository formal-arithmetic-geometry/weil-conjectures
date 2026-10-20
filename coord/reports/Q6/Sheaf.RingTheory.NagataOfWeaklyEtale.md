## What changed

Repaired the returned delivery by starting from the current shared version of
`Sheaf.RingTheory.NagataOfWeaklyEtale` and reapplying the retained complete
finite-normalization proof of `RingHom.isNagataRing_of_weaklyEtale`.
The existing header, docstrings, public imports, universes and theorem signature
are unchanged. All helpers are private and proved.

The proof imports the current upstream modules
`WeilConjectures.RingTheory.NormalOfFlatNormalFibers` and
`WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`.
The retired Sheaf normality import is removed. The upstream normality import
also exposes `RingHom.IsIntegral`, so the helper's element-integrality type is
qualified as `_root_.IsIntegral` to preserve its intended meaning.

The proof constructs its normalization and image subalgebra explicitly, and
constructs the finite field model by intermediate-field adjoin. It handles the
N-2 universe restriction by shrinking a finite-dimensional extension. Local
algebra, module and scalar-action projections are cached to avoid repeated
inference. The existing DAG node is refreshed from the current repository and
only its proof-route fields and obsolete tool approvals are changed.

The change record is
`coord/changes/q6-nagata-weakly-etale-proof-notation.md`.
The direct consumer is
`Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale`; its theorem application
has the same type and requires no adaptation.

## Proved and sorry left

Closed one original hole: `RingHom.isNagataRing_of_weaklyEtale`
(node `lem-exc-nagata-weakly-etale-ascent`). Added zero holes; split off zero
statements. The delivered module has zero remaining `sorry` declarations.

## No longer needed

Removed direct imports:
- `WeilConjectures.RingTheory.JapaneseDomain` (already public through NagataRing).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (available through the required API).
- `WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`.
- `Mathlib.RingTheory.Localization.Integral` (available through IntegrallyClosed).
- `Mathlib.RingTheory.KrullDimension.Zero` (absolute-flatness API suffices).
- `Mathlib.RingTheory.Spectrum.Maximal.Localization` (local reducedness API suffices).
- `Sheaf.RingTheory.WeaklyEtaleField` (use proved absolute-flatness and polynomial APIs).
- `Mathlib.CategoryTheory.MorphismProperty.Composition`.
- `Mathlib.CategoryTheory.MorphismProperty.Limits`.
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`.
- `Mathlib.RingTheory.Localization.Submodule` (the proof does not need localization
  Noetherianity; the prime extension-contraction API comes from `Localization.Ideal`).

The following former proof-dependency nodes are unnecessary for this proof:
`lem-weil-pbc-affine-chart-base-change-iso` and
`lem-weil-pbc-weakly-etale-composition-base-change`: ring-level weak-etale base change
already gives the required tensor-product instances;
`lem-weil-pbc-weak-etale-field`: proved source-library absolute flatness and the
polynomial nonunit criterion give precisely the needed field assertions in arbitrary universes;
`lem-weil-pbc-minimal-prime-reduced-localization-field`: prime localizations of an absolutely
flat ring are already fields;
`lem-weil-pbc-localization-noetherian`: no separate Noetherianity of fibres is needed;
`lem-weil-pbc-prime-localizations-jointly-injective`: use Mathlib's local reducedness theorem;
`lem-weil-pbc-finite-algebra-is-integral`: inject the integral closure into the finite normal
model and use Noetherian submodule finiteness instead of proving equality of the two rings.
Removed the obsolete top-level tool approvals for the field and affine comparison nodes.
These are local dependency removals, not a claim that other parents no longer use the nodes.

## Where the brief, the DAG or earlier work was wrong

The returned packet was based on an earlier version of the item. This repair
uses the current shared file, including its upstream Nagata public import,
and retains the complete original theorem docstring. The retained sandbox
also referred to the now-retired Sheaf normality module. Updating that proof
import required qualifying the element-integrality predicate to avoid a name
collision with `RingHom.IsIntegral`.

The repaired module compiled cleanly through `lcompile.py` in 17.3 seconds.
The unmodified direct consumer
`Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale` also compiled against the
repaired module through `lcompile.py --all`: 43.9 seconds for the dependency and
15.5 seconds for the consumer.
Profiling identified repeated inference through the constructed field and image
algebra structures. Additional local caches for their ring, module and scalar
action projections avoid that cost; no file was split and no limit was raised.

No mathematical statement or definition is changed. The unit record has no
realized statement or step at this node, and the finite-normalization route
is preserved. The ring-level weak-etale APIs give base change, absolutely flat
fibres, and algebraic residue images without the former scheme comparison
and same-universe field statements. No source-library file is modified.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
