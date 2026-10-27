## What changed

Restored `Sheaf.Paper.FiniteComparisonPresentation` from its recorded quarantine
archive. The assigned repair has zero holes. The private `proSites_monoidal`
helper fixes `EssentiallySmall.{u + 1} X.ProEt` explicitly using
`essentiallySmallSelf.{0}`. A private local instance `presentationSiteSmall`
supplies that same canonical size throughout the private proofs, with priority above imported maximum-universe
size instances. It is enabled explicitly only for the final presentation theorem
after the private section ends. The imported `scalarReductionSiteSmall` otherwise
leaves a coefficient universe beneath `max` undetermined. The archive's seven
integral-operations and completed-coefficient exclusions are unchanged.

The integral-operations import is retained for compatibility: two existing
import-all consumers refer to its instance names in their own exclusion lists.
Every original declaration of those consumers remains available. No other
existing module is changed.

The completed general helper proofs move to
`Sheaf.Paper.FiniteComparisonPresentationSupport` inside a namespace. Its
section-monoidal existence theorem is public and proved; the other helpers are
private. Five private entry points used by existing import-all consumers retain
their original signatures in the item: `sectionMonoidal_exists`, `localFinite`,
`localFinite_iso`, `finiteModelSieve`, and `localFinite_iff_sieve`.
The coefficient realization monoidal instance remains in the item.

This separates elaboration of the completed proof after profiling and attempts
to seal large constructions did not improve its approximately 82-second compile.
Both modules use normal transparency checking; the archive's two settings that
disabled it are removed. The public presentation statement and its three public
imports remain verbatim. The existing node keeps its Lean attachment and original
dependencies, adding only the proved section-monoidal existence lemma.
Change record: `coord/changes/E3-finite-comparison-presentation-universes.md`.

Validation: `lcompile.py --all` accepts the final item, support module, and all
four original direct consumers with no warnings and normal file limits. The
consumers are `DiscreteCoefficientModel`, `FixedScalarEtaleConstructibleSheaf`,
`EmbeddedFiniteHeartMonoidalPresentation`, and `FiniteComparisonLocalizing`.
All four consumer sources are unchanged; their checking copies were removed.
The two delivered Lean files contain zero holes and obey the 100-character line
limit. The public theorem statement and public imports were compared directly
with the archive and are identical.

## Proved and sorry left

Holes before: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No split-off sorry statements. The existing complete proof of
`AlgebraicGeometry.ProEtale.finiteComparisonPresentation`
(`lem-ctf-finite-comparison-presentation`) is restored and repaired, rather than
counted as a newly closed proof hole. The support module also has zero holes.

## No longer needed

The following direct proof imports moved from the item to the support module.
They remain needed there; these are not pruned mathematical dependencies:

- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence`
- `Mathlib.CategoryTheory.Functor.Flat`
- `Sheaf.Paper.FiniteDiscreteEncodedPresentation`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Mathlib.Algebra.Category.ModuleCat.Kernels`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport`

No recorded mathematical dependency is pruned and no module is withdrawn.
`Sheaf.Paper.IntegralOperationsWellDefined` remains imported for compatibility
with the instance names used by import-all consumers. The item's private
local instance supplies the fixed coefficient size without changing imported
instance registration.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned compilation repair with zero `sorry`s, as recorded in
`coord/rework.tsv`, not an unfinished mathematical argument. Its missing source
was quarantined, not withdrawn. The archive's size failure comes from the imported
`EssentiallySmall.{max v (u + 1)}` scalar-reduction instance. Fixing only the first
site-size occurrence leaves further instances of the same ambiguity. The private
local size instance resolves that ambiguity while keeping imported names and
instance registrations available to consumers. Shared definitions and target
statements are unchanged.

## New nodes

`lem-ctf-section-monoidal-exists`, in
`Sheaf.Paper.FiniteComparisonPresentationSupport`, records the completed existing
section-monoidal existence argument. It applies the normalized section tensor
comparison through Mathlib's `CoreMonoidal.mk'`. It has zero holes and is strictly
part of step 6 of the presentation argument. The other moved helpers remain private.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
