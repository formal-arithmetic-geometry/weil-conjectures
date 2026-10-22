## What changed

Proved `AlgebraicGeometry.supportedHom_pullback` by assembling the canonical constant
exchange, supported evaluation and cocycle normalization. Constructed the étale,
pro-étale and site-comparison transports explicitly, including complement arrows and
constant-unit normalization. Proved the derived comparison square with the existing
right-derived base-change cube theorem. The pro-étale supported object is transported
from the ordinary pro-étale constant to the published étale-origin constant via its
canonical comparison isomorphism.

Added the module-valued transport lemma
`AlgebraicGeometry.moduleSupportedHom_transport`. Its proof uses the derived unit,
an injective resolution after exact inverse image, and the given cocycle normalization;
it does not assume that inverse image preserves injectives.

A private categorical lemma reduces the identity-resolution roof before the
normalization proof is instantiated on sheaves. This avoids rewriting the large
specialized roof expression. Private projection lemmas expose only the
normalization and transport fields used
by the compatibility and square proofs. Large proof fields use proved auxiliary
theorems in the assigned file. The square calculation is proved categorically in
that same file and then instantiated for the four scheme functors. The normalization, coefficient-change, exchange and coherence
proofs all remain in that file.

The assigned module preserves every existing declaration type up to definitional equality,
and every original attribute and public import. The assigned theorem statement is unchanged.
Its `SupportHomPair.cocycleMorphism` body now uses the shared, irreducible localized
cocycle construction from `SupportedHomCocycleNormalization`; its old/new equation
is reflexivity after unfolding that construction. The normalization interface's
`SupportedHomChiCocycle` formula uses the same map. Its new proved equation exposes
the original single-complex construction. This avoids repeating that construction
inside normalization and coefficient-transport proof terms. All the argument's steps
remain in the assigned module. The module-valued transport interface is publicly
imported because the assigned
public definitions use its shared compatibility predicate and the cocycle and
derived Hom-map constructions that it reexports. The two additional change records are
`coord/changes/B8-supported-hom-cocycle-shared.md` and
`coord/changes/B8-supported-hom-cocycle-morphism-shared.md`.
In the unclaimed dependency
`Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization`, spelled out the
existing adjunction unit and constant exchange to replace its broad public Kummer
import by the two narrow operation imports. The bodies are definitionally equal to
the original bodies; every signature, attribute and theorem proof is preserved.
No adopted source-library declaration is changed. There are no forced adaptations.
The change records are `coord/changes/B8-supported-constant-restriction-direct.md`
and `coord/changes/B8-supported-constant-exchange-direct.md`.

The same definition-level repair reuses `Functor.representableTransportHom` for
`SupportHomPair.Transport.homMap` and the shared compatibility predicate for
`SupportHomPair.Transport.Compatible`. Both formulas are definitionally equal to
the original formulas, with the original parameter names, order and binder
information. The transparent `SupportHomPair.derivedHom` name is the original Hom
type. The Hom-map signature uses it to avoid repeatedly computing the
universe through the chosen derived localization. The complete assigned module
compiled cleanly with the resulting definitions. The mathematical proof remains
in the assigned module.
The added change records are `coord/changes/B8-supported-hom-map-shared.md`
and `coord/changes/B8-supported-hom-compatibility-shared.md`.

The group object now uses the existing `Sheaf.supportHypercohomologyFunctor` instead
of expanding that same functor's composition in its body. This is the same object
by reflexivity; no signature or mathematical statement changes. The change record
is `coord/changes/B8-supported-hom-group-shared.md`.

The identification's chi and naturality fields now use the existing
`SupportedHomChi` and `SupportedHomChiNatural` type aliases. They unfold to the
original field types, and the cocycle normalization clause is unchanged. This
shares the types across the identification and transport interfaces. The change
record is `coord/changes/B8-supported-hom-identification-shared.md`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.supportedHom_pullback`
(`lem-pur-supported-hom-pullback`): 1 hole closed out of 1.
Added the exact compatibility predicate `AlgebraicGeometry.moduleSupportedHomCompatible`
and the proved theorem `AlgebraicGeometry.moduleSupportedHom_transport`
(`lem-pur-module-supported-hom-transport`): 0 holes added.
There are no remaining `sorry` declarations in the assigned module or the new
transport module, and no unfinished statements are split off. The adapted dependency
retains these six original holes, all attached to
`lem-pur-supported-constant-exchange-normalization`:

- `AlgebraicGeometry.SupportedConstantNormalization.presentation`
- `AlgebraicGeometry.SupportedConstantNormalization.scheme_normalization`
- `AlgebraicGeometry.SupportedConstantNormalization.site_normalization`
- `AlgebraicGeometry.SupportedConstantNormalization.sectionMap_existsUnique`
- `AlgebraicGeometry.SupportedConstantNormalization.compareSectionMap_existsUnique`
- `AlgebraicGeometry.SupportedConstantNormalization.comparison_square`

The adapted `Sheaf.Paper.SupportedHomCocycleNormalization` retains its original
hole `AlgebraicGeometry.supportedHom_cocycle_normalization`, attached to
`lem-pur-supported-hom-cocycle-normalization`. The shared cocycle and its equation
contain no holes. These are seven retained dependency holes, zero holes added.
The other imported normalization
statements are existing stage-3 proof dependencies; their holes are not claimed closed.

The complete assigned module compiled cleanly with artifacts in 38.6 seconds.
The new transport module compiled cleanly in 33.7 seconds, the adapted cocycle
normalization dependency in 15.6 seconds, and the adapted constant normalization
dependency in 6.6 seconds. Separate checks proved the original derived Hom type,
Hom-map, compatibility predicate and group formulas by `rfl` (48.0 seconds), and
both original identification field types by `rfl` (3.2 seconds). The old/new
constant-definition equations were also proved by `rfl`. Diagnostic files are
excluded from the delivery. The delivery preflight checks declaration types,
imports and proof dependencies.

The assigned and new transport modules contain no proof placeholders; the seven
retained dependency holes are listed above. All original public declaration types remain definitionally equal, and the assigned
theorem statement and original public imports remain preserved. The equivalent definition bodies
and the dependency's import change are recorded explicitly.

## No longer needed

The proof does not apply the abelian-group-valued transport theorem of
`lem-pur-derived-representable-transport`. Its module remains imported because the
public Hom map reuses its existing `Functor.representableTransportHom` definition.
The new module-valued transport proof is still necessary and is proved directly
from cocycle normalization. No pruning of that node or module is claimed.

`thm-pur-with-support-exactness` is not an additional proof dependency: the statement's
derived pullback is already defined as the normalized base-change transformation.
Its existing public import and statement dependency remain preserved.

Removed the following old private imports; the proof uses the two canonical
normalization interfaces instead of reconstructing their proofs:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`
- `Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation`

Removed the obsolete direct `tool_uses` approvals from this node:

- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-weil-pbc-proetale-constant-exact`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-open-closed-short-exact`
- `lem-weil-pbc-etale-shriek-base-change-modules`
- `lem-cbc-proetale-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-cbc-proetale-extension-zero`
- `prop-pur-kinjective-resolutions-exist`
- `lem-sc-p1-rhom-hom-derived-roof`
- `lem-amb-closed-support-hom`
- `lem-sc-bounded-below-injective-resolution`
- `lem-sp-kinjective-comparison-principle`
- `lem-weil-pbc-comparison-pullback`
- `lem-pur-kinjective-degreewise-existence`

These are no longer direct tools of this proof; dependencies needed inside the
retained normalization interfaces remain attached to those interfaces.

The adapted normalization dependency no longer imports
`Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`: its only uses were the two
concrete maps now written directly. The existing Kummer declarations, their signatures,
proofs and dependencies remain in the library. This removes that broad import from
this proof route; it does not withdraw any adopted declaration.

No modules are withdrawn. Dependencies of retained upstream declarations remain.
The unit `sk-prop-a1-kummer` and all its realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned generic transport lemma is not directly applicable: its coefficient
category is `AddCommGrpCat`, while the assigned statement derives a `ModuleCat`
functor. The new lemma proves the needed formula for the actual module-valued map.
Also, the pro-étale normalization uses the ordinary pro-étale constant while this
item uses the étale-origin constant. The proof conjugates the normalization and
closed exchange by the canonical supported-constant comparison; it does not identify
these sheaves by a definitional equality.

## New nodes

`lem-pur-module-supported-hom-transport` records the module-valued exact transport
calculation used by each of the four compatibility clauses. It is a genuinely
separate categorical result: it contains neither scheme exchange constructions nor
the comparison-square coherence required by the assigned theorem. The new node is
under the same chapter and unit, derived from proof step 3 of the assigned node.
Edge cases checked in the argument: the identity functor, zero representing object,
zero or full support, and all integer degrees. The resolution and cocycle argument
does not impose a positivity condition on the degree or preservation of injectives.

Its resolution steps cite the existing Mathlib leaves
`lem-sc-bounded-below-injective-resolution-existence` and
`lem-weil-pbc-dplus-injective-representative`; the stronger ringed-site K-injective
resolution theorem is not invoked by the transport calculation.

The new node records LeanSearch, LeanFinder/Loogle and local source searches.
The change-record user tables include the newly landed affine-diagonal,
affine zero-section and projection-purity consumers; all three are unclaimed
and use definitionally equal types and constructions, so no adaptation is needed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
