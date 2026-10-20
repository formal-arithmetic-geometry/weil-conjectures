## What changed

Proved `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization` in
`Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` with its existing statement unchanged.
Constructed the site isomorphism from the explicit relative Frobenius lift, its
module trivialization by adjunction conjugation, and composition over every
commutative coefficient ring. Proved the normalized unit, open restriction,
additive-iterate and zero-iterate equations and transported the ordinary equations
through the existing exact-derived coherence API.

The normalized ordinary composition now reuses
`proEtaleConstantRingModulePullbackComposition`. Generalized that existing proved
theorem in `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition` by removing
its unused `[Finite Λ]` hypothesis. Its proof and all other declarations are
unchanged. Stacks Tag 03D8 applies to arbitrary ringed topoi. The module is unclaimed;
its existing finite-ring consumer, FiniteSystemPullbackCoherence (M3), needs no
adaptation. The comparison and all its section/conjugation equations are unchanged.

All helpers added to the item are private and proved. Its two public derived
comparison definitions and public imports are unchanged. The geometric argument
specializes the existing finite-field universal-homeomorphism theorem to the prime
field and handles every iterate, including zero. The coefficient map has a private
constant-section API; the module direct-image trivialization uses the explicit
`SheafOfModules.pushforwardId` isomorphism. Local irreducibility settings retain
these APIs during elaboration. Section calculations use the underlying set-valued
presheaf and a generic lemma with the ring sheaf as a parameter. The composite
comparison map and its mate equation are passed separately, avoiding repeated
scalar-action conversions. The section formulas retain the canonical
pullback-composition map directly. Some private technical
helpers are adapted from RelativeFrobeniusIntegralUniversalHomeomorphism and
FrobeniusTrivializationPullback; those modules are not edited.

Updated the item node's proof route and the composition node's statement/Lean
record to the generalization, with a statement-change record. No new node or
unfinished mathematical result is introduced. The target and consumer statements
remain identical.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization`
(node `lem-trf-absolute-frobenius-site`). Added zero holes. No `sorry` remains in
the item module; none is added elsewhere. The generalized composition module has
zero holes before and after this delivery. This is a proof, not a decomposition.

Validation on the compile server: ProEtaleModulePullbackComposition compiles in
4.8 s; the complete item compiles in 22.7 s, with no errors or warnings. The axiom
probe prints exactly `propext`, `Classical.choice`, and `Quot.sound` for the proved
theorem. The unchanged current sources of FrobeniusTrivializationPullback (6.9 s),
FrobeniusStalkTrivializationNormalization (15.9 s), and SchemeGeometricFrobenius
(6.5 s) compile against the delivered item. Temporary probes and consumer copies
are removed from the packet. A source audit verifies the exact original theorem
signature, both original public derived-definition bodies, and all public imports;
all added helpers are private and proved, and all Lean lines are at most 100 characters.

The exact finite-system consumer expression
`(proEtaleConstantRingModulePullbackComposition h k (A n)).choose` compiles
with its original finite-ring binders against the generalized theorem (1.6 s in the final validation).
Compiling the complete, untouched FiniteSystemPullbackCoherence source reaches
the 60-second limit both with the original shared library and with the generalized
composition theorem. No changes to that M3-held module are included.

## No longer needed

Removed these private proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators`
- `Sheaf.Paper.IntegralFinitePullbackComposition`

Removed these dependencies from this node's proof route:

- `lem-pc-kflat-resolution`
- `lem-trf-relative-frobenius-universal-homeomorphism`
- `lem-trf-site-inverse-image-composition-generators`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-proetale-derived-pullback-composition`
- `lem-weil-pbc-weakly-etale-composition-base-change`
- `lem-weil-proetale-weakly-etale-localization`

The relative map is a universal homeomorphism by cancellation from absolute
Frobenius, so the separate relative-integrality theorem is not used. Weak etaleness
comes from Mathlib's cancellation API `WeaklyEtale.of_comp`, the Lean record of
`lem-trf-weakly-etale-between-objects`, which stays in `proof_deps` (reviewer correction). Module comparisons are obtained from the
explicit pushforward and its adjunction, so separate inverse-image generators,
slice-site localization, and continuous-pullback-adjunction statements are not
needed here. Exact-derived natural-isomorphism coherence replaces the K-flat
resolution and derived-composition statements. The operations and sheafification
APIs remain used through the retained public imports. The inverse-image node stays
in `proof_deps`; only its redundant direct import is removed. Removed the obsolete
`tool_uses` entries for continuous-functor-sheaf-pullback-adjunction,
proetale-weakly-etale-localization, proetale-derived-pullback-composition and
kflat-resolution; retained absolute-frobenius-well-defined. These are dependency
removals for this item; no upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan's K-flat-resolution route is unnecessary because the actual
module pullback in the statement is exact and the derived comparison is explicitly
defined using `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`.
The existing coefficient-composition proof was exposed under an unnecessary
finite-ring hypothesis, which made it unusable for this arbitrary-ring target.
Removed that hypothesis from the existing proved theorem and its node, preserving
the complete proof. Its Stacks source concerns arbitrary ringed topoi.
The module's original statement and the blueprint unit route were preserved.

Change records: `coord/changes/D5-absolute-frobenius-site-proof-interface.md` and
`coord/changes/D5-module-pullback-composition-arbitrary-rings.md`.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
