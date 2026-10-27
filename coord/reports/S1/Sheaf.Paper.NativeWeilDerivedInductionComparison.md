## What changed

Decomposed the original comparison into native heart properties and the integer-induction
summand comparison, with separate modules and sourced DAG nodes. The original theorem assembles
these statements, the two triangulated instances, proper normalization, and exact open
normalization. Its signature is unchanged.

Proved the exact open normalization from exact-localization factorization identities.
Proved the heart clauses from the free-derived properties, constructible pullback,
and closure under coproducts, reducing its last clause to the localized free cofan.
Proved proper normalization from the unit equations of the canonical right-derived
comparison factors. Repaired the retained proof by closing the definitional identity after
localizing the literal forgetful square, and omitted its unused target-resolution hypothesis.
Validation: lcompile.py compiled the data, free coproduct and induction-summands modules;
after the repair it compiled the heart properties (2.9 s), proper normalization (7.2 s),
and final comparison assembly (5.9 s), all without warnings. Delivery compiler/preflight
checks are run by deliver3.py before push.

Moved the original comparison definitions verbatim to NativeWeilInductionComparisonData to
avoid an import cycle between the theorem and its components. The original module publicly
imports it, retaining the same API. See coord/changes/native-weil-comparison-components.md.

## Proved and sorry left

Original holes: 1. Original hole closed by decomposition:
AlgebraicGeometry.NativeWeilInduction.nativeWeil_derived_induction_comparison
(lem-sf-native-weil-derived-induction-comparison).

New completed results:
AlgebraicGeometry.NativeWeilInduction.exactForgetNormalization_proof;
AlgebraicGeometry.NativeWeilInduction.nativeWeil_proper_normalization;
AlgebraicGeometry.NativeWeilInduction.nativeWeil_heart_properties.

Two new holes remain, each a sourced public theorem whose proof is exactly by sorry:
AlgebraicGeometry.NativeWeilInduction.nativeWeil_free_coproduct
(lem-sf-native-weil-free-coproduct);
AlgebraicGeometry.NativeWeilInduction.nativeWeil_induction_summands
(lem-sf-native-weil-induction-summands).

This is a decomposition of one original hole into two strictly smaller obligations, not a
complete proof of the comparison and not net hole reduction. Holes closed: 1; holes added: 2;
net hole reduction: -1. The item module has zero textual holes; its new components have two.
No sorry occurs inside data.

## No longer needed

Removed proof imports from the original comparison data:
Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares;
Sheaf.CategoryTheory.KInjectiveDerivedMapComputation;
Sheaf.CategoryTheory.KInjectiveExactSquareComparison;
Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses;
Sheaf.CategoryTheory.RingedSheafSliceAdjunction;
Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction;
Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage;
Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization.

Their planned uses remain recorded below the new component nodes where appropriate. No
existing module or mathematical dependency is asserted globally unnecessary. No upstream
declaration is removed. No item withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

Delivery tooling: in this resumed session, two deliver3.py attempts each exhausted the
50-minute priority-slot wait and returned exit 75: DELIVERY BUSY: 6 deliveries are running
on this machine. Nothing was pushed. The repaired six-module packet compiles as recorded
above and remains preserved for retry.

The old rework row points to a quarantine archive absent from the current shared source;
the current item module is present and was used as the source. Its definitions are preserved.
The rework dependency is still transitive through NativeAdicCompactSupportSums and finite
coefficient duality; ProjectiveLineGenusZero is present in the current source. No dependency
is withdrawn to conceal that build failure.
The original data and full theorem shared a module, so importing individual proof components
would create a cycle; the data module resolves this without changing their mathematical bodies.

Edge cases were checked against the source constructions: integer zero, negative indices,
empty schemes and zero objects are included; the remaining lemmas add no boundedness or
absolute separatedness hypotheses. The derived Weil category is never identified with fixed
pairs in the ordinary derived category.

## New nodes

def-sf-native-weil-induction-comparison-data: existing comparison data and proved exact
normalization.
lem-sf-native-weil-heart-properties: Grothendieck, exactness, conservativity, Frobenius and
free integer coproduct clauses.
lem-sf-native-weil-proper-normalization: canonical proper unit equation.
lem-sf-native-weil-induction-summands: integer exchanges, actual adjunction transpose,
summand equation and invertibility on the constructible localizing hull.

lem-sf-native-weil-free-coproduct: localized free integer cofan universal property.

Change record: coord/changes/native-weil-comparison-components.md.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
