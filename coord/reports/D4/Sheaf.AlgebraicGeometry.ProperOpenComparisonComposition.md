## What changed

Proved `AlgebraicGeometry.Etale.properOpenComparison_id`. Replaced the existing proof of
`AlgebraicGeometry.Etale.properOpenComparison_comp` by a direct counit/naturality calculation,
removing its dependency on the holed composition-mate restatement. All three existing public
signatures and the body of `properOpenDirectImageCompIso` are unchanged. Four private, fully
proved helpers express natural restriction, its composition, the conjugate counit equation,
and the final adjunction cancellation. No helper has a hole.

Both laws use the existing `properOpenIdentification_unit`, which normalizes the specified
geometric identification. Composition uses proved upstream derived-unit and inverse-image
associativity laws; identity uses their proved unit laws. Added proof-only imports of
`Sheaf.AlgebraicGeometry.ProperOpenIdentificationNormalization` and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc`. Kept all public imports unchanged.
Updated the existing node's proof, proof dependencies and origin to this argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.properOpenComparison_id`, the one original hole remaining
in the module as copied into this sandbox. Its node is
`lem-weil-pbc-proper-open-comparison-composition`.

Reproved: `AlgebraicGeometry.Etale.properOpenComparison_comp`, already proved in the current
shared source via `properOpenComparison_comp_mate`; this is not counted as a newly closed hole.

Added holes: zero. Holes left in the delivered module: zero. No new modules or nodes.
The imported existing `AlgebraicGeometry.Etale.properOpenIdentification_unit`, node
`lem-weil-pbc-proper-open-identification-unit`, remains an existing downstream obligation;
this delivery does not change it or claim its proof.

The complete composition and identity combining proofs were compiled independently in the
sandbox with the exact existing normalization signature supplied as a parameter. The full
module subsequently compiled and passed deliver3.py --no-push with no warnings or forbidden
axioms (dry-run commit 25b2406f06, review class CODEX because the existing node was updated).
All three existing public signatures and the public compositor definition body were also
compared textually against the shared source and are identical.

## No longer needed

Removed proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonCompMate`

The composition proof no longer needs `Sheaf.AlgebraicGeometry.ProperOpenComparisonCompMate`
or its node `lem-weil-pbc-proper-open-comparison-composition-mate`: the direct proof performs
its naturality and cancellation argument explicitly. That module's only direct importer was
this item, so it is a pruning candidate.

The open-extension unit is proved invertible locally from the derived exact-functor
composition/identity isomorphisms and the already invertible underived unit. Thus the large
`LowerShriekCoherence` module is unnecessary here.

The original direct proof dependencies below are not used directly by this proof:

- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-proper-open-section`
- `lem-weil-pbc-etale-restriction-injectives`
- `lem-weil-pbc-derived-open-restriction`
- `lem-weil-pbc-clopen-section-direct-image`
- `lem-weil-pbc-proper-open-identification`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `cor-cbc-derived-extension-zero-base-change`

Their geometric/injective calculations are already packaged by the existing normalization
statement or the already proved generic derived coherence API. In particular, no conversion
from constant-ring sheaf-of-modules encodings is needed: the generic coherence lemmas apply
directly to `ModuleCat Λ`. Several geometric modules remain transitive dependencies of the
unchanged public comparison definition and normalization theorem; no claim is made that those
modules are globally unused.

Removed obsolete top-level tool approvals, preserving the order of retained approvals:

- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-etale-restriction-injectives`
- `cor-cbc-derived-extension-zero-base-change`
- `lem-weil-pbc-inverse-image-composition-module-linear`

## Where the brief, the DAG or earlier work was wrong

The initially displayed module had two holes, but the shared source copied shortly afterward
already contained a proof of composition through the new composition-mate theorem. The DAG
still described the earlier injective-representative route. This delivery counts only the
identity hole as newly closed and replaces the composition route without creating a split.
The current blueprint moved this unchanged statement and proof to
`main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/` (order 1842).

The existing normalization theorem supplies the exact restriction formula missing from the
older plan's interfaces. Once it is used, all remaining coherence is proved categorical glue.
Both proof applications were checked for arbitrary schemes and finite commutative rings,
including empty schemes, zero complexes and the zero ring; no extra hypotheses were introduced.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
