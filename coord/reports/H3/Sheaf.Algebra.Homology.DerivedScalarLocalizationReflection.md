## What changed

Prove `SheafOfModules.derivedScalarLocalizationReflection` with its entire signature unchanged.
A private, proved helper establishes fullness of ordinary restriction to the localization.
It clears sectionwise denominators and then uses the local-surjectivity Hom equivalence for
ring sheafification. The existing module comparison supplies local surjectivity from the
abelian module sheafification unit, without a new site hypothesis.

Exactness is imported from `CategoryTheory.scalarLocalization_sheaf_exact` and transferred
through the prescribed object/map equalities. The proved ordinary coefficient adjunction
gives both normalization formulas. Exact-functor derivation makes the specified universal
comparison `m.ε` invertible. Mathlib's `Adjunction.localization` then descends the ordinary
adjunction directly to `m.T`; its component formulas give both derived normalization
equations. Full faithfulness makes the ordinary counit invertible, and the derived formula
and essential surjectivity give its invertibility everywhere. The final unit identity and
both inverse equations are proved explicitly using naturality and the triangle identities.

The node's proof, proof dependencies and proof origin follow this route. No target,
definition, public declaration signature, source-library declaration or unit route changes.

## Proved and sorry left

Closed: `SheafOfModules.derivedScalarLocalizationReflection`
(`lem-sfb-derived-scalar-localization-reflection`), the item's one original hole.
Added: none. Left in the delivered Lean module: none. Split off: none.
The existing exactness theorem `CategoryTheory.scalarLocalization_sheaf_exact` is used as
its stated interface; its proof is outside this delivery. The final sandbox compile completed
with exit code 0 and no warnings.

## No longer needed

Removed explicit imports:
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` (public);
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction` (public);
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` (proof only);
- `Mathlib.CategoryTheory.Localization.Predicate` (provided by the adjunction import).

The fraction calculation uses only the basic localization interface already provided by
the localization definition.
The public-import change is recorded in
`coord/changes/derived-scalar-localization-reflection-imports.md`; there are zero current
Lean importers, and no adaptation is needed. Tensor/cochain definitions that the model's
own statement uses remain available through its original public imports.

The proof does not use `lem-pur-sheaf-ring-derived-coefficient-adjunction` or
`lem-pc-kflat-resolution` as proof dependencies. Direct localization of the exact ordinary
adjunction constructs the required normalized adjunction for the given universal pair,
so comparison on K-flat representatives and subsequent extension of the unit formula are
unnecessary. Their obsolete `tool_uses` approvals are removed, preserving the order of
the retained approvals. The corresponding statement dependency is retained unchanged: this delivery
does not alter what the theorem states. No existing declaration or module is withdrawn.
Source import-graph comparison also removes the following four project modules from this item's import closure:

- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
  (`lem-pur-sheaf-ring-derived-coefficient-adjunction`);
- `Sheaf.Algebra.Homology.SheafRingDerivedHomComparison`
  (`lem-pur-sheaf-ring-derived-hom-comparison`);
- `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`
  (`new-derived-adjunction-compatibility`);
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
  (`def-pc-essentially-constant-ind-diagram`).

These are pruning relative to this item; other parents may still need them. In contrast,
`CochainTensorUniverses` and `KFlatResolutionIndependentCoefficients` remain transitively
imported by the model/exactness interfaces and are not claimed as pruned modules.

## Where the brief, the DAG or earlier work was wrong

The original plan's K-flat comparison step is unnecessary for this Lean statement: it
asks for an adjunction with specified normalization on the supplied universal pair, and
Mathlib directly descends the ordinary exact adjunction with precisely those formulas.
The proof uses local surjectivity of the ring sheafification map, derived from its
existing module comparison; it never assumes sectionwise surjectivity of sheafification.
Denominators are units even when s is zero or nilpotent, so the zero ring and empty site
require no exclusions. The site object, site morphism and two derived morphism universes
stay independent.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
