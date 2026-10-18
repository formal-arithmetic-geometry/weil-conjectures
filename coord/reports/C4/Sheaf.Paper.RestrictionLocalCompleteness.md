## What changed

The signature and public imports of
`CategoryTheory.restrictScalars_locallyDerivedComplete_iff` are unchanged. Its proof
first compares the two existing presentations of localization and slice restriction,
then applies invariance of completeness at a single section. The complete-elements
ideal and its covering-sieve descent upgrade image sections to the given locally
generated ideal IB; the converse uses the maximal sieve and naturality of φ.

Three supporting modules record the proved comparisons:
`Sheaf.Paper.LocalCompletenessModels`,
`Sheaf.Paper.RestrictionDerivedProducts`, and
`Sheaf.Paper.RestrictionSectionCompleteness`. All imports added to the original
module are private proof imports. No existing definition or statement is changed,
and no adaptation of another group's module is required.

The support proof uses the existing localization free resolution, multiplication
Roos-tower criterion, K-injective products, K-flat resolutions and general derived
adjunction theorem. Restriction is exact and conservative, and its derived functor
is a right adjoint, hence preserves products. Invertibility of one minus the product
shift is consequently preserved and reflected. The comparison with slice
restriction commutes with multiplication by naturality of φ.

Edge cases checked mathematically: f=0 gives the identity for one minus shift;
if f is invertible completeness forces the slice restriction to vanish; the zero ring and
empty site cause no exception. The argument applies to unbounded complexes and
nonflat coefficient maps (including Z→Z/2), and imposes no finite generation
condition. There is no choice of arbitrary data in a definition.

Validation: all four files compile in import order through lcompile.py; the
single-section file takes about 34 seconds, within the unchanged 60-second limit.
The final delivery dry run also checks the axiom probe and preflight.

## Proved and sorry left

Closed the original one hole:
`CategoryTheory.restrictScalars_locallyDerivedComplete_iff`
(`lem-weil-pbc-restriction-local-completeness`). Added zero holes. No sorry remains
in any delivered module. This is a proof from existing declared dependencies,
not a decomposition into new unproved statements.

Also proved `CategoryTheory.localCompleteness_models_iff`,
`CategoryTheory.scalarRestriction_derived_isRightAdjoint`,
`CategoryTheory.restrictScalars_completeElement_iff`, and the conservative,
limit-preserving and colimit-preserving instances for underived
restriction. All private helpers are proved.

Existing imported theorems that still have their own holes are used with their
unchanged statements, as required by stage 3. They are not counted as holes added
by this delivery.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.LocalHomTowerCriterion`
- `Sheaf.Algebra.Homology.DerivedInternalHom`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`

These are direct-import removals, not claims that the underlying mathematics is
unneeded transitively. The tower criterion, derived limit, internal Hom, module
categories and restriction remain used by the support proofs. The item's new
direct proof dependencies are the two comparison lemmas and the original
complete-elements ideal lemma. No original planned mathematical dependency is
pruned from the transitive argument. No module is withdrawn. The unused faithful-restriction helper was also removed
from the new support module before delivery.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not explicitly bridge its two localization models:
the target's predicate uses sheafified fraction localization and an exact descended
slice functor, whereas the available complete-elements and tower APIs use a
sequential colimit and a chosen Q-representative. The new model comparison proves
that bridge without changing either definition.

The DAG also records `lem-pur-sheaf-ring-derived-coefficient-adjunction` with Lean
module `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`, but that
file and declaration are absent from this checkout. Its statement is broader and
includes normalized derived adjunction formulas that are not needed here. The
narrower right-adjoint property required by this proof is proved from the available
generic derived-adjunction and resolving-class declarations instead. It leaves no
new obligation and does not replace any proper-base-change unit step.

The original statement was not disputed. No signature, target statement, public
visibility of an existing declaration, or existing definition was changed.

## New nodes

`lem-weil-pbc-local-completeness-models` records the proved equivalence between
fraction/exact-restriction and sequential/chosen-representative completeness.
Its source is Tag 0997 and the already stated localization free resolution.

`lem-weil-pbc-restriction-derived-products` records the proved exact and
conservative underived restriction API and the right-adjoint property of its
unbounded derived functor. It uses sheafified extension, K-flat resolutions,
essential constancy and the generic derived adjunction theorem. Generic tools
from other units are declared in its split report.

`lem-weil-pbc-restriction-section-completeness` records the proved coefficient
comparison for a single section, without an ideal. It combines the existing
multiplication-tower criterion with product preservation and reflection of
isomorphisms, and explicitly proves the multiplication compatibility square.

All three are proved, with zero split-off holes. Their searches, sources and proof
steps are recorded, and the original item's proof route is updated. No change
record is needed because no existing statement or definition changes.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
