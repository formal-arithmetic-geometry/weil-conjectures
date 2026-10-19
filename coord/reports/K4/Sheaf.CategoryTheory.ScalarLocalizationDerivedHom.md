## What changed

Proved `CategoryTheory.scalarLocalizationSectionsMap_mem` and
`CategoryTheory.scalarLocalizationSections_isUnit` in
`Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`, without changing any declaration's
statement, visibility, or definition. The first proof applies the naturality equation of the
ring-sheaf morphism to a section and then uses the section's restriction compatibility.
The second proves that the localized coefficient is a unit at every object, maps that unit
through ring sheafification, and assembles sectionwise inverses into a compatible section.
Compatibility follows by cancellation of the localized coefficient. The product with the
inverse section is one, proving invertibility in the section ring.

Both proofs compile together against the current sources using the required server
compiler (14.2 seconds, exit code 0). The current proof-dependency import
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` has been retained, so the
delivery changes only the two proof bodies relative to the current library.
The argument uses no nonzero or regularity hypotheses: cancellation uses `IsUnit`, so zero
rings, nilpotent denominators, t = 0, and an empty site remain covered.

## Proved and sorry left

Original holes: 4. Closed: 2. Added: 0. Remaining: 2. No decomposition.

Closed:
- `CategoryTheory.scalarLocalizationSectionsMap_mem`.
- `CategoryTheory.scalarLocalizationSections_isUnit`.

Unchanged named theorem holes, both attached to
`lem-weil-pbc-scalar-localization-derived-hom`:
- `CategoryTheory.scalarLocalization_exact`.
- `CategoryTheory.scalarLocalization_derivedHom`.

These retain their original source references and complete proof plans. In particular,
exactness still needs the natural comparison between restricted scalar extension and
sheafified sectionwise tensor localization. The derived Hom proof still needs the
normalized derived adjunction, the telescope comparison, and the fraction-colimit argument.

## No longer needed

None. No import, node, or module is pruned: the two remaining theorem holes still have
the original proof plan and dependencies. No new modules or statements are introduced.

## Where the brief, the DAG or earlier work was wrong

The underlying telescope declaration exists, but its module
`Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope` publicly imports this item
for the coefficient-action definitions. It consequently cannot currently be imported as a
proof dependency here. Its existing node and stage-2 review already record this issue:
the coefficient definitions need to move below both modules before the intended import
can be used. This delivery leaves that interface unchanged.

The retained sandbox lacked the current proof-only import of
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`; this was restored before
compilation. The two completed proofs are otherwise retained from the earlier attempt.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
