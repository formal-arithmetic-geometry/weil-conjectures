## What changed

Replaced the single sorry in
`CategoryTheory.restrictScalars_locallyDerivedComplete_iff` by a complete Lean argument.
Its signature and the existing definitions are unchanged. The argument separately proves
that images of sections of I belong to IB, transfers the pointwise vanishing test, extends
that test to the image ideal with `Ideal.map_le_iff_le_comap`, and descends along the
covering sieve supplied by hIB. The reverse implication tests the actual image generator.
It uses the existing `ringedSite_complete_elements_ideal` declaration.

Added `Sheaf.Paper.LocalCompleteTestComparison`, with the proved theorem
`CategoryTheory.isRingedSiteCompleteElement_iff_localTest`. This compares exact derived
slice restriction with restriction of Q's representative, using
`Functor.mapDerivedCategoryFactors` and `Q.objObjPreimageIso`, then transports both
arguments of derived internal Hom along isomorphisms. It depends on the localization
presentation comparison below. The slice-instance bindings are transparent local lets;
opaque proof bindings do not identify the two derived-category presentations.

Added the pointwise scalar comparison module and proved the ordinary localization
comparison module:
`Sheaf.Paper.RestrictionCompleteElement` and `Sheaf.Paper.SectionLocalizationSequence`.
Updated the original node's proof, proof dependencies and proof origin to match the Lean
argument, and added a node for each new theorem. No existing statement or definition was
changed, so no consumer adaptation or definition change record is needed.

All four delivery modules compile through lcompile.py. The main theorem was checked
again after pruning its imports. The unit `sk-thm-properbasechange` and all of its realized
statements and proof steps are retained; this is a reduction below that unit.

## Proved and sorry left

Original module: one hole before, zero holes after. The closed upper hole is
`CategoryTheory.restrictScalars_locallyDerivedComplete_iff`
(`lem-weil-pbc-restriction-local-completeness`). Its proof from the intermediate
statements is complete Lean, including generated-ideal closure and descent.

The new theorem `CategoryTheory.isRingedSiteCompleteElement_iff_localTest`
(`lem-weil-pbc-local-complete-test-comparison`) is proved without a local sorry.

The new theorem `CategoryTheory.sectionLocalization_sequence_iso`
(`lem-weil-pbc-section-localization-sequence`) is also proved without a local sorry.
Its private helpers construct the fraction cocone, prove its ordinary module colimit
property, assemble the presheaf colimit and transport it through module sheafification.

One new hole remains:

- `CategoryTheory.restrictScalars_completeElement_iff`
  (`lem-weil-pbc-restriction-complete-element`): finish the pointwise comparison of the
  multiplication towers under scalar restriction. It needs compatibility with restriction
  to the slice, preservation of derived products/Roos triangles, and detection of zero
  through the unchanged cohomology abelian sheaves. There are no ideal-generation or
  covering-sieve hypotheses or conclusions in this theorem.

This is a decomposition: one original hole closed and one hole added, not a claim of
net sorry reduction or an axiom-free proof. Existing imported declarations may still
contain their already recorded holes. No definition contains a new sorry, and the
residual statement concerns one section, with no ideal or local-generation data.

Edge cases checked mathematically: no flatness or finite generation is used; zero and
nilpotent sections give zero localized modules; an invertible section gives the unit;
the fraction-colimit construction works for the zero ring; zero ideals, zero objects and
empty covering sieves do not introduce extra assumptions. The main Lean proof uses sieve
membership and the full local-generation equivalence as stated.

## No longer needed

Removed these direct proof imports from `RestrictionLocalCompleteness`:

- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.LocalHomTowerCriterion`
- `Sheaf.Algebra.Homology.DerivedInternalHom`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`

The main proof now uses exactly the complete-elements ideal theorem, the proved local-test
comparison and the pointwise scalar comparison. Thus its direct proof dependencies no
longer include `lem-weil-pbc-local-hom-tower-criterion`, `def-weil-derived-limit`,
`def-pur-derived-internal-hom`, `def-pc-sheaf-restrict-scalars`,
`def-weil-sheaf-of-modules-category` or `def-weil-abstract-derived-category`. Some of these
remain statement dependencies or occur below the residual pointwise comparison: they
are not claimed globally unnecessary. The complete-elements ideal node is retained.
The constant-ring `WeilConjectures...Sheaf.RestrictScalars` module is not used anywhere
in the new argument. No module is withdrawn and no global reachability pruning is claimed.

The comparison helper imports no ideal-sheaf or scalar-restriction module; these are not
needed for its signature or proof. The new scalar helper has no ideal-sheaf dependency.
The ordinary localization comparison uses preservation of colimits by sheafification;
it needs neither exactness of sheafification nor a separate free telescope resolution.
Those declarations may still be needed below the existing tower criterion.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically appropriate, but its declarations use different
localization and restriction constructions. The target uses sheafified sectionwise
localization and the induced exact derived restriction. The complete-elements ideal
uses a sequential localization and Q applied to restriction of a chosen representative.
The tower criterion has a third localization API. These cannot simply be interchanged by
an application of the criterion. The new comparison helper proves the restriction part
and uses the now-proved ordinary localization comparison explicitly.

Exact preservation of ordinary products alone should not be asserted to imply
preservation of derived products. The residual pointwise comparison's proof plan uses
the derived tensor/restriction adjunction to justify the latter before comparing Roos
triangles. No exactness of infinite products of sheaves is assumed.

## New nodes

`lem-weil-pbc-local-complete-test-comparison` records the proved compatibility theorem.
Its only new proof prerequisite is the ordinary localization-presentation comparison;
the derived-restriction comparison is implemented with Mathlib's factorization API.

`lem-weil-pbc-section-localization-sequence` records the ordinary module-sheaf isomorphism.
Its pointwise fraction colimit, compatibility with restrictions and preservation by
module sheafification are all implemented in Lean.

`lem-weil-pbc-restriction-complete-element` isolates the scalar comparison for a single
section and derived object. It remains to implement the tower comparison described
above, using the existing tower criterion and proving the needed derived-product compatibility.
A scratch compilation verifies ordinary exactness and conservativity directly: compose
restriction with `SheafOfModules.toSheaf`, identify that composite with the source's
forgetful functor by `Iso.refl`, and use `moduleSheaves_colimits_forgetful` together with
`preservesFiniteLimits_of_reflects_of_preserves`, its finite-colimit analogue, and
`reflectsIsomorphisms_of_comp`. The finite-colimit reflection instance is obtained from
`reflectsColimitsOfShape_of_reflectsIsomorphisms`. These facts alone do not finish the
comparison of derived products. A second scratch compilation also verifies derived
conservativity: use `Functor.mapDerivedCategoryHomologyFunctorIso`,
`DerivedCategory.isIso_iff`, and `isIso_of_reflects_iso` on every homology map.

All three carry sources, full proof plans, Mathlib searches of the required three kinds,
the inherited blueprint ancestor and the original chapter and unit. Blueprint searches
for localization, complete elements, slice restriction and restriction of scalars found
no existing blueprint statement of these exact API comparisons. No change records.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
