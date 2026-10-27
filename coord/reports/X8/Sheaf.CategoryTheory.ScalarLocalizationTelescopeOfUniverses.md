## What changed

Proved `CategoryTheory.scalarLocalization_telescopeOfUniverses` for the existing
`changeOfRingsOfUniverses` construction, preserving its statement and all three
original public imports. Restriction along the localization unit is exact. A
normalized ordinary adjunction descends through quasi-isomorphisms, and the
fraction colimit supplies the required derived telescope, including its prescribed
legs, naturality and shift laws. Adjunction injectivity and the exact-derived
factorization prove scalar semilinearity.

Added three proved helper modules:

- `Sheaf.CategoryTheory.ScalarLocalizationTensorComparisonOfUniverses`: restricted
  tensor comparison, canonical tensor-unit maps, naturality, and the regular unitor.
- `Sheaf.CategoryTheory.ScalarLocalizationFractionColimitOfUniverses`: sectionwise
  regular-module fractions, their tensor colimit for module sheaves, and the
  degreewise complex colimit with normalized inverse-power legs.
- `Sheaf.CategoryTheory.ScalarLocalizationCoefficientAdjunctionOfUniverses`: exact
  restriction and the normalized adjunction for the actual independent-universe
  tensor model.

These generalize the existing proved small-site arguments without changing their
original modules. Private helpers retain the generic derived-adjunction descent,
semilinearity, and complex-to-derived telescope argument. The tensor comparison
and ordinary tensor adjunction are locally irreducible after their computation
lemmas; this avoids unfolding their sheafification data in subsequent proofs.
The three helper modules separate the substantial tensor, fraction, and adjunction
arguments after profiling the original combined file. No shared definition or
existing interface is changed.

## Proved and sorry left

Closed the item's one original hole:
`CategoryTheory.scalarLocalization_telescopeOfUniverses`
(`lem-weil-pbc-scalar-localization-telescope-of-universes`).

All declarations of the three new modules are proved or explicitly constructed.
Holes closed: 1. Holes added: 0. Sorries left in the delivered files: none.
This is a proof, with no split-off unproved obligations.

## No longer needed

No existing module is withdrawn, and no original public import is removed.

The proof no longer applies
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction`: its normalized formula is for
`changeOfRings`, while this item fixes `changeOfRingsOfUniverses`. The new proved
adjunction supplies the required formula for that model.

`lem-weil-pbc-exact-functor-derived-functor` is not a proof dependency: the canonical
`Functor.mapDerivedCategory` and its existing factorization API suffice.

The small-site theorem
`lem-weil-pbc-scalar-localization-underlying-telescope` is not applied as a theorem.
Its module remains publicly imported because it defines the telescope property and
derived-unit predicate used by this item's unchanged statement. The generic part
of its argument is reproduced as a proved private helper; its small-site regular,
module, and complex colimit theorems are replaced by the new universe-independent
fraction-colimit proof. Those existing modules remain needed elsewhere and are not
claimed as globally pruned.

No Hom-localization equivalence, Hom-continuity hypothesis, or AsSmall transport is
used. The unit's Fourier/perverse route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged. The old dependency list did not directly
supply the normalized ordinary adjunction for `changeOfRingsOfUniverses`, and the
proved localization-colimit chain has small-site universe binders. Their proofs
adapt directly to the coefficient-universe tensor structures. The implementation
therefore uses this explicit adaptation, rather than the optional AsSmall route
mentioned in the previous proof sketch.

The fraction argument covers zero modules, the empty site, t-torsion, t=0, and
already invertible t: the ordinary module-localization colimit theorem makes no
regularity assumption, and no cancellation of t in the source ring is used.

## New nodes

`lem-weil-pbc-scalar-localization-tensor-comparison-of-universes` records the proved
restricted tensor comparison and its normalized section API. Its source is Stacks,
Modules on Sites, Tag 03EK. It realizes the tensor-comparison step below the same
blueprint ancestor as the assigned node.

`lem-weil-pbc-scalar-localization-fraction-colimit-of-universes` records the proved
complex colimit and all inverse-power legs. It uses the existing ordinary module
localization colimit, the new tensor comparison, and the actual sheafified
localization. Its sources are Stacks, Algebra, Tag 00CM, and Modules on Sites,
Tags 03CY and 03EK.

`lem-weil-pbc-scalar-localization-coefficient-adjunction-of-universes` records the
proved exactness and normalized adjunction for the fixed tensor model. Its sources
are Stacks, Modules on Sites, Tags 03CZ, 03DA and 03DB. Sectionwise scalar extension and
the module-sheafification Hom equivalence give its construction.

All three nodes have the assigned node's chapter and unit, logged Mathlib searches,
explicit proof steps and Lean attachments.

`coord/changes/X8-scalar-localization-telescope-private-proof-context.md` documents
the added private-helper section commands for the interface scanner. No existing
statement, definition, exported attribute, or public import is changed.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
