## What changed

Proved `AlgebraicGeometry.Etale.exactCompactificationUnit_refinement` without changing its
signature, public imports, or docstring. Its proof uses the canonical common refinement,
compares the two transported sheaf maps by cancellation of their monic support inclusion,
and descends the resulting homotopy equalities by fully faithful localization whiskering.
The transport argument works for natural transformations; it does not require constructing
an isomorphism between an arbitrary supplied sheaf functor and the common refinement.

Added `Sheaf.AlgebraicGeometry.CompactificationSheafRefinement`. Its definition constructs
the refinement map explicitly from the ordinary adjunction unit, inverse open base change,
and the direct-image compositor. The theorem proves that it preserves the compactification
inclusion and that the inclusion is componentwise monic, using restriction to the open and
its closed complement.

Added `Sheaf.AlgebraicGeometry.CompactificationRefinementHomotopyUnit`. It proves the
normalization identity for one cartesian refinement and an arbitrary exact source functor.
A private lemma proves the whole pasting calculation over abstract abelian categories,
so its sheaf specialization does not unfold large sheaf constructions. Private proved
helpers derive the adjunction-unit formula from the exact derived triangle
comparison and the composition-unit formula from `rightDerivedNatTrans_app`. The homotopy
compositors are retained explicitly; the ordinary transported-map identity is checked on
complexes before passing to their homotopy classes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exactCompactificationUnit_refinement`
(`lem-sfb-exact-compactification-unit-refinement`).

The added public theorems are proved:

- `AlgebraicGeometry.Etale.compactificationSheafRefinement_properties`
  (`lem-sfb-compactification-sheaf-refinement`).
- `AlgebraicGeometry.Etale.compactificationRefinement_homotopyUnit`
  (`lem-sfb-compactification-refinement-homotopy-unit`).

There are zero holes in the item and zero holes added elsewhere. The explicit new
`compactificationSheafRefinement` definition contains no holes or arbitrary choices;
its inverse base-change map is uniquely determined by the existing isomorphism theorem.
No statement was weakened and no existing library declaration was removed.

Validation: all three delivered modules compile through `lcompile.py`. The final
checks took 36.2 s for the sheaf refinement module, 30.2 s for the homotopy unit
module, and 7.4 s for the item. All are below the 60 s per-file limit.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` from the item.
The proof no longer uses the previous planned proof dependencies
`lem-amb-unbounded-compact-support-comparisons`,
`lem-amb-unbounded-proper-open-interchange`,
`lem-cbc-proper-support-sheaf-composition`, or
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
The last generic composition identity needed here is proved directly using the source
library's composition-unit API. A separate K-injective proper/open normalization theorem
is unnecessary: exact inverse image and the derived adjunction-unit identity suffice.

These are removals from this proof route, not withdrawals of the modules or their
existing declarations. In particular the old compact-support-comparisons node remains in
the original statement's convention list and may have other consumers. No global module
withdrawal or modification of the adopted source library is requested.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original route was more general than required: it
suggested a proper/open comparison normalized through resolutions. The displayed
refinement is already defined by an adjunction unit and a derived composition map, so
formal unit compatibility proves the required normalization directly. The common
refinement argument only needs transported natural transformations, not an independently
constructed transported sheaf isomorphism.

Edge cases checked in designing the new statements include the identity refinement,
empty source, and zero input natural transformation. The cartesian hypothesis is retained
exactly where inverse open base change is used. The blueprint unit and its realized route
are unchanged.

## New nodes

`lem-sfb-compactification-sheaf-refinement` records the explicit ordinary refinement map,
its preservation of support inclusions, and monicity of those inclusions. Its two
construction/uniqueness facts are proved together in the stated properties theorem.

`lem-sfb-compactification-refinement-homotopy-unit` records single-refinement unit pasting
before localization. It is independent of support-inclusion cancellation and common
refinements and applies to arbitrary input natural transformations. It is proved, not a
new residual obligation.

The item node's proof, proof dependencies, and proof origin are updated to this route.
No change record is needed: only the item's proof and its node, plus the two new modules
and their new nodes, are changed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
