## What changed

Proved `WeilConjectures.integralConstructibleReductionHom` from the defining augmented
Roos completeness of the target and the adopted source theorem
`CategoryTheory.Pretriangulated.IsHomotopyLimit.bijective_milnorMap`.
Proved private helpers identify the intrinsic quotient transitions with the
normalized scalar-adjunction transitions and establish finiteness of shifted Hom
into each restricted finite reduction. The latter reuses the existing proved
private `intrinsic_hom_finite` from `CompactSupportTermHomFinite`, accessed with a
private `import all`; it does not use that module's compact-support theorem.
The other two private helpers give the general Roos-cone conversion and the
adjunction compatibility calculation.
No signatures, definitions, public imports, or adopted source files change.
The item node records this shorter proof route. Its unit has no realized steps
that this route bypasses.

## Proved and sorry left

Closed one hole: `WeilConjectures.integralConstructibleReductionHom`
(node `lem-sf-integral-constructible-reduction-hom`).
Added zero holes; split off zero statements. No `sorry` remains in the delivered
module. All four private helpers are fully proved. Existing dependencies retain
their own proofs and holes; this is a proof from the published interfaces, not a
claim that the transitive library is already sorry-free.

## No longer needed

The proof does not use `lem-coef-integral-mapping-limit-projections` or
`Sheaf.Paper.IntegralMappingLimitProjections`: applying Hom to the defining Roos
triangle avoids the enriched mapping-system comparison entirely.
It does not directly use `cor-weil-finite-constructible-hom`,
`lem-weil-structure-direct-images-constructible`, or
`lem-weil-point-sections-finite-torsion` and their modules
`FiniteConstructibleHom`, `DirectImagesConstructible`, and
`PointSectionsFinitenessFiniteTorsion`. The proved `intrinsic_hom_finite` instead
uses the existing etale finite-Tor internal Hom and finite-type direct-image
finiteness interfaces, exact point sections, and finite-ring derived etale origin.
These nodes are removed from this item's direct proof dependencies; no claim is
made that their modules leave other consumers' import closures.
No original import was removed: all four public imports support the unchanged
statement. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned enriched mapping-limit comparison was unnecessary for this Hom-set
statement: the adopted source already proves the Milnor Hom bijection for a
specified homotopy-limit cone. Completeness alone gives existence, and the finite
shifted-Hom groups give uniqueness. The transition comparison is proved on K-flat
representatives without assuming derived restriction is faithful.

The proof uses `lem-sf-compact-support-term-hom-finite` as a tool from another unit,
only through its fully proved private general finite-Hom helper. It also uses the
published shift-closure and representative-comparison tools; none replaces a
realized step of this item's unit. These uses are listed in the node's proof;
maintainer tool approvals are not edited by this delivery.

Searches used before writing the proof: msearch leanfinder (eight unrelated hits),
loogle (no match for the initial Hom-exactness query), msearch grep (no Mathlib
match), and project rg, which located the adopted source Milnor bijection and the
proved general finite-Hom helper. Empty and zero objects and level zero were
checked: the argument has no nonempty, nonzero, or positive-index restriction.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
