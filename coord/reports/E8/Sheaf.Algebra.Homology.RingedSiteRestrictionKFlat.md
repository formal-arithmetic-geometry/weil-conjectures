## What changed

Proved `SheafOfModules.ringedSite_restriction_exact_kflat` without changing its
statement. The proof uses the exact extension/restriction adjunction, the tensor
projection formula in both variables, and the additive total-complex comparison.
The comparison identifies both bicomplex differentials; the total-complex API
then handles their sum and sign. Exact faithful extension reflects acyclicity.
Faithfulness is proved directly from the sheafification unit's local injectivity
on a direct-sum summand and separatedness on the slice.

Generalized the complete projection-formula construction in
`Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData` and
`Sheaf.CategoryTheory.RingedSliceExtensionTensor` to separate the site morphism
universe from the coefficient universe. Existing specializations are unchanged.
The change record is
`coord/changes/ringed-slice-tensor-independent-universes.md`.
No source-library module was changed.

Validation: all three delivered Lean modules compile with no diagnostics. The
unchanged direct consumer
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits` also compiles
against the generalized interface. The assigned module compiled in 16.8 seconds;
the direct consumer compiled in 22.5 seconds. The support construction's last
uncached compile took 29.8 seconds. All checks use `lcompile.py`.

## Proved and sorry left

Closed one hole: `SheafOfModules.ringedSite_restriction_exact_kflat`
(node `lem-sfb-ringed-site-restriction-kflat`).
Added zero holes; zero split-off statements. No `sorry` remains in any delivered
Lean module. The two adapted projection-formula modules were already proved
and remain proved. This is a proof, not a decomposition.

## No longer needed

Removed the private proof import
`Sheaf.CategoryTheory.RingedSliceExtensionExactness` and the parent node's
proof dependency/tool use `lem-weil-pbc-ringed-slice-extension-exactness`.
Its coefficient universe did not cover the assigned theorem. The proof instead
uses the existing exact-functor API and proves extension faithful at the needed
universe, then applies Mathlib's `ShortComplex.exact_map_iff_of_faithful`.
This prunes that dependency from this proof only; other consumers still need it,
so no existing module is withdrawn. All other declared proof dependencies are used.

## Where the brief, the DAG or earlier work was wrong

The declared projection formula allowed an independent site object universe but
required its morphism universe to equal the coefficient universe. The assigned
statement allows `Category.{v} C` with coefficients in `max u v w`.
The existing complete direct-sum construction generalizes to this situation:
arrows have universe `v`, while coefficients/modules have universe `max u v`.
The change record lists consumers and preserves their old specialization.
The exactness/reflection interface has the same extra-coefficient mismatch;
the direct faithful-extension proof avoids changing that interface.
The parent node's proof now records exactly the route used by the Lean proof.
The blueprint unit's transport route is retained.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
