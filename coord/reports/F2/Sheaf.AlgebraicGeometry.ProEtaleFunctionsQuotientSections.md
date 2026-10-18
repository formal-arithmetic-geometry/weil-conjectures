## What changed

Proved `AlgebraicGeometry.Scheme.exists_proEtale_functions_quotient_sections` with its original signature. The construction uses continuous maps into the indiscrete group for all functions and into the discrete group for locally constant functions. A locally bijective constant-presheaf map identifies the latter with the constant sheaf, including the required compatibility with the sheafification unit.

Private proved helpers establish the sheafified cokernel comparison, inheritance of closed points and separably closed residue fields by weakly etale objects, vanishing of constant-sheaf H1 on affine objects and their slice sites, and the quotient equivalence. All data are constructed; choices used for inverse equivalences are uniquely determined inverses. The geometric proof handles empty affine opens and uses no noetherian or coefficient finiteness hypothesis.

Updated the existing node's proof, proof dependencies and proof origin to describe the actual argument. Existing public imports and the public declaration are unchanged.

Validation: the full 563-line module compiled cleanly through `lcompile.py` in 21.3 seconds. A normalized comparison confirms that the original public theorem signature is identical. The delivered Lean file has zero `sorry` tokens and no lines over 100 characters. All added imports pass `tools/import_direction.py may`.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.exists_proEtale_functions_quotient_sections` (`lem-cbc-proetale-functions-quotient-sections`). No holes added, none left in this delivery, and no statements split off. The proof uses the declared etale/pro-etale cohomology comparison and affine etale acyclicity inputs; proving those inputs is outside this item.

## No longer needed

Removed the following imports:

- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`.
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` (retired wrapper).
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat` (provided by the affine weakly-etale API).
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (provided by the comparison theorem's public imports).
- `Sheaf.CategoryTheory.SiteCoveringAxioms` (provided by the two cohomological inputs).

Removed these proof dependencies and their old tool-use approvals:

- `lem-weil-pbc-proetale-restriction-injectives`: the existing proved `ProEt.sliceEquiv` and `ProEt.sliceDense` suffice; no module-coefficient restriction or derived comparison is used. Their module is `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, node `lem-weil-proetale-weakly-etale-localization`.
- `lem-weil-pbc-cohomology-over-object-localization`: restrict the short exact sequence to the slice directly and evaluate at its terminal object.
- `lem-weil-pbc-derived-functor-long-exact`: the proved source `Sheaf.H.ker_δ` is exactly the Ext exactness statement needed.
- `lem-pc-sepclosed-finite-sep-trivial`: Mathlib's `IsSepClosed.algebraMap_bijective` applies directly to the separable residue-field extension, including infinite algebraic extensions.

These are dependencies this proof no longer needs; other consumers may still need them. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old proof named a module-coefficient pro-etale restriction theorem, whose attached module is absent from the shared checkout, for an argument with arbitrary abelian coefficients. The existing fully proved weakly-etale slice-site equivalence works for these coefficients and replaces that dependency. The generic object-cohomology localization and derived-functor long-exact-sequence statements are stronger than the lifting step needs. Direct restriction of the short exact sequence and the existing Ext API give a shorter Lean argument.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
