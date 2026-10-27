## What changed

Proved `CochainComplex.exists_totalTensorConeComparison` in
`Sheaf.Algebra.Homology.AdditiveTotalTensorConeComparison` by specializing the
existing signed bifunctor cone isomorphism to `curriedTensor C`, applying its
simultaneous naturality and inclusion lemmas, and applying `DerivedCategory.Q.mapIso`.
The original theorem signature, universes, and public imports are unchanged.
Updated the existing DAG node proof to record these three steps. No definitions,
other modules, or unit routes changed.

## Proved and sorry left

Closed one of one holes: `CochainComplex.exists_totalTensorConeComparison`
(node `lem-sfb-additive-total-tensor-cone-comparison`). Zero holes remain in the
item; zero holes were added or split off. The upstream cone comparison and its
naturality module contain no `sorry`. The proof compiled through `lcompile.py`.

## No longer needed

Removed the unused private import `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
The direct proof dependency `lem-sfb-left-resolution-additive-finite-coproducts`
is no longer needed by this proof: the existing proved cone comparison already
constructs the isomorphism. This does not withdraw that Mathlib leaf or remove
any upstream declaration. All other original proof dependencies remain, and all
public imports are retained because they form the existing statement interface.
No project module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's five-step calculation is valid but repeats the construction and
naturality already proved upstream. Its source citations and the module docstring
identify exactly the reusable isomorphism and equations. The proof is therefore
a short specialization with no new mathematical result needed. Searches using
leanfinder, loogle and grep confirmed that the generic project comparison is the
appropriate result; Mathlib's termwise cone comparison alone is insufficient.
Edge cases such as the zero complex, identity arrow, odd degree signs,
characteristic two, and unbounded complexes use the same upstream construction;
no additional hypotheses were introduced.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
