## What changed

Proved `CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso_comp` in
`lean/Sheaf/CategoryTheory/DerivedExactSquare.lean`, following the existing DAG plan.
The ordinary pasting identity descends degreewise to bounded-below homotopy categories.
Localization extensionality reduces the derived identity to these objects. After
postcomposing with the three invertible localization factors, naturality and the
existing composition, natural-isomorphism, and square factorization equations reduce
both sides to the localization of the ordinary pasting identity.

All existing declaration signatures, definitions, and docstrings are unchanged.
No new public declarations, modules, nodes, or statement repairs were needed.
The module compiles through lcompile.py in approximately ten seconds with no warnings.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso_comp`
(node `lem-weil-pbc-derived-exact-square-factorization`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
There are no sorries left in the delivered module. `#print axioms` for the completed
theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these unused proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories`, a retired re-export of the source module.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, whose étale-sheaf definitions
  are unnecessary for this theorem about arbitrary abelian categories.

The remaining public exact-functor import supplies the generic derived-category and
homotopy-category definitions and their proved localization API. The generic
DerivedCategory notions recorded by `def-weil-pbc-derived-categories` remain in use;
no planned mathematical step or definition node is bypassed. No other module or node
is asserted to have become unreachable globally.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing natural-language proof accurately describes
the Lean proof, including cancellation of invertible localization factors and the
absence of extra hypotheses. The two imports removed above were redundant for the
stated generic theorem. The proof works uniformly for zero categories and zero objects:
it uses only functoriality, naturality, and cancellation of specified isomorphisms.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
