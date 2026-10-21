## What changed

Completed all six proofs in `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness`.
Reused `siteConstantModuleFunctorGeneral_exact` for the constant functor. The stalk
functor is additive and exact by the proved constant-scalar equivalence followed by
Mathlib's point fibre. Mathlib's homology comparison and exact-map APIs give natural
cohomology comparisons and preservation of acyclicity and quasi-isomorphisms.

Constructed the normalized natural module isomorphism from the actual module
sheafification unit, whose underlying map is locally bijective. Point fibres invert
that map; the constant-presheaf fibre comparison supplies its source. Coprojection
naturality proves exactly the required germ formula. Lifted this natural isomorphism
termwise to complexes. The regular module uses the ring unit and its multiplicativity,
so the ordinary A-action and specified germ formula are preserved.

All helpers are private and fully proved. Existing public signatures, definition
bodies and attributes are unchanged. Removed the unused public import of
`Mathlib.Algebra.Homology.DerivedCategory.Basic`; no statement uses derived categories. Updated the item's DAG proof and
dependencies to this route. Change record:
`coord/changes/J5-etale-constant-stalk-proof-context.md`.

## Proved and sorry left

Closed all 6 original holes:

- `AlgebraicGeometry.Scheme.etaleConstantComplexFunctor_additive`;
- `AlgebraicGeometry.Scheme.etaleConstantModuleStalkFunctor_additive`;
- `AlgebraicGeometry.Scheme.etale_stalk_constant_exact`;
- `AlgebraicGeometry.Scheme.etale_stalk_constant_cohomology`;
- `AlgebraicGeometry.Scheme.etale_stalk_constant_preserves`;
- `AlgebraicGeometry.Scheme.etale_stalk_constant_complex_retraction`.

Zero holes left and zero holes added; no split-off statements or new axioms.

## No longer needed

Removed the redundant public import `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
The remaining public homology imports supply all complex and homology signatures.

Removed private imports:

- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`;
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The direct proof no longer uses `lem-weil-pbc-constant-sheaf-geometric-stalk` or
`lem-weil-pbc-module-sheaves-colimits-forgetful`; their two obsolete tool-use approvals
were removed from this node. No source-library declaration or module is withdrawn.
The constant-presheaf connected-colimit comparison is imported directly from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf` instead.

The standalone fixed-ring sheafification-exactness dependency
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` is unnecessary directly:
the already proved general constant-realization exactness theorem gives exactly the
needed genuine sheaf-of-modules result. Module-sheafification itself remains needed
for its canonical unit. `def-weil-sheaf-of-modules-category` remains a statement
dependency, rather than a separate proof step. The remaining public imports are
needed for the exposed statements and definitions.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its reflection through underlying
abelian sheaves is unnecessary: the proved constant-scalar restriction equivalence
and exact point fibre work directly with modules. The normalized retraction similarly
uses local bijectivity of the actual sheafification units, avoiding a transport from
an abelian constant-stalk isomorphism. The unit route and every statement are unchanged.

Mathlib searches were run through msearch.py (Lean Finder, Loogle, grep), followed by
reading the actual general exactness, point fibre, connected-colimit, module unit and
homology declarations. Source checks used Stacks `sites-modules.tex`,
`lemma-sheafification-exact` (03EI), `lemma-stalk-exact-modules` (04EQ), and
`etale-cohomology.tex`, `lemma-stalk-exact` (03PT). Edge cases are retained: zero ring,
zero modules, arbitrary unbounded complexes and empty schemes (for which there is
no geometric point). No new statement needs an additional mathematical assumption.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
