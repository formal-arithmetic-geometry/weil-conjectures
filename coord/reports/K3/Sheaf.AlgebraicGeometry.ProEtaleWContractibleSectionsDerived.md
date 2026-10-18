## What changed

Completed `AlgebraicGeometry.Scheme.ProEt.wContractible_sections_derived` without changing
its statement, definitions, universes or public imports. The proof follows the existing
four-step DAG plan. Exact evaluation gives Mathlib's induced derived functor and its
factorization through the homotopy category. For a K-injective resolution, naturality
of the recorded derived-sections unit and cancellation of isomorphisms prove that the
specified unit component is invertible. Applying that comparison to a sheaf concentrated
in degree zero reduces positive cohomology to `isZero_single_obj_homology`.

Added proof imports of `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`Mathlib.Algebra.Homology.SingleHomology`. All construction data remain unchanged.
The proof uses the existing named exactness and K-injective-unit theorems; their
remaining upstream holes are the intended dependencies of this stage.

On resuming the retained attempt, repaired the explicit isomorphism instance for
the image of the localized resolution under the derived functor. The final module
compiled through `lcompile.py` with exit code 0 and no diagnostics (4.8 seconds).

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.Scheme.ProEt.wContractible_sections_derived`
(node `det-pe-wc-sections-derived`). Both clauses are proved in Lean from the existing
dependency declarations. Original holes: 1; closed: 1; added: 0; remaining in this
delivery: 0. No split-off theorems.

## No longer needed

Removed the proof-only import `Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`:
the argument uses only abelianness of the section-module category, already supplied
by the retained imports, and never uses enough injectives of ModuleCat.
No DAG node or Sheaf/WeilConjectures module is bypassed or withdrawn. In particular,
`lem-weil-pbc-ring-modules-enough-injectives` is still used for its abelian-category
clause, exactly as specified in the original plan. Grothendieckness and K-injective
resolutions remain used by the existing resolution helper. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The explicit kernel/image computation of
step 2 is already available in Mathlib's exact-functor and homology-preservation API.
The unit-cancellation argument follows step 3, and the last clause follows step 4.
Read the current blueprint unit and item proof, and the cited Stacks labels
`lemma-right-derived-exact-functor`, `lemma-K-injective-defined`,
`lemma-enough-K-injectives-implies` and
`theorem-K-injective-embedding-grothendieck` in the local literature.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
