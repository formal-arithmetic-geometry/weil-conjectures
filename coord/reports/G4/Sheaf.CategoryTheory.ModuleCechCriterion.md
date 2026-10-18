## What changed

Proved `CategoryTheory.module_cech_acyclicity_criterion` in
`Sheaf.CategoryTheory.ModuleCechCriterion` with its signature and existing docstring unchanged.
Private, proved helpers reindex chosen Čech products and transport positive exactness across
`ULift`. This is necessary because the finite families in the conclusion have index universe
zero, while the hypotheses `products` and `hrefine` and the presheaf lifting theorem use the
common universe.

The first clause follows from injective module-presheaf cocycle lifting. For the second,
the exact underlying-abelian-sheaf functor and the existing Čech H¹ lifting theorem give
surjective sections on basis objects. Products of these sequences give short exact Čech
complexes on the chosen products in the basis, and the homology sequence proves the quotient
again has positive Čech vanishing. Product comparison transports this to any `SiteCechComplex`.
The existing `Functor.rightAcyclic_of_epi_map_g` packages precisely the final dimension-shifting
induction; `InjectiveResolution.isoRightDerivedObj` computes it on the resolution in the goal.
Updated the existing node's proof and dependencies to record this packaging.

Only the assigned module and its existing DAG proof record change. No public signature,
definition or public import changed; no consumer adaptation or change record is needed. The
`hbasis` hypothesis is retained unchanged (the finite-refinement argument suffices here).

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.module_cech_acyclicity_criterion`
(node `lem-weil-pbc-cech-criterion`). Added zero holes; zero holes remain in the item.
All three private helpers are fully proved. This is a proof, not a decomposition.

The full file compiled successfully through `lcompile.py` after implementing both clauses.
The final pruned version and delivery axiom probe are checked by the delivery tool.
The proof handles empty finite families, degree one, arbitrary positive degree, an empty
basis, repeated ordered indices, and arbitrary choices of products without extra hypotheses.

## No longer needed

Removed these redundant proof imports:

- `Sheaf.CategoryTheory.InjectiveModulePresheaf`: retired forwarding module; use
  `WeilConjectures.CategoryTheory.InjectiveModulePresheaf` directly.
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`: retired forwarding module.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`: the explicit
  full-long-exact-sequence interface is unnecessary when using the existing proved
  `Functor.rightAcyclic_of_epi_map_g` criterion.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: already available through the
  needed module-presheaf injectivity theorem; no direct use of its interface here.
- `WeilConjectures.CategoryTheory.SiteCechComplex`: already publicly reexported by the
  statement import `Sheaf.CategoryTheory.SiteCechComplex`.

The explicit direct dependencies `lem-weil-pbc-derived-functor-long-exact` and
`lem-weil-pbc-derived-functor-injective-vanishing` are replaced by
`lem-pc-right-acyclic-of-epi-map-g`; they remain mathematical inputs to that generic theorem.
The obsolete direct tool approval for the former is removed from the node's `tool_uses`.
All remaining declared dependencies are used, including the underlying-module abelian
structure, sheafification, Grothendieck/enough-injectives input, section lifting, cocycle
lifting, chosen Čech products and the complex homology sequence. No source module is withdrawn.
The unit's own statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The original plan omits the universe transport needed
for `Fin m`: it cannot be passed directly as the `Type u` index argument of `products`.
The proof lifts the finite family to `ULift.{u} (Fin m)` and proves that its exactness and
covering presieve agree with those of the original family. The plan also needs transport
from the products chosen by `products` (known to lie in B) to the arbitrary products quantified
in the conclusion; the existing comparison theorem supplies it.

The generic dimension-shifting criterion was already proved in the source library and
attached to `lem-pc-right-acyclic-of-epi-map-g`, so no new theorem or node is necessary.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
