## What changed

Filled the two theorem proofs in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`.
Added the private proof import
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp`.
For each target, expose the existing finite-type, quasi-compactness and separatedness
instances on the underlying schemes, apply `NatTrans.isIso_iff_isIso_app`, and use
the corresponding component theorem on the square mapped by `Over.forget`.
Explicit corner and morphism arguments avoid typeclass search attempting to infer
instances on unreduced functor applications. Rebundling the square agrees with the
original square by definitional equality and proof irrelevance.

Both existing signatures, attributes, public imports, and docstrings are preserved.
The proof follows the existing node plans verbatim, so no DAG changes are needed.
Loogle found `CategoryTheory.NatTrans.isIso_iff_isIso_app`; source searches found the
already proved component declarations. The final single-file lcompile check passed
without warnings or errors in 14.0 seconds.

## Proved and sorry left

Closed 2 of 2 holes in the assigned module:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`
  (`nt-target-proetale-e`), using
  `isIso_boundedConstructibleBaseChange_continuousMap_app`.
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`
  (`nt-target-proetale-qbar`), using
  `isIso_boundedConstructibleBaseChange_padicAlgCl_app`.

Zero holes remain in the item module. Zero holes are added, and zero statements are
split off. Existing transitive proof obligations in imported modules are unchanged;
this delivery proves the two targets from their already stated component theorems.

## No longer needed

None. No imports, nodes, modules, or unit-route steps are pruned. Both declared
proof dependencies (`new-proper-continuous-basechange-app` and
`new-proper-qbar-basechange-app`) are used through their shared ProperApp module.
Both original public imports remain necessary for the unchanged statements.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is needed. The target nodes already describe exactly
this componentwise assembly. Their proof-origin notes describe the historical
split-off obligations; their component theorem declarations now have complete
proof bodies, although their transitive imported obligations may remain open.
The bundled-to-unbundled application requires explicit local morphism-property
instances and explicit underlying corner/morphism arguments for Lean elaboration.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
