## What changed

Proved `CategoryTheory.Mod.coextendScalarsIsoComapInv_formula` in
`Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula`, following all five
existing DAG proof steps and the unit route unchanged.

The inverse-restriction equivalence has identity underlying counit.
`Adjunction.rightAdjointUniq_hom_app_counit` therefore identifies the comparison's
forward component with `coextendCounitHom`, the stated evaluation at the unit.
For its inverse, `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` with the
adjunctions exchanged, together with `coextendHomEquiv`, identifies the component
with `coextendHom` applied to that identity counit. Uncurrying and applying
`whiskerLeft_coextendHom_hom_coextendEv` gives the transported action.
Monicity of `coextendι` proves uniqueness among all underlying arrows.

Removed the unused public RingPresheaf import and redundant private
Adjunction.Basic import. The import change and empty current consumer list are
recorded in `coord/changes/K3-coextension-evaluation-import-pruning.md`.
All theorem signatures and existing docstrings remain verbatim.
The final module, including the pruned imports, compiles cleanly through
`lcompile.py` (exit 0, 5.7 seconds); its theorem signature was also checked
verbatim against the repository source.

## Proved and sorry left

Closed 1 of 1 existing holes:
`CategoryTheory.Mod.coextendScalarsIsoComapInv_formula`
(node `lem-sfb-coextension-iso-evaluation-formula`).

Holes added: 0. Split off: 0. Holes remaining in the delivered module: 0.
The proof uses existing proved constructions and Mathlib lemmas; there are no
new intermediate statements or postponed proofs.

## No longer needed

Removed imports:
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`: neither the generic
  internal-module statement nor its proof uses presheaves or sheafification.
- `Mathlib.CategoryTheory.Adjunction.Basic`: its required API is already supplied
  by `Mathlib.CategoryTheory.Adjunction.Unique`.

No declared DAG proof dependency is discarded: the scalar restriction and
module-object definitions, inverse-restriction equivalence and its adjunction,
coextension adjunction and equalizer construction, and right-adjoint uniqueness
are all used. No library module is withdrawn. The unit still requires this item,
even though it currently has no Lean importers.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing five-step DAG plan is
realized directly. The item originally imported RingPresheaf despite having no
presheaf-specific statement or proof requirement.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
