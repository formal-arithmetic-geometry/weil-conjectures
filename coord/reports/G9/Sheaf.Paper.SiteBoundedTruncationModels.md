## What changed

Proved `SheafOfModules.exists_site_bounded_truncation_models` with its original
signature and public imports unchanged. The proof transports the good lower
truncation to module-valued sheaves, applies the existing bounded constant-model
theorem on the comapped slice site, transports across the iterated-slice equivalence,
and extends the resulting covering family to a covering sieve. Natural comparisons
on entire complexes retain the model differentials.

Added the fully proved `CategoryTheory.site_moduleSheaf_restriction_equivalence`
to `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`, exposing the
constructive inverse with natural comparisons for constants and arbitrary slice
restrictions. Its original public theorem and public imports are unchanged.
Change record: `coord/changes/G9-site-module-sheaf-restriction-interface.md`.
The existing equivalence node now lists both declarations; both node proof plans
follow the Lean argument. No unit route changes.

## Proved and sorry left

Closed the one original hole in the assigned module:
`SheafOfModules.exists_site_bounded_truncation_models`
(node `lem-weil-pbc-site-bounded-truncation-models`).
Added zero holes and split off zero obligations. Both delivered Lean modules have
zero `sorry`. The added inverse interface and all private helpers are proved.
The existing dependency `CategoryTheory.exists_site_bounded_constant_model`
remains the intended stated dependency, together with its transitive dependencies.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: use Mathlib's precoverage and
  generated covering-sieve APIs directly.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: Mathlib's good-truncation
  homology API suffices; no homotopy colimit is used.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems` and
  `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`: the final
  ring-sheaf comparison is on complexes; its restriction functor only needs
  preservation of zero morphisms, already provided by the public statement imports.
  Node `lem-pur-site-restriction-module-adjunction-exact` is not needed here.

Retain `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`,
`Sheaf.Paper.SiteBoundedConstantModel`, and the natural constant-restriction API
in `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
Added the proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` for the
induced derived equivalence. No other node or module is pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original equivalence interface did
not expose compatibility of the inverse equivalence with arbitrary slice
restriction, which the transport argument needs. The added theorem constructs
and proves that interface using the existing sheafification counit and units.
No data is chosen from an unproved mere-existence theorem. The upper bound
`max a b₀` handles a cutoff above the original bound without a separate case.
Empty covers and the zero ring remain allowed. Models are built on the slice
precoverage, so no terminal object of the original site or points are assumed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
