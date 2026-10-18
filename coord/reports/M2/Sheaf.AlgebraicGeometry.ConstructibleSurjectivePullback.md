## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback`
in `Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback`, with its original signature.
The proof implements the Stacks 095Q quotient-and-kernel argument. The existing source
comparison theorem supplies the finite-values/finite-stalk bridge; the existing constructible
pullback theorem supplies the forward direction; faithful surjective pullback reflects the
split epimorphism obtained using filtered-colimit factorization. The second presentation
applies to the kernel, and the final cokernel is identified by Mathlib's abelian-category API.
No definition, existing instance, public import, or declaration signature changed.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective`.
Updated the item's docstring and DAG proof/dependencies to this implementation.
The proper-base-change unit statement and its realized steps are preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback`
(node `lem-weil-pbc-etale-constructible-surjective-pullback`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses existing declared dependencies; their remaining transitive obligations are
not new holes. Single-file compilation passed cleanly in 4.1 seconds. The empty-scheme and zero-ring cases require no separate choices: filteredness
supplies an index, the colimit argument applies to zero objects, and the faithful-pullback
lemma requires only the existing surjectivity hypothesis.

## No longer needed

Removed these proof-only imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: the source pullback theorem
  already proves constructibility of the inverse-image strata.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` and
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: the theorem already uses
  the module-valued `Etale.upperStar`, with its exactness and adjunction API.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`: no transport through
  the separate constant-ring `SheafOfModules` encoding is needed.
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`: used through the
  proved constructibility comparison, with no direct application here.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`: no explicit construction of
  pulled-back strata is needed in this proof.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: the proved faithful-pullback theorem packages
  the stalk argument directly for module sheaves.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: its public canonical upstream
  definition is already imported directly.

The following former proof dependencies are no longer direct dependencies of this item:
`lemma-constructible-pullback-stratification`, `lem-pur-scheme-constructible-preimage`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-inverse-image-composition-module-linear`,
`lem-weil-pbc-finite-locally-constant-module-values`,
`lemma-constructible-pullback-locally-constant`, `lemma-constructible-pullback-finite`,
`def-weil-pbc-etale-constructible-sheaf`,
`lem-weil-pbc-inverse-image-stalk-germ`, and `lem-weil-pbc-sets-etale-iso-on-geometric-stalks`.
The definition dependency stays in stmt_deps, and the comparison, pullback, and faithfulness
lemmas still use the relevant value, stratification, and stalk results transitively.
This is removal of direct dependencies/imports; global unreachability is left to the ledger.
Obsolete direct tool approvals for module exactness, composition transport, stalk germs,
and finite locally constant module values were removed from this node's tool_uses list.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or the Stacks route was found. The original plan
expanded some arguments that the source library now proves directly: finite-value comparison,
constructible pullback, and faithful surjective module pullback. In particular no bridge to
the separate constant-ring `SheafOfModules` encoding is required for this statement.
The comparison node's lean record still names the earlier Sheaf wrapper; its current
lean_audit identifies the proved canonical upstream theorem used here.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
