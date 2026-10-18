## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_comparison_stalk` without `sorry`. The proof constructs the pro-etale geometric point, identifies its neighbourhood colimit with the existing geometric stalk, applies the general point-comap comparison and transports across the specified comparison adjunction. The same categorical proof handles sets, abelian groups and modules over arbitrary rings. The proof imports the existing upstream point-comap API and the weakly-etale algebraically closed section theorem. A new DAG node records the general site-point comparison used by the route.

## Proved and sorry left

Closed the module theorem `AlgebraicGeometry.Scheme.proEtale_comparison_stalk` (one `sorry` closed). No `sorry` remains in the delivered module. The new node `lem-cbc-site-point-comap-germ` is attached to existing proved declarations and adds no `sorry`.

## No longer needed

Removed the following 17 proof-only imports (all retained public imports are unchanged):

- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`
- `Sheaf.Paper.StrictHenselizationPointedMap`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk`
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`

The following 16 former proof dependencies are pruned from this item's proof route; their modules may still be used by other items:

- `def-weil-pbc-strict-henselization-limit`
- `def-weil-pbc-strict-henselization-structural-map`
- `lem-weil-pbc-strict-henselization-local-structure`
- `lem-weil-pbc-strict-henselization-pointed-map`
- `lem-cbc-proetale-classical-stalk`
- `lem-cbc-comparison-pullback-sections`
- `lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`
- `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`
- `lem-weil-pbc-sets-etale-stalk-finite-limits`
- `lem-weil-pbc-sheaf-algebraic-structures-objects`
- `lem-weil-pbc-abelian-groups-forget-filtered-colimits`
- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-filtered-colimit-modules-elementwise`
- `def-weil-pbc-sites-and-cohomology`

The direct categorical comparison makes the strict-localization evaluation, sections comparison and passage through underlying algebraic structures unnecessary. Sets, abelian groups and modules are specializations of one coefficient-category proof. All seven former `tool_uses` approvals were withdrawn because none is used by the new argument.

The unit record `dag/units/sk-prop-sf-comparison.json` has empty `realized.statement` and `realized.steps` lists. This changes only the route inside `lem-cbc-proetale-comparison-stalk`; the parent `lem-cbc-proetale-stalk-conservative` still receives the same canonical comparison theorem, and the unit's statement and route are unchanged. The dry run flags removal of `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections` for the independent reader to assess; that lemma realizes step 2 of the distinct unit `sk-prop-pe-comparison-morphism`, computing sections on arbitrary weakly etale objects. Its module and node remain in the library and its role in that unit is unchanged. The present stalk comparison is not itself a realization of that unit's statement or steps, and requires only the geometric-morphism interface plus the general point-comap theorem. This delivery does not replace or alter the general sections formula.

## Where the brief, the DAG or earlier work was wrong

The original DAG route was substantially longer than needed. Mathlib's point-comap theorem, together with the existing upstream germ formula, already supplies the canonical comparison for every coefficient category. The only scheme-specific work needed is the geometric lift point and its covering-lifting argument. The item statement and all public signatures are unchanged. The new proof retains the geometric point field and works for an arbitrary ring, including the zero ring; the component isomorphisms live directly in ModuleCat. The empty scheme case has no geometric point and adds no case restriction. Universe enlargement is removed using explicit equivalences and coprojection equations, not an equality of universes. Each private helper is proved. No arbitrary data is selected from an unproved existence theorem.

## New nodes

`lem-cbc-site-point-comap-germ` records the general site-point inverse-image comparison and its unit-germ formula. Its declarations are already supplied by `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` and `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app` in `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap`; no new module is needed.

Validation: the pruned module compiles cleanly through `lcompile.py`. The first `deliver3.py --no-push` passed compilation, the axiom probe and preflight (CODEX review class). The primary new-node signature was checked against the existing upstream declaration, and the general coefficient comparison against Mathlib's full signature. The axiom probe found no nonstandard axiom in any delivered declaration.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
