## What changed

Proved `AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk` with its original
statement and public imports unchanged. Three proved private helpers establish germ
injectivity, specialization injectivity, and specialization semilinearity.

The proof imports the existing proved stalk trivialization and integral-section vanishing
results. Generic rank one follows by transporting a singleton basis; a generating stalk
vector has nonzero generic image and hence gives a field basis. Semilinearity gives the
stalk-image formula. For the section-image formula, choose local representatives of stalk
preimages directly, prove agreement on overlaps by generic-germ injectivity, and glue.

Updated the item's node to this shorter route. Added a DAG attachment for the existing
proved integral-section vanishing theorem; no Lean declaration or module was added for it.
The unit statement and its realized steps remain intact.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.invertible_module_generic_stalk`
(node `lem-sc-invertible-module-generic-stalk`).

Added 0 holes. Split off 0 holes. No `sorry` remains in any delivered Lean file.
The new DAG attachment names the already proved
`AlgebraicGeometry.Scheme.Modules.eq_zero_of_presheaf_map_eq_zero`.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.FunctionField`;
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`;
- `Sheaf.CategoryTheory.RingedSiteModules`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

The first three provided no theorem needed by the final argument. The last two define
interfaces for general sites; ordinary topological-sheaf gluing suffices here. Their notion
nodes remain proof dependencies where appropriate for the mathematical sheaf condition;
the corresponding general-site Lean declarations are unused.

Removed direct proof dependencies:
- `def-sc-invertible-module`: used through the existing proved stalk and vanishing tools;
- `lem-sc-integral-scheme-stalks-in-function-field`: used below the vanishing tool;
- `lem-weil-pbc-sheaf-sections-determined-by-germs`: used below the vanishing tool;
- `lem-sc-function-field-sections-glue`: unnecessary. A local preimage in each module stalk
  already has a section representative; use those representatives and glue directly.

No library module is withdrawn. These nodes can still be needed by other consumers or
by the imported proved tools.

## Where the brief, the DAG or earlier work was wrong

The original nine-step argument was valid but longer than necessary. In particular the
function-field section-gluing step repeated work: the hypothesized module-stalk preimage
already supplies a local section. The existing public theorem docstring describes that
valid original argument; the node now describes the actual shorter Lean proof.

Two proved source-library tools were available: `invertible_stalk_linearEquiv` and
`eq_zero_of_presheaf_map_eq_zero`. The first already had a DAG node; the second had no
attachment, so this delivery records one. The cross-unit stalk result is a generic tool,
used only to transport a basis, and its proof is already complete.

No statement, definition, target, unit route, or source-library file changed.

## New nodes

`lem-sc-invertible-section-zero-on-nonempty-open` records the existing proved theorem in
`WeilConjectures.AlgebraicGeometry.Modules.IntegralSections`. On an integral scheme, a
section of an invertible module vanishing on a nonempty subopen is zero. The node records
the local trivialization, cancellation, integral restriction-injectivity and sheaf
separation proof. The statement applies to arbitrary opens and requires no properness,
noetherianity or affine hypothesis. No new Lean statement or change record is needed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
