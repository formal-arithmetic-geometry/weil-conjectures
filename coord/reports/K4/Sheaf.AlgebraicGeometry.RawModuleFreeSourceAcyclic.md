## What changed

Retired `Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic`, as explicitly listed
in `coord/retire-items.tsv`. Reattached
`lem-sbc-raw-module-free-source-acyclic` to the existing canonical theorem
`AlgebraicGeometry.Etale.rawModuleFreeSource_acyclic` in
`WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceAcyclic`.

The former signature uses `RawModuleScalarComparison.forget`; this is an abbrev
of upstream's `moduleAbelianForget`. A scratch example with the former signature
compiled by applying the upstream theorem directly (8.8 seconds, no warnings).
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The scratch file stays outside the delivery's Lean tree.

The change record is
`coord/changes/K4-retire-raw-module-free-source-acyclic.md`.

## Proved and sorry left

Zero of zero holes closed in the assigned module; zero holes added or split off.
No sorry remains in the withdrawn module. The canonical upstream theorem is
already proved, including its transitive axiom audit. This is a duplicate
retirement repair, not a newly proved theorem or a decomposition.

## No longer needed

The module `Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic` and its duplicate
public theorem and private `rawSourceSectionsEquiv` / `rawSourceSectionsIso`
helpers are no longer needed. Its three public imports and two private proof
imports are removed with the module:

- `Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`
- `WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso` (`import all`)
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
  (`import all`)

No mathematical dependency node is pruned. The existing proof dependencies
`lem-sbc-injective-module-forget-evaluation-acyclic` and
`lem-weil-pbc-sheaf-free-separator` stay attached, and the upstream proof still
uses the represented sections and evaluation acyclicity argument. Both actual
parents, `WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapInjective` and
`WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapSurjective`, already
import the upstream module. Their DAG dependencies remain unchanged. There are
zero current importers of the Sheaf copy, including quarantined sources.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a hole, but the current item is a listed
zero-hole twin retirement. Its DAG attachment still pointed at the duplicate
Sheaf declaration even though both parents already use the upstream theorem.
The upstream statement's only textual difference is the definitionally equal
name for scalar forgetting, so no weaker statement, new lemma, parent rerouting,
or unit-route change is required. The source proof was checked against Stacks
`sites-cohomology.tex`, `lemma-cohomology-modules-abelian-agree` (Tag 03FD),
especially the second paragraph on injective module sheaves. The complete
upstream proof preserves that same sections-adjunction and acyclicity argument.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
