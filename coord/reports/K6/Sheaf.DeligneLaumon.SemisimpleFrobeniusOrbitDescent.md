## What changed

Replaced `exists_semisimple_frobenius_orbit_descent`'s hole by a complete assembly proof,
with its statement unchanged. The proof constructs the finite extension inside the algebraic
closure using the proved source theorem
`ProEtale.CondensedRing.exists_intermediateField_natCard_eq_pow`, forms the actual scheme
pullback, and transports each power-return summand through the canonical geometric-fiber
isomorphism using `IsoAlgebra.mapOfNatIso`. It proves that pushforward along this isomorphism
preserves irreducible local systems by transporting a lisse subobject through the inverse
equivalence. It then transports the biproduct isomorphism and lifts it through the full
constructible subcategory. Finally it applies the pairwise stalk lemma to the monic summand
inclusions. All three new imports are private proof imports. No existing signatures, definitions,
source-library declarations, consumers, or public imports changed.

The two remaining arguments are isolated as `GeometricPowerOrbit` (a decomposition on the
original geometric fiber, without choosing any constant extension or comparing stalks) and
`GeometricPowerOrbitStalk` (a local comparison for two supplied embedded power algebras,
without simplicity, semisimplicity, or any decomposition hypothesis). These are separate
strict parts of the original three-step argument, not a renamed version of the assigned
statement. In particular the cartesian-model and equivariant-descent step is proved here.

## Proved and sorry left

The original hole of
`AlgebraicGeometry.WeilSheaf.exists_semisimple_frobenius_orbit_descent`
(node `lem-zl-semisimple-frobenius-orbit-descent`) is replaced by a complete proof from two
new statements. Its module has zero remaining holes. The proved private helpers
`lisse_lowerStar_iso` and `irreducible_lowerStar_iso` establish preservation of lissity and
irreducibility under the explicit geometric-fiber equivalence.

Two holes are added, each as exactly `:= by sorry` in its own new module:

- `AlgebraicGeometry.WeilSheaf.exists_geometric_power_orbit`,
  node `lem-zl-geometric-power-orbit`.
- `AlgebraicGeometry.WeilSheaf.exists_stalk_equiv_of_power_orbit`,
  node `lem-zl-geometric-power-orbit-stalk`.

This is a decomposition: one original hole removed, two strictly smaller holes added;
zero of the original holes closed without additional holes. The closed-minus-added
ledger change is -1; the total hole count increases by one.
No data definition contains a hole or chooses arbitrary data from an unproved theorem.

Validation: `lcompile.py --all` compiled both new statement modules after import pruning
in 6.2 s and 7.2 s. A final `lcompile.py` run compiled the main module without errors or
warnings in 8.1 s. The original signature was compared verbatim, all Lean lines are within
100 characters, and every node's proof dependencies equal the union of its steps' uses.
Final delivery compilation and preflight are run by `deliver3.py`.

## No longer needed

No existing imports were removed; the original sole public import remains verbatim.
The two new modules import the specific source modules needed by their statements, rather
than the aggregate `Sheaf.DeligneLaumon.ConstantFieldRestriction`: respectively
`WeilConjectures.WeilSheaf.BaseChangeField.Transport`, and Transport together with
`WeilConjectures.WeilSheaf.BaseChangeField.Geometric` and `WeilConjectures.WeilSheaf.Stalk`.
The main proof no longer directly uses these originally declared proof dependencies:

- `lem-zl-geometric-constituents-any-base`
  (`WeilConjectures.RepresentationTheory.Clifford`): its attached declaration gives an abstract
  filtration, not a decomposition of the supplied geometric sheaf with return-compatible
  inclusions. The narrower geometric orbit statement carries that argument instead.
- `lem-wf-schur-scalar`
  (`WeilConjectures.Mathlib.RepresentationTheory.Irreducible`): used by the new geometric
  orbit node's proof plan, rather than by the descent assembly. It is still needed there.
- `lem-wf-weil-group-constant-extension`
  (`WeilConjectures.EtaleCohomology.Purity.RealSheaves.ConstantExtension`): no Weil-group
  construction is used; the existing source geometric-fiber isomorphism and iterated
  return transport give the descent directly.
- `def-weil-local-frobenius-trace`: the actual local calculation is now the pairwise stalk
  node's responsibility; it remains a statement dependency and a dependency of that node.

The finite-extension existence helper already has a complete source proof. It is recorded
as `lem-zl-finite-constant-extension-exists` with `existing: true`; no Lean statement is added
or restated. The stronger `lem-weil-unique-subfield-of-closure` additionally proves a
root-set formula and uniqueness, and neither its theorem nor its module is needed here.
The source helper constructs the field as the range of an embedding of
`FiniteField.Extension`, then uses `FiniteField.natCard_extension` for its cardinality.

No existing modules are withdrawn or claimed globally unreachable. The unit's own
`lem-zl-geometric-constituents-any-base` realization and every upstream declaration remain.

## Where the brief, the DAG or earlier work was wrong

The old proof dependencies are useful mathematical background but do not directly furnish
the source-category interfaces required by the old proof steps. In particular
`Representation.exists_filtration_isIrreducible_restrict` is a theorem about a
finite-dimensional group representation and a normal subgroup; it does not supply source
sheaf summands, an equivariant source biproduct, or the deck-related stalk comparison.
The new statements specify the two missing interfaces. The original statement is not
changed and no disputed or weaker substitute is used.

Edge cases checked mathematically: a zero-length geometric decomposition is impossible for
the supplied nonzero simple V; one summand permits power one; a zero orbit iterate is the
identity; the stalk comparison for identical embedded summands allows t'=t. The pairwise
lemma applies to arbitrary constructible power-return subobjects and needs no smoothness,
normality, or extra lissity assumption. For X a finite-field point the orbit has one
geometric simple factor and the local assertion reduces to the same scalar return.

The blueprint ancestor tool could not follow the original node's module-valued
`created.item`; the new nodes use the original node's explicit ancestor
`thm-zl-real-mixed-by-curves` and preserve its intervening ancestor chain. No tool was edited.

## New nodes

`lem-zl-geometric-power-orbit`, in `Sheaf.DeligneLaumon.GeometricPowerOrbit`, isolates the
isotypic-block and multiplicity-eigenline argument on the original geometric fiber. Its
return-equivariant inclusions retain the information needed for the separate local
calculation. Source: the current blueprint's geometric-constituents proof, paragraphs 1--2.

`lem-zl-geometric-power-orbit-stalk`, in `Sheaf.DeligneLaumon.GeometricPowerOrbitStalk`,
compares the local Frobenius modules of two supplied power-return subobjects whose
inclusions are related by a power of the original Weil map. It does not construct or assume
a decomposition. Source: the geometric orbit step of `sk-i-dl-general-real` and the local
power comparisons in `thm-zl-real-mixed-by-curves`.

For each node, LeanSearch, LeanFinder or Loogle, and Mathlib grep were actually run via `msearch.py`;
the exact queries and results are recorded in its JSON. Project and blueprint searches
found no theorem with either interface. No change record is needed because no existing
statement or definition changes.

`lem-zl-finite-constant-extension-exists` attaches the existing proved source declaration
`ProEtale.CondensedRing.exists_intermediateField_natCard_eq_pow` in
`WeilConjectures.TraceFormula.ModelExtension` (lines 50--59). It records only the
finite-extension existence assertion actually used by the proof. No new Lean module,
statement, hole, or source edit is added for this node. Its Mathlib searches were run and
recorded separately. The stronger existing unique-subfield node was read and retains
its original statement and attachment.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
