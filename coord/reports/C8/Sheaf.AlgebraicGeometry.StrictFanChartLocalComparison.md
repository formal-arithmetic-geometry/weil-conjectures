## What changed

Replaced the proof hole of `AlgebraicGeometry.strict_fan_chart_local_comparison` by a
complete assembly from the existing point-localization and affine universal-property
theorems and two strictly partial bridge statements. The theorem's statement, the
`SharpSpaceMap` definition, its `map` definition, and `PointLocalization` are unchanged.
No existing module other than the assigned item is changed.

The item proves the germ/stalk-map identity, stalk-map identity and composition,
locality of bijective stalk maps, sharpness transported by a monoid equivalence,
sharpness of affine stalks, the affine isomorphism induced by a monoid equivalence,
and conversion of the existing localization theorem to the exact normalization
required by `PointLocalization`. In particular, both inverse fan morphisms are
constructed from `affine_hom_universal`, and injectivity proves the inverse identities.
The actual equivalence is `ac.trans (af.trans ad.symm)`; its normalization is proved
by `ad.apply_symm_apply`. The isomorphism on localized opens is conjugated by the
supplied chart coordinates, and functoriality of global sections proves its required
section formula. These are proved private helpers, with no holes.

Added proof imports `FineFanPointLocalization`, `StrictSharpSpaceSections`, and
`AffineOpenGermComparison`. The two new modules have one public statement each.
The first supplies the normalized characteristic map independently of any fans.
The second only spreads an already supplied affine isomorphism and already supplied
stalk homomorphism; it neither constructs them nor assumes strictness. The main proof
constructs those objects and verifies the hypotheses before applying it.

Source checked: ILO VIII 3.1.1--3.1.10, printed pp.98--100, and the point-local
paragraph of proof 3.3.15, printed p.109 (PDF pp.104--106 and 115). The unit record
`sk-i-curve-zero` has no realization by this supporting node; its route is unchanged.

Validation: both new modules compiled individually and in the import-order run of
`lcompile.py --all`. After correcting the germ helpers, the final assigned module
compiled successfully against those compiled siblings in 21.0 seconds, with no compiler warnings. The original theorem
signature was also compared verbatim with the shared source and is unchanged.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.strict_fan_chart_local_comparison`
(`lem-trf-strict-fan-chart-local-comparison`). There are zero holes in the item module.

Added two named holes, each with its own source-based proof and DAG node:

- `AlgebraicGeometry.strict_sharp_space_sections`
  (`lem-trf-strict-sharp-space-sections`): the germ-normalized characteristic map of
  `strictLogBlowupCartesian` must be transported to the exact underlying base map and
  normalized on every relative log section by sheaf separation.
- `AlgebraicGeometry.FineFan.affine_open_germ_comparison`
  (`lem-trf-affine-open-germ-comparison`): restriction through the two opens and transport
  of the given normalization equations to the existing affine germ-rigidity theorem.

This is a decomposition, not an unconditional proof or a net decrease of holes:
one upper hole closed and two strictly smaller bridge holes added. No holes are
hidden in private helpers or definitions. Existing dependencies still containing
`sorry` are used as intended by stage 3, and none of their proofs is changed.

## No longer needed

None globally. No existing public import is removed and no module is withdrawn.
The direct proof edges to `lem-trf-strict-log-blowup-cartesian` and
`lem-trf-affine-fan-germ-rigidity` are replaced by the two bridge nodes, which still
need those original dependencies. This is not pruning them. The chart existence and
blowup-tower clauses of `log_fan_chart_blowup` are unnecessary for this local theorem;
its `LogFanChart` structure and stalk-bijection fields remain essential, so its
module and node are retained. The affine localization sections theorem is now used
explicitly to obtain sharpness of affine stalks.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false and no signature was weakened. Two API
mismatches require the bridge statements: the strict pullback theorem normalizes on
germs, while this item demands normalization on relative sections; and the affine
germ-rigidity theorem is on an open subspace, while the conclusion requires an open
of the original scheme and all factorization triangles. These are independent parts
of the stated argument, not renamed versions of the item.

Mathlib's general presheafed-space stalk-map lemmas require all colimits of the value
category. This project's `CommMonCat` stalks use only its explicit filtered-colimit
instance, so those lemmas cannot simply be invoked. The needed germ, identity and
composition laws are instead proved directly using `colimit.ι_map`, `colimit.ι_pre`
and `colimit.w`; no colimit axiom or new instance is introduced.

Edge cases checked in the two new statements: the trivial monoid is included and
requires no nonempty generating list; the empty open obeys section normalization
by sheaf separation; an empty source makes the stalk assertion vacuous; identity
strict maps obey the given section formula; and the spreading lemma needs no
invertibility of its monoid homomorphism because the isomorphism of affine opens
is supplied separately. Full sheafed-space morphism equalities are retained.

## New nodes

`lem-trf-strict-sharp-space-sections` records only the characteristic-map construction
and section normalization, with `lem-trf-strict-log-blowup-cartesian` as its proof
dependency. It is independent of fan charts. Its module is
`Sheaf.AlgebraicGeometry.StrictSharpSpaceSections`.

`lem-trf-affine-open-germ-comparison` records only the restriction and spreading of a
given affine comparison, with `lem-trf-affine-fan-germ-rigidity` as its proof dependency.
Its input contains the affine isomorphism and section formula that the item proves
using the universal property. Its module is
`Sheaf.AlgebraicGeometry.AffineOpenGermComparison`.

Both have LeanSearch, LeanFinder and Mathlib grep searches recorded. Project and
blueprint searches found the existing dependencies but no exact bridge. No change
record is needed: this delivery changes no existing statement or definition.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
