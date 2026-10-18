## What changed

Repaired `Sheaf.Paper.LocalHomTowerCriterion` by removing its duplicate private
`CategoryTheory.telescope_shortExact` declaration and importing the existing generic
telescope theorem from `Sheaf.RingTheory.ModuleLocalizationTowerVanishing`. The existing
module was adapted only to expose that already-proved theorem as a public `lemma`; its
binders and proof body are unchanged. The criterion now calls the library theorem directly.

The previously delivered supporting module
`Sheaf.Algebra.Homology.LocalCoefficientTelescopeDual` remains part of the delivery and
its proof is unchanged. Its public declarations and node remain needed by the criterion.
The criterion and both supporting modules compile with `lcompile.py --all`.

## Proved and sorry left

Closed the returned duplicate-proof issue and retained the proof of
`CategoryTheory.localHom_zero_iff_multiplicationTower_zero`
(node `lem-weil-pbc-local-hom-tower-criterion`). The supporting theorem
`CategoryTheory.localCoefficientTelescope_rhom_product`
(node `lem-weil-pbc-local-coefficient-telescope-dual`) is also proved.
The adapted `Sheaf.RingTheory.ModuleLocalizationTowerVanishing` contains no new `sorry`.
There are zero `sorry`s in the delivered modules and no holes were added.

## No longer needed

The item's local duplicate `telescope_shortExact` helper is no longer needed; the proof
uses the existing generic declaration imported from
`Sheaf.RingTheory.ModuleLocalizationTowerVanishing`. No other proof dependency from the
previous delivery was removed. The prior pruning of the derived-limit existence,
localization-free-resolution, Hom-complex, internal-Hom, pushforward, and termwise-product
imports remains valid; the telescope monomorphism, Grothendieck-abelian, SES-triangle,
ringed-internal-Hom exactness, and telescope-duality dependencies remain in use.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified that the local generic telescope lemma duplicated
a theorem already present in the library, but the existing theorem was private and therefore
could not be imported by name. The repair generalizes that theorem in place by exposing it
without changing its statement or proof, then removes the duplicate declaration. The DAG
proof now records the existing telescope theorem's module as a dependency. No target
statement or mathematical definition changed.

## Forced adaptations

`Sheaf.RingTheory.ModuleLocalizationTowerVanishing` was adapted because the criterion must
call its existing theorem after the duplicate is removed. The original delivery check reported:
`CategoryTheory.telescope_shortExact: same statement as telescope_shortExact in
Sheaf.RingTheory.ModuleLocalizationTowerVanishing; import and use the existing theorem
instead of proving it again, or generalize it in place.` The only changed line in that module
is `private lemma telescope_shortExact` to `lemma telescope_shortExact`; all binders,
statement text, proof lines, imports, and the existing public target theorem are unchanged.

## New nodes

`lem-weil-pbc-local-coefficient-telescope-dual` remains the supporting calculation node in
`dag/nodes/sec-proper-base-change/`; it introduces no unproved statements. The criterion node
now lists `lem-weil-pbc-module-localization-tower-vanishing` as the existing module dependency
that supplies the generalized telescope theorem.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
