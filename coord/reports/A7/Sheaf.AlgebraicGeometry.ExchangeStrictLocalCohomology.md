## What changed

Added `Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomologyStalk`, which states the strict-local geometric-stalk criterion used by the item theorem. The item theorem now imports that criterion and combines it with the existing conservative family of geometric points. The item theorem's proof is complete; the intermediate criterion remains a named theorem with its own DAG node.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.isIso_exchange_iff_strictLocalCohomology` from the local criterion and the geometric-stalk conservativity theorem. Added one strictly smaller named theorem with `sorry`: `AlgebraicGeometry.Etale.isIso_exchange_stalk_iff_strictLocalCohomology`, recorded by node `lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion`.

## No longer needed

The item proof does not use the former direct representative-level imports `Sheaf.Paper.KunBcMapOnCohomology`, `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`, `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`, `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`, `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`, `Mathlib.CategoryTheory.Sites.Point.Skyscraper`, `Mathlib.AlgebraicGeometry.Sites.EtalePoint`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`, `WeilConjectures.SixFunctors.BaseChange.Square`, and `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`; the dependency is encapsulated by the new criterion module and existing conservative-family API.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands the strict-local representative computation inline, but the library already contains the strict-henselization stalk exchange and strict-local total cohomology comparison APIs. The proof can therefore isolate that computation as one strictly smaller criterion and retain the unit route above it.

## New nodes

`lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion` records the intermediate stalk criterion and its remaining proof obligation.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
