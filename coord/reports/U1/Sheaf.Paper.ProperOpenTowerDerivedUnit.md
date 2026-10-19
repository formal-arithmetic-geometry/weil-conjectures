## What changed
Proved `AlgebraicGeometry.Etale.properOpenTowerDerivedUnit` without changing its statement or any existing definition. The proof constructs lifts and comparison maps using the proved upstream K-injective resolution API, proves uniqueness and naturality up to homotopy, transports quasi-isomorphisms through homotopy equivalences, and proves independence of the chosen resolutions after localization.

Added two fully proved formula modules, `Sheaf.Paper.ProperOpenTowerSingleUnitFormula` and `Sheaf.Paper.ProperOpenTowerSuccessiveUnitFormula`. They compute the two canonical derived-unit expressions using unit naturality, exact open-extension localization comparisons, and the proved upstream composition/conjugacy API. Updated the three node records to describe these proofs. All three files compile, and every Lean line has at most 100 characters.

Revalidated the retained delivery against the current sources on 2026-10-19 using `lcompile.py --all`: all three modules compiled successfully. Compared the original theorem signature verbatim; it is unchanged. Checked that each node's `proof_deps` is the union of its proof steps' `uses`.

The two formula lemmas require no boundedness, properness, Noetherian, or finite-coefficient hypothesis: their proofs use naturality and K-injectivity alone. For zero complexes or the zero coefficient ring all displayed maps are the unique maps; identity composition maps cancel as in the proofs. These edge cases introduce no additional assumption or exceptional case.

## Proved and sorry left
Closed the one original hole: `AlgebraicGeometry.Etale.properOpenTowerDerivedUnit` (node `lem-sfb-proper-open-tower-derived-unit`).

The new declarations `AlgebraicGeometry.Etale.properOpenTowerSingleUnitFormula` and `AlgebraicGeometry.Etale.properOpenTowerSuccessiveUnitFormula` are also proved completely. These were temporary splits in the retained sandbox and were proved before delivery. No holes are split off or added; zero `sorry` occurrences remain in all three delivered Lean files. The theorem still uses the existing proper/open interchange theorem; this delivery does not claim to close its dependencies.

## No longer needed
Removed `import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the existing upstream `CochainComplex.KInjectiveResolution` API and total-right-derived unit API suffice, so the proof no longer needs node `def-sfb-right-derived-functor`.

Removed the redundant direct import `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`; the existing derived lower-shriek import supplies its definitions. This removes a direct import, not the underlying definitions from the import closure.

Removed proof dependency and obsolete tool-use approval `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: the two formula calculations use the upstream generic composition and conjugacy API. The main module retains its existing public import `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` as part of its pre-existing import interface; the theorem does not invoke its general ringed-topos composition theorem. The original public imports are retained for the existing statement interface; no additional module is claimed pruned from the targets' import closure. The other original proof dependencies provide the K-injective, exactness, proper/open interchange, and canonical composition interfaces used in the proof. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The retained report incorrectly listed both formula lemmas as still open. Their proofs now compile and contain no `sorry`. Earlier intermediate compile errors concerned reassociation, mapped identities, and the precise canonical derived-composition comparison; these are resolved by explicit homotopy-category calculations and the upstream `CompConjugate` theorem. No mathematical statement repair was needed.

## New nodes

- `lem-sfb-proper-open-tower-single-unit-formula`: records the single-unit normalization, extracted from step 7 of the original node (Stacks Tags 0F7B, 0F7J, and 0D6E). Unit naturality and cancellation of the canonical open and pushforward composition isomorphisms prove it; it leaves no further obligation.

- `lem-sfb-proper-open-tower-successive-unit-formula`: records the successive-unit normalization from step 6 of the original node, with the same sources. Naturality of the supplied interchange, its representative equation, and the canonical composition identity prove it; it leaves no further obligation. Search records are included in both nodes. No change record is required because no existing statement, definition, or public import was changed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
