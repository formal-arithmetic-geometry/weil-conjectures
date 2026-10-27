## What changed

Completed `SheafOfModules.signedLineScalarPullbackSquare_of_normalized` by local signed
basis calculations. All original public imports and the public theorem signature are
verbatim unchanged. Added private proved helpers for adjunction-unit naturality,
restriction, semilinearity, local basis transport through the localization comparison,
and preservation of signed bases by normalized pullback families. Proof-only imports
expose the existing private signed-basis API and the proved localization comparison.
Local elaboration settings are documented in
`coord/changes/U5-signed-pullback-local-elaboration.md`.

The final module compiles cleanly in 29.0 seconds through `lcompile.py`.

## Proved and sorry left

Closed the single original hole:
`SheafOfModules.signedLineScalarPullbackSquare_of_normalized`, node
`lem-pur-signed-line-scalar-pullback-naturality`. No holes added or left, no split-off
statements. All five new private helpers are proved. The tentative helper split in
64bf91c6e88 is superseded by its complete private proof in this delivery.

## No longer needed

No original public imports removed and no module withdrawn. The node's planned direct
proof dependencies no longer needed are:

- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
  (`Sheaf.CategoryTheory.ModulePullbackTensorIso`): the existing sectionwise square
  permits a direct calculation, so no tensor reassociation is constructed.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
  (`Sheaf.CategoryTheory.SiteInverseImageTensor`): given normalized families already
  supply tensor recursion; `local_continuous` supplies slice continuity.
- `lem-weil-pbc-ringed-topoi-module-adjunction`
  (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`): the universe-level
  Mathlib pullback adjunction suffices.
- `lem-pur-ringed-site-finite-free-dual-pullback`, as a proof theorem: the negative
  evaluation normalization and naturality of a functional suffice. The public import
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` remains because the
  statement uses its pullback functor and section abbreviations.
- `def-pur-sheaf-tensor-product`, as an additional direct proof dependency: the scalar
  tower supplies the signed-power and basis APIs; tensor construction is still used
  transitively.

The retained direct proof dependencies are the signed scalar tower, the localization
comparison and the universe-level module-pullback existence theorem. None of the above
modules is asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned explicit scalar/pullback reassociation is unnecessary for the stated
sectionwise square. Applying sheaf separatedness to the pushforward of the target
signed power checks equality using the source trivializing cover directly. Cover
preservation is still used for slice continuity when transporting bases. Negative
degrees use the normalized evaluation equation and naturality on target slices.

The local chart proof must distinguish `(Over.post U).obj (Over.mk (𝟙 V))` from
`Over.mk (𝟙 (U.obj V))`: their underlying objects agree, but their structure arrows
are related by the functor identity law. The proof calculates on the first object and
uses an explicit slice morphism to compare with the second. This avoids dependent
rewrites through the ring/module restriction wrappers.

The unit record attaches no realized statement or proof step to this node. The tensor
power/internal-Hom route is preserved; no unit or target statement changes.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
