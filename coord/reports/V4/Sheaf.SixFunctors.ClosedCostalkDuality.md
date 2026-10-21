## What changed

Filled both common-left-adjunction proofs in `Sheaf.SixFunctors.ClosedCostalkDuality`.
They now apply the actual native tensor-Hom adjunction at the two sites, the native
symmetry and a proved categorical projection-to-adjunction argument. The two final
comparison proofs continue to apply uniqueness of right adjoints, with unchanged
statements, universes and hypotheses.

Added `ClosedTensorDualAdjunction`: a complete proof of fixed-target contravariant
self-adjunction and of the natural Hom calculation transporting it through a projection
formula and exceptional adjunction. The proof checks naturality in both variables;
it has no sorry. Added the separate etale and pro-etale closed tensor projection
statements, each exactly the middle identity in the current blueprint's Hom chain.
These statements have no exceptional functor, dualizing object or internal Hom.
Proved both closed projection formulas: use exact closed/open localization, its
homology comparisons and canonical tensor pullback to show the adjunction unit on
`i_* N tensor K` invertible. Whiskering that unit with tensor pullback and counit
produces a natural isomorphism, which is transported to the supplied exact derived
presentations (etale) and actual right-derived direct image (pro-etale). This avoids
introducing a new totalization theorem. The etale proof includes the full arbitrary-ring
module presentation and exactness, closed counit, open vanishing and joint detection.
Proved the separate native tensor-pullback input too: construct unit-normalized ring
and module underlying-set comparisons, transport every operation graph by the set
adjunction, and identify the module functor literally with p. Generalize the private
identity scalar-extension construction from `RingedTopoiDerivedPullback` to independent
site universes, apply canonical tensor descent with native representative isomorphisms,
and transport through the exact derived localization factorizations.

Extracted the six unchanged etale operations into `ClosedCostalkEtaleOperations`,
publicly re-exported by the original module, so the projection module can use them
without an import cycle. The definitions and instance bodies are identical. Change
record: `coord/changes/V4-closed-costalk-etale-operations.md`.

All six changed/new Lean files compile remotely; final import-order verification
is recorded by the delivery tool.
The generic calculation was built incrementally through explicit opposite-category,
currying, evaluation, projection and adjunction naturality checks. Edge cases checked
in the statements: identity immersion, empty closed or open side, zero complexes,
zero coefficient ring, arbitrary unbounded complexes and independent site universes.
No reflexivity, perfectness, constructibility or boundedness is assumed.

## Proved and sorry left

Closed the two existing holes:

- `AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality_etale_common_left_adjunction`
  (`lem-weil-closed-costalk-etale-common-left-adjunction`).
- `AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality_proetale_common_left_adjunction`
  (`lem-weil-closed-costalk-proetale-common-left-adjunction`).

The item module has zero remaining sorry. The unchanged final declarations
`AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality_etale` and
`AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality` are proved from these.
New fully proved declarations include
`WeilConjectures.CoefficientClosedStructure.dual_adjunction` and
`WeilConjectures.CoefficientClosedStructure.common_left_of_projection`.

The new `AlgebraicGeometry.Scheme.proEtaleClosedTensorProjection`
(`lem-weil-proetale-closed-tensor-projection`) is fully proved from the existing
canonical tensor-pullback and ringed open/closed declarations. Its proof includes
module-functor comparisons, exact-derived adjunction, closed counit invertibility,
open vanishing, homology detection and the natural projection isomorphism.

The new `AlgebraicGeometry.Scheme.etaleClosedTensorProjection` is also proved.
Its proof transports arbitrary coefficient module adjunctions to the abelian sheaf
adjunction, reflects exactness and the support data, and then uses the same derived
supported-unit calculation. Both localization identifications use the Q factorizations
in the actual statement. No special presentation of iStar is assumed.

The new `AlgebraicGeometry.Scheme.etaleNativeTensorPullback`
(`lem-weil-etale-native-tensor-pullback`) is fully proved as well, for an arbitrary
scheme morphism and arbitrary inverse-image ring sheaf. The proof constructs the
algebraic presentation required by the general canonical tensor-pullback interface,
rather than assuming an identification of coefficient or module presentations.

Actual final hole count: zero in every changed/new Lean file. Closed 2 existing holes;
added 0 holes; 0 unfinished statements split off. The new mathematical intermediate
theorems are all proved in this session. The net hole decrease in the assigned packet
is 2. Existing library dependencies, including canonical tensor comparison and
`RingedDerivedNative.closedAdjunction`, are used as stated; their existing holes
are not counted as newly added or claimed closed.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.Paper.PbcCompletedPullbackActual`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The pro-etale projection proof imports `ProEtaleRingedOpenClosed` privately and
uses the proved exact-derived-adjunction helpers of `ProEtaleRingedClosedKernelAdjoint`;
those modules are retained dependencies, even though they are no longer direct imports
of the item. It also uses `ProEtaleOpenClosedDetection`, canonical tensor pullback
and the native closed adjunction. The etale native tensor-pullback proof uses
`RingedTopoiCanonicalTensorPullbackOfUniverses` privately, so removing that direct item
import does not prune its node. K-flat resolution remains below canonical tensor
pullback, rather than a separately reproved totalization step.

`ConcreteCoefficients` and `Etale.UpperLowerStar.Defs` moved to the extracted
operations module; they are not claimed as pruned. The closed-support, K-flat and
tensor-pullback results remain dependencies of the geometric projection statements,
so their removal as direct imports is not a claim that those nodes are unnecessary.
No source-library declaration was removed, no module was withdrawn, and no global
closure pruning is claimed.

The common-left nodes no longer cite `lem-weil-closed-costalk-duality` as a proof
dependency: that was a circular placeholder. They now cite the relevant projection,
the generic Hom calculation, native symmetry and native closed adjunction. The
unit's displayed tensor-Hom/projection/exceptional-adjunction route is retained.
`dag/units/sk-prop-sf-biduality-general.json` has empty `realized` fields; no unit
step or statement has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained packet proved zero of the item's two holes. The first required delivery
check correctly rejected that packet; the common-left adjunction calculations had
not been written. This delivery supplies them. The old two intermediate DAG nodes
pointed back to their own parent; their proof dependencies now follow the actual
acyclic Lean proof.

The main-20261015 blueprint explicitly supplies the closed projection identity as
a separate middle step. Its existence is not a consequence of generic adjunction
uniqueness. We therefore give that geometric step its own statements, while proving
all of the categorical arrows and their naturality. The adopted source library and
all target signatures remain untouched. No other group's module needed adaptation.

## New nodes

`def-weil-closed-costalk-etale-operations` attaches the six extracted, unchanged
operations and instances. The main node's Lean attachment now lists its two final
comparisons and records the public re-export. Change record:
`coord/changes/V4-closed-costalk-etale-operations.md`.

`lem-weil-closed-tensor-dual-adjunction` records the proved symmetric currying
self-adjunction; `dual` is a real functor construction, not a chosen existence witness.

`lem-weil-closed-projection-common-adjunction` records the proved generic Hom chain,
including both naturality laws, from a projection isomorphism and exceptional adjunction.

`lem-weil-etale-closed-tensor-projection` and
`lem-weil-proetale-closed-tensor-projection` record the respective unbounded geometric
projection identities. Both are proved. Each has a source paragraph, full proof in
words, edge-case analysis above and independent Lean module.

`lem-weil-etale-native-tensor-pullback` records the proved separate inverse-image
result for an arbitrary morphism and arbitrary inverse-image ring sheaf, with its own
module and source proof in words. Its operation-graph proof adapts the private argument
of `ProEtaleAlgebraicInverseImage` to the etale adjunction; its identity scalar-extension
proof adapts the private construction of `RingedTopoiDerivedPullback` to independent
site universes. Mathlib searches found the exact derived descent and ordinary tensor
tools but no matching native ringed-site tensor comparison.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
