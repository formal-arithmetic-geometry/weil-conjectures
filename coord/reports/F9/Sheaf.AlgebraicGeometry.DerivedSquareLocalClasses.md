## What changed

Reduced AlgebraicGeometry.derivedSquareUnit_localClasses to the single-morphism
resolution/class comparison squareResolution_localClass and the pre-sheafification
roof calculation square_localHypercohomology. The proof combines these equations
with proved naturality of the normalized derived local class and the supplied
local defining equation of e. It cancels only the canonical total/classical
comparison isomorphism, never a class map.

Moved restrictedDirectImageMap and schemeSingleCohomologyComparison, with the same
names, signatures and bodies, into DerivedSquareLocalClassModels, publicly imported
by the item. This prevents an import cycle. The new isomorphisms
squareInverseOpenComparison and squareLocalResolutionComparison are constructed
from actual augmentations, derived units and exact homology/evaluation comparisons.
There is no arbitrary data witness from an unproved existence theorem.

SquareLocalClassNaturality proves AlgebraicGeometry.RingedSpace.squareLocalClass_naturality.
It uses the already proved private sheafificationAt_naturality lemma via a proof-only
`import all Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf`, and
combines that equation with naturality of the abelian sheafification unit. No
resolution-level proof is duplicated. A private categorical pasting lemma proves
the composition argument independently of the large derived constructions.

The unclaimed consumer TopBaseChangePresheaf exceeded the file limit without Lean
errors. Its topBaseChangeAdjoint now uses the identical named
schemeSingleCohomologyComparison in place of spelling out its body, and the private
equality API uses rfl without delta unfolding. Public signatures are unchanged.

## Proved and sorry left

Closed the original direct hole AlgebraicGeometry.derivedSquareUnit_localClasses
(node lem-weil-pbc-derived-square-local-classes) by decomposition into two strictly
smaller steps. The item has zero direct holes. This is a decomposition, not a net
proof: one hole closed, two holes added, net minus one hole closed.

The delivery adds these two holes, each the entire proof of its named public theorem:

- AlgebraicGeometry.squareResolution_localClass
  (lem-weil-pbc-square-resolution-local-class): a single morphism, no coefficient
  square, no edge e; agrees classical resolution classes with normalized derived classes.
- AlgebraicGeometry.square_localHypercohomology
  (lem-weil-pbc-square-local-hypercohomology): a calculation before sheafification,
  no edge e and no class maps or classical direct-image comparisons.

Proved AlgebraicGeometry.RingedSpace.squareLocalClass_naturality
(lem-weil-pbc-square-local-class-naturality), with no direct holes, and constructed
both comparison isomorphisms without holes, together with the proved unfolding API
squareInverseOpenComparison_class. Total delivered direct holes: two.
The delivery compilation checked all five new/changed proof modules successfully
(main theorem 55.9 seconds). The consumer compiled without Lean errors but exceeded
the file limit at 67 seconds; its checking cost is being repaired.

## No longer needed

No modules are withdrawn or pruned from the target closure. The parent's former
resolution, square-mate, unit-normalization and independence dependencies are
retained in the two lower statements' proof plans. They are not claimed obsolete.
The parent now imports exactly the three comparison/naturality modules used by its proof.
Its redundant direct public imports of DerivedAdjunctionTopEdge,
FlatBaseChangeOpenChoices and RightDerivedFunctor.PlusCompatibility are removed;
all three remain publicly available through DerivedSquareLocalClassModels.
The unused DerivedSquareUnitMap import was removed from the new model-only module;
it remains in the parent and roof module, which use the square map. No existing
source-library declaration, signature, attribute or public import is changed.

## Where the brief, the DAG or earlier work was wrong

The original plan explains the mathematical route but its cited statements do not
yet express either the normalized classical/derived class comparison or the local
roof calculation as a usable Lean equation. The two new statements specify these
separate steps against explicitly constructed maps. A general derived square does
not come with a termwise lift into v_*J; the roof must pass through an injective
replacement, and only its sections' cohomology is inverted.

The initial comparison experiment exposed a universe mismatch: X.Modules must use
the supplied HasDerivedCategory.{w} instance. This is handled explicitly. The existing normalized naturality proof is reused directly.
Edge cases checked mathematically: q=0, the empty inverse-image open, zero modules,
identity squares and nonflat maps. Neither remaining statement adds a flatness or
cohomological bound hypothesis. The unit route and original target statements stay intact.

## New nodes

- def-weil-pbc-derived-square-local-models: actual resolution and inverse-open
  comparison isomorphisms, plus the relocated existing definitions. Source: Tags
  01E4, 0D5X and canonical total/classical compatibility.
- lem-weil-pbc-square-resolution-local-class: the single-morphism normalization
  step of Tags 01E4 and 0BKJ, using the explicit resolution isomorphism.
- lem-weil-pbc-square-local-hypercohomology: the coefficient-roof calculation of
  Tag 01FB, before sheafification, including normalization by Tag 0D5X.
- lem-weil-pbc-square-local-class-naturality: the proved naturality of the fixed
  local-class transformation, using K-injective model and sheafification naturality.

Mathlib searches: LeanSearch returned sheafification-unit and rightDerived_map_eq
ingredients; LeanFinder returned generic local cohomology and derived comparison
facts; Loogle for homologyRightDerivedFunctorObjSingleFunctorIso and for
mapHomologyIso/homologyπ returned no hits; msearch grep returned no Mathlib match.
Project rg found the definitions and specialized flat-base-change and stalk class
comparisons, but no general normalized derived/classical square equation.
Blueprint searches for local cohomology class and 01E4 found zero imported nodes;
the new nodes retain the parent's recorded blueprint ancestor and exact route.

Change records: coord/changes/F9-derived-square-local-models.md and
coord/changes/F9-top-base-change-comparison.md.

Not duplicates: the existing higher-direct-image theorem gives the sheafification
and stalk universal properties, but does not identify its classical class map with
topEdgeLocalClass. The square-mate and unit-normalization theorems concern derived
direct images, without evaluating local hypercohomology or moduleCohomologyFMap.
The two new comparison statements isolate these missing equations; neither
restates the original theorem or assumes its desired conclusion.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
