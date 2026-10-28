# CategoryTheory.inverseImage_ring_functor

## Reason

The statement and four sectionwise operation definitions need sheaf products,
whiskering by the ring forgetful functor, and its limit preservation. They do not
need the project site-covering or module-sheaf declarations, nor do they expose
internal ring objects. Import the Mathlib statement dependencies directly and
keep the two generic proof tools as private proof imports.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
public import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
```

## New

```lean
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
```

All existing declaration signatures, attributes, and operation definitions remain
verbatim. New helpers are private, proved transport lemmas. The only theorem-body
change fills `CategoryTheory.inverseImage_ring_functor`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InverseImageRingFunctor | A4 | Complete proof, direct statement imports. |
| Sheaf.CategoryTheory.GeometricRingInverseImage | unclaimed at snapshot | Sole direct importer and sole external user of all five declarations; statements and operation definitions unchanged; compiled against the delivery. |

The direct-consumer set was checked with `tools/downstream.py --direct --uses`
for `inverseImage_ring_functor` and the four operation helpers. The consumer
already imports `AlgebraicInverseImage`, which supplies its module-sheaf and
whiskering APIs. No consumer adaptation is required.

## Status

landed 20261028T020131-L-2470541 2026-10-28 (merge of deliver/A4/Sheaf.CategoryTheory.InverseImageRingFunctor)
