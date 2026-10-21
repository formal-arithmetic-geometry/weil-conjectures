# AlgebraicGeometry.Etale.geometricStalk_torAmplitude_test

## Reason

Complete the proof using the existing module-valued geometric stalk and inverse-image
functors. Retain only the two imports needed by the statement, and the two private proof
imports. The old header imported a separate pointed-colimit presentation, the lower Tor
predicate, the explicit SheafOfModules inverse-image witness, strict henselization theory,
and several redundant APIs. These are unnecessary for this proof. The theorem signature,
visibility, definitions and instances are unchanged. No source-library module is modified.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.SixFunctors.GeometricStalkTensorConstantSingle
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
```

## New

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.SixFunctors.GeometricStalkTensorConstantSingle
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleStalkTorTest --uses
geometricStalk_torAmplitude_test` reported zero downstream modules and only the item
itself as a textual user. A direct import search likewise found no current Lean importer.
The DAG parents and unit realization remain in place: no withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleStalkTorTest | E1 | Complete proof and reduce imports; signature unchanged. |

There are no consumers to adapt. No target signature or target-used definition changes.
The definition nodes and all four steps of the existing unit route are retained.

## Status

landed 20261021T061000-L-1681833 2026-10-21 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleStalkTorTest)
