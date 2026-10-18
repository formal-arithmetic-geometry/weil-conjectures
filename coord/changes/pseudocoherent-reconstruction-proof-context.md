# DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction module context

## Reason

The reconstruction proof uses K-projective Hom bijections and the ordinary adjunction.
It does not use the original derived-change-of-rings route for its final comparison.
Remove its unused public import and unused proof imports, add the proof dependencies
actually used, and enable the two backward elaboration options needed for the categorical
normalization calculations. These options affect elaboration in this file only.

The theorem's name, universes, binders, hypotheses, conclusion and visibility are identical.
There is no definition change and no target meaning changes. The new helpers are private
and proved. The seven new public intermediate results have their own DAG nodes.

## Old

The import and command context of the original module was, verbatim:

```lean
public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.PseudoCoherentNilpotentInvariance
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import Sheaf.RingTheory.NilpotentMarkedFreeComplexLift
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
```

## New

The import and command context is now, verbatim:

```lean
public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.ComplexTowerLimitProjectionComparison
import Sheaf.RingTheory.NilpotentFiniteFreeComplexTower
import Sheaf.RingTheory.FiniteFreeComplexTowerInverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Additive

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
```

The public import removed is `Sheaf.Algebra.Homology.DerivedChangeOfRings`. The statement
needs none of its declarations. The still-needed source dependencies are retained as
proof imports of the relevant intermediate modules. The only downstream module independently
publicly imports `Sheaf.Algebra.Homology.DerivedChangeOfRings`, so its declarations remain
available there without any adaptation.

## Users

`tools/downstream.py Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction --uses
isPseudoCoherent_inverse_ring_reconstruction` lists exactly one downstream module. Reading
its complete source shows that it imports the theorem's module as a proof dependency,
currently leaves its own proof open, and already directly publicly imports the removed
public dependency. The unchanged source is compiled against the delivery as a consumer
check and is not part of the delivered file set.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.RlimPerfectComplete | R1 | Same source; own public import; no adaptation. |

## Status

landed 20261018T071136-L-1664003 2026-10-18 (merge of deliver/B4/Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction)
