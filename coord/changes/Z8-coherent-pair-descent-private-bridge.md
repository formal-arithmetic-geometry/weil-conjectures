# CategoryTheory.CommonStage.coherent_pair_functor_descent

## Reason

The original hole asserts canonical additive quotient categories, coherent functor and
transformation descent, and their Karoubi formulas. Reuse the proved native StageSystem
quotient via an explicit equivalence of representatives and quotient Hom types. Build the
finite biproducts at a common stage. All new constructions and lemmas are private; their
only public use is the body of the theorem. Existing definitions, statements, instances,
visibility, public imports and docstrings remain verbatim.

File-local elaboration settings and the local reducibility of the two object wrappers
permit Lean to infer the canonical private category instance. They change no data or
kernel checking. The checker conservatively records these commands as an interface edit.
The instances on the wrapper are private and have the exact existing pairCategory and
pairPreadditive bodies specialized to the constructed pair structure.

## Old

```lean
import Mathlib.Algebra.Colimit.Module
```

There were no local elaboration commands or private instances between DescentSystem and
the final theorem.

## New

```lean
import WeilConjectures.CategoryTheory.StageSystem.Preadditive
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option allowUnsafeReducibility true in
attribute [local reducible] PairStructure.Obj Pair
```

The scoped allowUnsafeReducibility option permits a local elaboration attribute only;
it neither introduces an unsafe declaration nor bypasses the kernel. The two new private
instances canonicalCategory and canonicalPreadditive select the already specified pair
operations for the private construction, and are unavailable to importing modules.

## Users

`tools/downstream.py Sheaf.CategoryTheory.CoherentPairFunctorDescent --uses
coherent_pair_functor_descent` listed the transitive consumers below and found no external
textual use of the theorem name. Each consumer retains exactly the same public imports,
definitions and theorem signatures. All added imports are private proof imports and every
local elaboration command applies only in this module. No target meaning changes and no
consumer adaptation is necessary. Claim holders were read on 2026-10-23.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoherentPairFunctorDescent | Z8 | Existing public interface unchanged; no adaptation. |
| Sheaf.CategoryTheory.CommonStageKaroubiInverse | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.CategoryTheory.StageSystemFunctorDescent | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.CategoryTheory.Triangulated.TExactPairDescent | G8 | Existing public interface unchanged; no adaptation. |

## Status

landed 20261023T103444-L-3141953 2026-10-23 (merge of deliver/Z8/Sheaf.CategoryTheory.CoherentPairFunctorDescent)
