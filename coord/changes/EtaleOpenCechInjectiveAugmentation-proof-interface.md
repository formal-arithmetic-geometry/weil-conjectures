# EtaleOpenCechInjectiveAugmentation proof interface

## Reason

The proof adds proof-only imports and a private `open TopologicalSpace` command while
using the new comparison module. The delivery tool classifies these as changes visible to
importers, so this record documents the interface effect.

## Old

The original import block, verbatim:

```lean
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.CoverPreserving
```

The original theorem signature and proof, verbatim:

```lean
theorem etaleOpenCechInjectiveAugmentation_quasiIso
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (J : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (e : (CochainComplex.single₀ AddCommGrpCat.{u + 1}).obj (J.obj.obj (op (i.obj ⊤))) ⟶
      (cechComplexFunctor U).obj (i.op ⋙ J.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        J.obj.obj (op (i.obj (∏ᶜ fun k ↦ U (s k))))) t =
          J.obj.map (i.map (homOfLE le_top)).op) : QuasiIso e := by sorry
```

## New

The module imports the proof dependencies and contains the proved theorem. Its local
namespace uses `open TopologicalSpace` for the private degree-zero helper. The public
theorem signature is unchanged. The added imports, verbatim:

```lean
import Sheaf.AlgebraicGeometry.EtaleOpenCechProductComparison
import Sheaf.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Homology.SingleHomology
```

The added namespace opening, verbatim:

```lean
open TopologicalSpace
```

No existing definition or public declaration type changes. The new public comparison
theorem is documented by its new node; its module is imported only for this proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation | X3 | proof and proof-only imports |
| Sheaf.AlgebraicGeometry.EtaleOpenCechResolutionTotal | G1 | Direct importer; compiled unchanged against this delivery; no adaptation needed. |

## Status

landed 20261012T194155-L-470170 2026-10-12 (merge of deliver/X3/Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation)
