# Sheaf.Paper.BoundaryQDefiningCompositeComparison canonical derived braiding

## Reason

Restore the module from the quarantine path named by its 2026-10-23 rework entry.
Compiling that original against the current library fails first at line 76 with
`failed to synthesize instance of type class BraidedCategory (DerivedCategory C)`;
the same error occurs in the public tensor composites and comparison predicate.
The current upstream declaration `DerivedCategory.braidedCategory'` is deliberately
not a global instance. Its defining module explicitly instructs callers to install
it locally. Enable that existing canonical Koszul braiding in this module.

The initial compile with that local instance exceeded 60 seconds. The current
upstream `Functor.leftDerivedFunctor_map_braiding_hom_δ` already proves exactly the
private generic braiding identity. Apply it directly and remove the duplicate
K-flat proof and its two private helpers. The public tensor constructions retain
their original bodies and their specified canonical Koszul braiding.

## Old

The original proof import, verbatim:

```lean
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
```

The original open/context boundary, verbatim:

```lean
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
```

The original private braiding proof used `comparison_fac` and
`comparison_braiding_Qh` to compute the comparison on K-flat representatives and
extend by naturality. All three original private theorem signatures and bodies
are preserved in the rework archive
`quarantine/Sheaf/Paper/BoundaryQDefiningCompositeComparison.lean`, lines 48-137.
No public signature or definition is replaced.

The old private signatures, verbatim:

```lean
private theorem comparison_fac (P Q : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj P)).app
      (DerivedCategory.Qh.obj Q)) ≫
      (F.leftDerivedFunctorCounit.app P ⊗ₘ F.leftDerivedFunctorCounit.app Q) ≫
      μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
    F.leftDerivedFunctor.map (μ DerivedCategory.Qh P Q) ≫
      F.leftDerivedFunctorCounit.app (P ⊗ Q) ≫
      DerivedCategory.Qh.map (δ (F.mapHomotopyCategory (.up ℤ)) P Q)

private theorem comparison_braiding_Qh (P Q : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) :
    F.leftDerivedFunctor.map (β_ (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Q)).hom ≫
      (F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj Q)).app
        (DerivedCategory.Qh.obj P) =
    (F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj P)).app
      (DerivedCategory.Qh.obj Q) ≫
      (β_ (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))
        (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj Q))).hom

private theorem comparison_braiding (K M : DerivedCategory C) :
    F.leftDerivedFunctor.map (β_ K M).hom ≫
      (F.leftDerivedTensorComparison.app M).app K =
    (F.leftDerivedTensorComparison.app K).app M ≫
      (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom
```

## New

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
```

```lean
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
-- The canonical Koszul braiding is explicitly installed locally in the current API.
attribute [local instance] DerivedCategory.braidedCategory'

variable {C : Type v} [Category.{u + 1} C] [Abelian C]
```

The private `comparison_braiding` has the same signature and the complete body:

```lean
  exact F.leftDerivedFunctor_map_braiding_hom_δ hF K M
```

The two other private helpers are removed. This uses the canonical braiding
specified by the node: the Koszul braiding on complexes descended through K-flat
resolutions. No supplied braiding or coherence hypothesis is introduced. All
public declaration signatures, definition bodies and public imports are preserved
from the quarantined module. The attribute is local and exports no new instance.
The main theorem docstring and node's first proof step and proof origin record
this direct native-API route. No DAG dependency changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundaryQDefiningCompositeComparison | D4 | Restore the module, install its canonical braiding locally, and reuse the native braiding theorem. |

`tools/downstream.py` with `--allow-missing` and the five public declaration names
reports zero downstream modules. A textual search of both `lean/` and `quarantine/`
also finds no consumer of those declarations or import of the module. The DAG
parent `lem-weil-boundary-proetale-q-compatibility` still uses this node, so its
attachment and all dependencies are retained. No consumer needs adaptation.
No target statement changes; the canonical tensor composites keep their meaning.

## Status

landed 20261023T102533-L-2921015 2026-10-23 (merge of deliver/D4/Sheaf.Paper.BoundaryQDefiningCompositeComparison)
