# AlgebraicGeometry.nonempty_derivedBaseChange_iso_of_isFlatOver

## Reason

Restore the quarantined item recorded in coord/rework.tsv, retaining its Lean
attachment and original theorem signature. Its archived public import of the
Sheaf derived-pullback construction clashes with adopted upstream proof imports.
The duplicate was retired in the already-landed
B2-derived-pullback-source-construction change. Import the adopted definition
and complete the theorem using the existing canonical relatively flat module
base-change theorem, with explicit comparisons of derived-category models.

The canonical theorem asks for a localization in one universe for every scheme;
the item only assumes four localizations in an arbitrary universe w. Applying
the canonical theorem directly would strengthen the hypotheses. Instead, apply
it in the canonical Grothendieck model in universe u and transport the resulting
object isomorphism to the four given models. The direct-image comparison uses
the same functorial K-injective resolution in both models; no data is chosen
from an unproved existence theorem.

## Old

The archived import interface, verbatim:

```lean
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import Sheaf.AlgebraicGeometry.BaseChangeMapCech
import Sheaf.AlgebraicGeometry.CechResolution
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
```

The archived public theorem signature, verbatim:

```lean
theorem nonempty_derivedBaseChange_iso_of_isFlatOver
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [SheafOfModules.IsQuasicoherent.{u} (R := moduleRings X.toRingedSpace) G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))] :
    Nonempty
      ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ≅
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G)))
```

Its proof was `by sorry`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
```

The public theorem signature above is textually identical. Its proof is complete,
with no added public declarations. Six private helpers compare single objects,
direct images, pullbacks, the full source and target, and the canonical-model
base-change isomorphism. All are proved. The source construction of derived
pullback, all other definitions and the target statements are unchanged.

Remove BaseChangeConventions, which is unused here, and narrow DirectImage to
DirectImage.Basic, which supplies IsFlatOver. The proof no longer directly imports
the legacy CechResolution or BaseChangeMapCech statements. The existing canonical
proof still performs the prescribed affine Cech computation and uses the source
flat-complex and affine-section declarations transitively.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | Y3 | Restore its source path, replace the retired definition import, close its one archived hole. |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | unclaimed | Only archived direct importer; its import is private. Unchanged archived source compiles against the restored item (5.1 s). No adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Rework row names this item, but its current archived source imports ArrowIsoTensorPullbackCounit, not this item directly. The private edge does not change its public interface. No adaptation. |

The required downstream.py --allow-missing --uses query reports zero live
importers and zero declaration users. No current live Lean file imports the item.
A search of live and quarantined
Lean sources finds no caller of the theorem yet; unfinished DAG parents still
cite the node, so it is restored rather than withdrawn. The node remains attached
to the original declaration. Its parents include lem-pc-zero-scheme-recd,
thm-pc-f-representable, cor-pc-projective-noetherian-rf-perfect-base-change and
lem-pc-f-open-subfunctor, all retained. The unit record has no prescribed
realized node for the changed lower-level argument; the existing canonical
theorem follows the same finite affine Cech route.

Compiling the restored item takes 5.5--5.8 s. `#print axioms` for the public
theorem reports only propext, Classical.choice and Quot.sound. The archived
consumer compiles without modifications in the same server compile set. No
WeilConjectures file is changed. No target definition is changed by this packet;
the prior B2 derived-pullback migration already records its definition review.

## Status

landed 20261020T174928-L-823111 2026-10-20 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange)
