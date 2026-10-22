# AlgebraicGeometry.schemeGlobalDerivedHom_pullback_comparison

## Reason

The assigned rework row persists, but E4 already restored the item with zero
holes at landing 20261022T002359-L-1922723. The current original compiles.
This delivery repairs a remaining compatibility conflict: importing the existing
mixed-universe transport theorem together with the Sheaf pullback comparison fails:

```
error: import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison failed,
environment already contains 'AlgebraicGeometry.schemeGlobalDerivedHom_pullback_comparison'
from Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
```

The adopted source module supplies the same three public definitions. Re-export
it at the Sheaf path, retaining both previous public imports. The assigned theorem
then specializes the existing mixed-universe theorem instead of duplicating its
naturality and cancellation argument. No source-library file changes.

The full import-closure comparison removes exactly three Sheaf modules from
this item's route: Sheaf.AlgebraicGeometry.DerivedPullbackComposition,
Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange, and
Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate. The last contains one
literal sorry. All additional project source modules imported by the adopted
mixed theorem contain zero literal sorries. These modules remain in the library;
this records pruning of the item's dependency route only.

## Old

The former Sheaf module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom


/-! # Canonical pullback comparison on global derived Hom
Source: Stacks Project, Cohomology, Remark 08I3 and Section 0B6A;
Duality, Tag 0AA8 (blueprint: def-pc-global-hom-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe uP wP
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{uP},
  HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type uP) [Ring R], HasDerivedCategory.{wP} (ModuleCat.{uP} R)]

/-- Apply global sections to the evaluation-mate pullback map, then the canonical
Leray comparison. No comparison map is supplied as an input.
Source: Stacks, Tags 08I3, 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalDerivedHom_pullback_comparison
    {S T : Scheme.{uP}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) :
    (schemeGlobalDerivedHom S).obj (op P, Q) ⟶
      (schemeGlobalScalarRestriction h).obj
        ((schemeGlobalDerivedHom T).obj
          (op ((derivedPullback h).obj P), (derivedPullback h).obj Q)) :=
  (schemeDerivedGlobalSections S).map
      ((schemeHomPullbackAdjunction h).homEquiv _ _
        (((schemeDerivedTensorHomEquiv T)
          ((derivedPullback h).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
          ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
            ((schemeHomTensorPullbackIso h).inv.app
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
              (derivedPullback h).map
                ((schemeDerivedTensorHomEquiv S)
                  ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
                  P Q (𝟙 _))))) ≫
    (schemeGlobalSectionsDirectImageIso h).hom.app
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj
        (op ((derivedPullback h).obj P), (derivedPullback h).obj Q))

/-- Restriction of scalars along a composite, with the identity module comparison.
Source: Stacks, Tags 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalScalarRestrictionCompIso {X Y Z : Scheme.{uP}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeGlobalScalarRestriction (f ≫ g) ≅
      schemeGlobalScalarRestriction f ⋙ schemeGlobalScalarRestriction g :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp' g.appTop.hom f.appTop.hom (f ≫ g).appTop.hom rfl) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Scalar identification of the two paths around a commutative square.
Source: Stacks, Tags 0B6A and 0AA8
(blueprint: def-pc-global-hom-pullback-comparison). -/
def schemeGlobalScalarSquareIso {X Y X' Y' : Scheme.{uP}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g) :
    schemeGlobalScalarRestriction gX ⋙ schemeGlobalScalarRestriction f ≅
      schemeGlobalScalarRestriction f' ⋙ schemeGlobalScalarRestriction g :=
  (schemeGlobalScalarRestrictionCompIso gX f).symm ≪≫
    eqToIso (congrArg schemeGlobalScalarRestriction h) ≪≫
      schemeGlobalScalarRestrictionCompIso f' g

end AlgebraicGeometry
```

The assigned theorem's public signature is unchanged byte for byte. Its old
proof uses four private helpers and Sheaf.GlobalHomBaseChangeExchange.

## New

The compatibility module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison

/-! # Canonical pullback comparison on global derived Hom

Compatibility import for the adopted canonical construction. Keeping a second copy
of the public declarations prevents importing the mixed-universe transport theorem.
The private equality in GlobalHomBaseChangeCounitTransport checks that the former
evaluation-mate expression agrees with the adopted construction, including its
tensorator and Leray comparison.

Source: Stacks Project, Tags 08I3, 0B6A and 0AA8.
(blueprint: def-pc-global-hom-pullback-comparison).
-/

@[expose] public section
```

The original three public names and their types come from the source module.
The scalar composition and square definitions are textually identical. The only
changes inside the pullback construction replace schemeHomTensorPullbackIso and
schemeGlobalSectionsDirectImageIso with mixedHomTensorPullbackIso and
mixedGlobalSectionsDirectImageIso. In the assigned module's Compatibility section:

- legacyTensor_eq proves equality of the tensorators by component extensionality.
- legacyLeray_eq proves equality of the Leray comparisons by reflexivity and proof
  irrelevance of the existential proof.
- legacyPullbackComparison_eq compares the entire original definition, written
  verbatim on its right side, with the adopted definition. Rewriting the first
  two equalities and reflexivity proves it.

These are complete private proofs, with no new assumptions or holes. Thus no
statement or target changes mathematical meaning. The definition node is attached
to the actual source module; its statement and dependencies remain unchanged.
The unit route remains unchanged.

The new complete theorem proof is:

```lean
  simpa only [schemeGlobalDerivedHom_pullback_comparison,
    mixedGlobalHomPullbackComparison, schemeGlobalHomDirectImageMap,
    mixedGlobalHomDirectImageMap, mixedHomDirectImageComparison] using
    mixedGlobalHom_baseChange_counit_transport f g M N E K t e e' h
```

The mixed and original direct-image comparisons choose witnesses of the same
existential proposition, so their definitions agree by proof irrelevance.

The exchange consumer requires one additional existing equality in its final
simp list: schemeHomTensorPullbackIso_eq_mixed. Its original final simpa produces
a type mismatch: the proof's expanded pullback mate contains
(schemeHomTensorPullbackIso g).inv.app, while the expected type now contains
(mixedHomTensorPullbackIso g).inv.app (and likewise for pullback.fst f g).
Normalizing the compatibility tensorator in that last simp reconciles them.
Every exchange signature and import is preserved; no other lines change.

## Users

The downstream script was run for each of the three public names. It reports
six downstream modules. Their current holders were checked in coord/claims.
The archived FlatPrecomposePus additionally remains a DAG parent and caller.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Re-export identical canonical definitions; retain previous public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | B2 | Specialize the adopted mixed transport; unchanged public signature. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | Forced addition of one tensorator equality to final simp; unchanged signatures and imports. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Identical statement meaning and no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | Identical statement meaning and no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | Identical counit-map construction by the proved comparison equality; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate | unclaimed | Scalar-square construction identical; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | quarantined | Original transport signature preserved; archive retained without edits. |

All active downstream originals are compiled against the changed comparison in
the sandbox. Only the exchange consumer needs the forced adaptation above.

## Status

landed 20261022T013348-L-3552123 2026-10-22 (merge of deliver/B2/Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport)
