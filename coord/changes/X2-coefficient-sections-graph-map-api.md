# AlgebraicGeometry.ProEtale.sfbCoefficientSectionMap

## Reason

Repair of the quarantine return at `3714d173785`: restore the original module and all
its declarations with the complete proof. The current shared branch has since restored
the archived one-hole file verbatim. This packet preserves that source's theorem signature
and the node attachment, and closes its hole; it does not withdraw or replace the item
with a stub. The existing item claim is X2. The definition changes below are relative
to both the archived source and that restored baseline.

Factor the four existing coefficient definitions through generic evaluation and graph-map
constructions, preserving their signatures and exact formulas by definitional equality.
The canonical coefficient unit and multiplication morphisms are named explicitly; they
are the existing `MonObj.one` and `MonObj.mul`, with no new instance or choice of data.
The generic evaluation helpers take these morphisms directly.

The proof uses proved formula lemmas to rewrite the coefficient operations and section map.
Automatic conversion from an evaluated generic formula to the coefficient wrapper caused
kernel timeouts; explicit rewriting through the formulas avoids that conversion. All
helpers are proved, and the whole proof remains in the original module. No resource limit
is increased. Private site calculations use scoped
`backward.isDefEq.respectTransparency false` and
`backward.isDefEq.respectTransparency.types false` to compare the existing site wrappers.
The private multiplication construction has an explicit underlying sheaf map, is marked
`irreducible`, and is used through its proved component API.

No source-library declaration, coefficient object, graph, operation, theorem statement,
or Challenge declaration is changed. There is no postponed data or new unfinished lemma.

## Old

```lean
noncomputable def sfbSectionOne
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) : (condensedRingObj Λ X).obj.obj (op T) :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (MonObj.one (X := condensedRingObj Λ X))).app (op T)).hom (ULift.up (1 : ℤ))

noncomputable def sfbSectionMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt)
    (a b : (condensedRingObj Λ X).obj.obj (op T)) :
    (condensedRingObj Λ X).obj.obj (op T) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) (condensedRingObj Λ X) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (MonObj.mul (X := condensedRingObj Λ X))).app (op T)).hom (a ⊗ₜ[ℤ] b)

noncomputable def sfbCoefficientSectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (T : B.ProEt) :
    (condensedRingObj Λ B).obj.obj (op T) ⟶
      (condensedRingObj Λ T.left).obj.obj (op (Scheme.ProEt.mk (𝟙 T.left))) :=
  (condensedPushforwardHom Λ T.hom).hom.app (op T) ≫
    (condensedRingObj Λ T.left).obj.map
      (sfbSectionGraph T.hom T (𝟙 T.left) (Category.id_comp T.hom)).op

noncomputable def sfbCoefficientGlobalMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedRingObj Λ Y).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  (condensedPushforwardHom Λ f).hom.app (op (Scheme.ProEt.mk (𝟙 Y))) ≫
    (condensedRingObj Λ X).obj.map
      (sfbSectionGraph f (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)).op
```

## New

```lean
noncomputable def sfbSheafSectionOne {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (unit : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R) (T : X.ProEt) :
    R.obj.obj (op T) :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      unit).app (op T)).hom (ULift.up (1 : ℤ))

noncomputable def sfbSheafSectionMul {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (mul : R ⊗ R ⟶ R) (T : X.ProEt)
    (a b : R.obj.obj (op T)) : R.obj.obj (op T) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R R ≫
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      mul).app (op T)).hom (a ⊗ₜ[ℤ] b)

noncomputable def sfbCoefficientUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X :=
  MonObj.one (X := condensedRingObj Λ X)

noncomputable def sfbCoefficientMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :
    condensedRingObj Λ X ⊗ condensedRingObj Λ X ⟶ condensedRingObj Λ X :=
  MonObj.mul (X := condensedRingObj Λ X)

noncomputable def sfbSectionOne
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt) : (condensedRingObj Λ X).obj.obj (op T) :=
  sfbSheafSectionOne (condensedRingObj Λ X)
    (sfbCoefficientUnit Λ X) T

noncomputable def sfbSectionMul
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (T : X.ProEt)
    (a b : (condensedRingObj Λ X).obj.obj (op T)) :
    (condensedRingObj Λ X).obj.obj (op T) :=
  sfbSheafSectionMul (condensedRingObj Λ X)
    (sfbCoefficientMul Λ X) T a b

noncomputable def sfbSectionMapOfHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (η : R ⟶ (lowerStar Ab.{u + 1} f).obj S)
    (T : Y.ProEt) (a : X ⟶ T.left) (ha : a ≫ T.hom = f) :
    R.obj.obj (op T) ⟶ S.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  η.hom.app (op T) ≫ S.obj.map (sfbSectionGraph f T a ha).op

noncomputable def sfbCoefficientSectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {B : Scheme.{u}} (T : B.ProEt) :
    (condensedRingObj Λ B).obj.obj (op T) ⟶
      (condensedRingObj Λ T.left).obj.obj (op (Scheme.ProEt.mk (𝟙 T.left)))  :=
  sfbSectionMapOfHom (X := T.left) (Y := B) T.hom
    (condensedRingObj Λ B) (condensedRingObj Λ T.left)
    (condensedPushforwardHom (X := T.left) (Y := B) Λ T.hom) T
    (𝟙 T.left) (Category.id_comp T.hom)

noncomputable def sfbCoefficientGlobalMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedRingObj Λ Y).obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      (condensedRingObj Λ X).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  sfbSectionMapOfHom f (condensedRingObj Λ Y) (condensedRingObj Λ X)
    (condensedPushforwardHom Λ f) (Scheme.ProEt.mk (𝟙 Y)) f (Category.comp_id f)
```

## Users

`tools/downstream.py` reports the following five downstream modules. Its `--uses`
checks find no occurrence of any of the four changed definitions outside the item. Both downstream
modules retain their statements and meaning; no consumer adaptation is necessary.
The removed public continuous-coefficient import is independently available through
`FiniteConstantLocalModel` and `FiniteConstantModelResolution`. The internal-Hom consumer
directly imports `ProEtalePointPullback`; the local-model consumer uses none of its
additional declarations. The identity-open consumers use the published condensed-module
framework through their own imports. The theorem statement matches the current restored
source verbatim. A clean server compile completed in 13.5 seconds with no warnings.
The final source (16.3 seconds) and all three unchanged direct consumers were then
compiled in import order against the repaired module: LocalModelCohomologyDescent
(4.9 seconds), AdmissibleScalarRealizationExact (6.8 seconds), and
IdentityOpenDerivedRestriction (8.0 seconds). All compiled without warnings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | X2 | Own definitions factored by definitional equality; theorem proved. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | No adaptation; imports the theorem and does not mention the changed definitions. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No adaptation; no use of the changed definitions. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | unclaimed | No adaptation; scalar interfaces are supplied by its own public imports. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | No adaptation; no use of the changed definitions or removed coefficient APIs. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | No adaptation; imports the identity-open restriction framework. |

All five Challenge declarations and all their mathematical meanings are preserved.
The definition refactor introduces no weakening or new assumptions.

## Status

landed 20261021T130232-L-2645840 2026-10-21 (merge of deliver/X2/Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization)
