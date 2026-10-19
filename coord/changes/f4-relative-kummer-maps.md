# Canonical relative Kummer definitions

## Reason

Relocate the seven canonical maps and predicates to a public dependency module so
that genuine separate calculation and exchange results can mention them without an
import cycle. The item publicly reexports this module. The established public imports are retained
to preserve the cached instance elaborations: reducing them to two roots repeatedly
made the definitions exceed the unchanged compile limit.

Also repair expensive definitional conversions in `derivedCoefficientPullback`,
`kummerGenerator`, and `KummerBaseChangeConclusions`. Detailed profiling showed Lean
normalizing localization morphisms while comparing named degree-zero complexes with
their single-complex expansions. The original extracted definitions repeatedly
exceeded the unchanged 60-second compilation limit. Explicit reflexive equality maps
make these coefficient identifications visible and avoid those conversions. The exact coordinate-naturality equation is also named by the irreducible
`CoordinateKummerNaturality` predicate, shared by the conjunction and its exchange
lemma. Unfolding that predicate gives verbatim the same equation. This
repairs the definitions themselves; no compilation limit is raised and no source
functor is replaced.

All seven existing signatures and their visibility stay identical. Four bodies
(`constantPullback`, `twistPullback`, `relativeUnit`, and
`RelativeKummerConclusions`) are verbatim. The three other bodies have the same
actual maps and predicates: the general `derivedSheaf_eq_single` theorem is proved by `rfl`, and its
two Boolean proof abbreviations instantiate that same reflexive identity;
`coordinateClass` is the published coordinate class before and after those equality
maps; `mapWithComparison` is the original comparison followed by the mapped
coefficient arrow. After substituting the reflexive equalities, `eqToHom_refl`,
`CategoryTheory.Functor.map_id`, the shift functor's identity law, and the category identity laws
remove every inserted transport. The resulting formulas are exactly the old ones.
This proves equality of the actual maps, rather than merely preservation of their
isomorphism classes.

Thus all consumer statements retain their mathematical meaning, including all
Challenge targets. Definition-sensitive target review is reopened by this record;
no target signature or hypothesis changes. The two direct existing importers are
compiled unchanged against the final overlay as recorded in the report.

## Old

In `lean/Sheaf/Paper/PurityRelativeKummer.lean`, verbatim:

```lean
/-- Canonical pullback on constants, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def constantPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ⟶
      P.constant X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.constantEtale Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient))

/-- Canonical pullback on the finite twist, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.twist h Y) ⟶
      P.twist h X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.twistEtale h Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (P.twistEtalePullback h f)

/-- Pullback of a coefficient object in the derived category. This is the standard
single-complex comparison followed by the canonical map on the actual sheaves.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor).obj
      (P.derivedSheaf h Y twisted) ⟶ P.derivedSheaf h X twisted :=
  (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.coefficientSheaf h Y twisted) ≫
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
          (match twisted with
            | true => P.twistPullback h f
            | false => P.constantPullback f)

/-- The canonical unit with coefficients identified by their canonical pullback map.
Source: blueprint sk-prop-a1-kummer, clauses (1) and (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    P.derivedSheaf h Y twisted ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
        (P.derivedCoefficientPullback h f twisted)

/-- The edge-section map, obtained by transposing the actual coordinate class and
taking H0, followed by the standard H0(K[1])=H1(K) comparison. It is the A-linear map
whose value on 1 is the Leray edge image of kappa(t).
Source: blueprint sk-prop-a1-kummer, clause (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def kummerGenerator (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (((ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection Y) false ≫
            (P.coordinateKummer h Y a).hom)) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.derivedSheaf h (Punctured Y) true)) ≫
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).shiftIso
        (1 : ℤ) 0 1 (add_zero 1)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true))

/-- The assertions in clauses (1)-(3), with the actual specified maps. No finite-type
condition is built into this predicate, so it also applies to geometric fibres.
Source: blueprint sk-prop-a1-kummer, clauses (1)-(3)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def RelativeKummerConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  IsIso (P.relativeUnit h (lineProjection Y) false) ∧
  IsIso (P.relativeUnit h (lineProjection Y) true) ∧
  (∀ (m : ℕ), 0 < m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (lineProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Line Y) true)))) ∧
  IsIso ((DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (P.relativeUnit h (puncturedProjection Y) true)) ∧
  IsIso (P.kummerGenerator h Y a) ∧
  ∀ (m : ℕ), 2 ≤ m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)))

/-- Clause (4): naturality of the actual coordinate class and invertibility of the
canonical exchange mates. Their targets use the canonical coefficient pullback
identifications; invertibility is equivalently tested before those identifications.
Source: blueprint sk-prop-a1-kummer, clause (4)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def KummerBaseChangeConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.derivedSheaf h (Punctured Y) true) ≫
    (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
      P.derivedCoefficientPullback h (puncturedMap g) false ≫
        (P.coordinateKummer h Y' (g ≫ a)).hom ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
      (P.derivedSheaf h (Line Y) true)) ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.derivedSheaf h (Punctured Y) true))
```

## New

In `lean/Sheaf/Paper/PurityRelativeKummerMaps.lean`, publicly reexported by the item:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.PurityAffineLineDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
/-!
# Relative affine-line acyclicity and the actual Kummer generator

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.md
(blueprint: prop-pur-gm-relative-kummer).

All objects below are actual finite-coefficient module sheaves on the small pro-etale
site. The maps are the units and canonical exchange mates of the published functors.
The generator is homology of the adjoint of the coordinate's actual Kummer boundary.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  ProEtale.upperStar ProEtale.lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.derivedBaseChangeMap

/-- A single-object comparison followed by the image of a coefficient map.
Source: composition of the specified comparison with the coefficient map
(blueprint: def-pur-relative-kummer-maps). -/
def CategoryTheory.Functor.mapWithComparison
    {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    (S : C ⥤ E) (T : D ⥤ E') (L : E ⥤ E') (F : C ⥤ D)
    (alpha : S ⋙ L ⟶ F ⋙ T) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    L.obj (S.obj X) ⟶ T.obj Y := alpha.app X ≫ T.map f

namespace WeilConjectures.PurityFiniteSetting

/-- The named coefficient complex is the degree-zero complex of its sheaf.
Source: the definition of `derivedSheaf` (blueprint: def-pur-relative-kummer-maps). -/
theorem derivedSheaf_eq_single (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) (twisted : Bool) :
    P.derivedSheaf h Y twisted =
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
          (P.coefficientSheaf h Y twisted) := rfl

/-- The untwisted named complex is the constant sheaf in degree zero.
Source: the definition of `derivedSheaf` (blueprint: def-pur-relative-kummer-maps). -/
abbrev derivedSheaf_false_eq (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  P.derivedSheaf_eq_single h Y false

/-- The twisted named complex is the finite root line in degree zero.
Source: the definition of `derivedSheaf` (blueprint: def-pur-relative-kummer-maps). -/
abbrev derivedSheaf_true_eq (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  P.derivedSheaf_eq_single h Y true

/-- The actual coordinate class with its coefficient complexes explicitly identified.
The equality maps are identities by the three preceding definition lemmas.
Source: the definition of `coordinateKummer` (blueprint: def-pur-relative-kummer-maps). -/
noncomputable def coordinateClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.derivedSheaf h (Punctured Y) false ⟶
      (P.derivedSheaf h (Punctured Y) true)⟦(1 : ℤ)⟧ :=
  eqToHom (P.derivedSheaf_false_eq h (Punctured Y)) ≫
    (P.coordinateKummer h Y a).hom ≫
      (eqToHom (P.derivedSheaf_true_eq h (Punctured Y)).symm)⟦(1 : ℤ)⟧'

/-- Canonical pullback on constants, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def constantPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ⟶
      P.constant X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.constantEtale Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient))

/-- Canonical pullback on the finite twist, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.twist h Y) ⟶
      P.twist h X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.twistEtale h Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (P.twistEtalePullback h f)

/-- Pullback of a coefficient object in the derived category. This is the standard
single-complex comparison followed by the canonical map on the actual sheaves.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor).obj
      (P.derivedSheaf h Y twisted) ⟶ P.derivedSheaf h X twisted :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
      (eqToHom (P.derivedSheaf_eq_single h Y twisted)) ≫
    Functor.mapWithComparison
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0)
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0)
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)
      (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) f).hom
      (X := P.coefficientSheaf h Y twisted) (Y := P.coefficientSheaf h X twisted)
      (match twisted with
        | true => P.twistPullback h f
        | false => P.constantPullback f) ≫
    eqToHom (P.derivedSheaf_eq_single h X twisted).symm

/-- The canonical unit with coefficients identified by their canonical pullback map.
Source: blueprint sk-prop-a1-kummer, clauses (1) and (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    P.derivedSheaf h Y twisted ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
        (P.derivedCoefficientPullback h f twisted)

/-- The edge-section map, obtained by transposing the actual coordinate class and
taking H0, followed by the standard H0(K[1])=H1(K) comparison. It is the A-linear map
whose value on 1 is the Leray edge image of kappa(t).
Source: blueprint sk-prop-a1-kummer, clause (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def kummerGenerator (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (eqToHom (P.derivedSheaf_false_eq h Y).symm ≫
        ((ProEtale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection Y) false ≫
            (P.coordinateClass h Y a))) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.derivedSheaf h (Punctured Y) true)) ≫
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).shiftIso
        (1 : ℤ) 0 1 (add_zero 1)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true))

attribute [local irreducible] derivedCoefficientPullback coordinateClass
  relativeUnit kummerGenerator derivedSheaf coefficientSheaf constant twist

/-- The assertions in clauses (1)-(3), with the actual specified maps. No finite-type
condition is built into this predicate, so it also applies to geometric fibres.
Source: blueprint sk-prop-a1-kummer, clauses (1)-(3)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def RelativeKummerConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  IsIso (P.relativeUnit h (lineProjection Y) false) ∧
  IsIso (P.relativeUnit h (lineProjection Y) true) ∧
  (∀ (m : ℕ), 0 < m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (lineProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Line Y) true)))) ∧
  IsIso ((DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (P.relativeUnit h (puncturedProjection Y) true)) ∧
  IsIso (P.kummerGenerator h Y a) ∧
  ∀ (m : ℕ), 2 ≤ m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)))

/-- Naturality of the actual coordinate Kummer class, under the specified coefficient
and shift identifications. Naming this equation avoids repeatedly normalizing its
localization morphism types when constructing the base-change conjunction.
Source: blueprint sk-prop-a1-kummer, clause (4)
(blueprint: def-pur-relative-kummer-maps). -/
@[irreducible] noncomputable def CoordinateKummerNaturality (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.coordinateClass h Y a) ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.derivedSheaf h (Punctured Y) true) ≫
    (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
      P.derivedCoefficientPullback h (puncturedMap g) false ≫
        (P.coordinateClass h Y' (g ≫ a))

/-- Clause (4): naturality of the actual coordinate class and invertibility of the
canonical exchange mates. Their targets use the canonical coefficient pullback
identifications; invertibility is equivalently tested before those identifications.
Source: blueprint sk-prop-a1-kummer, clause (4)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def KummerBaseChangeConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  P.CoordinateKummerNaturality h g a ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
      (P.derivedSheaf h (Line Y) true)) ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.derivedSheaf h (Punctured Y) true))

end WeilConjectures.PurityFiniteSetting
```

## Users

The original inventory comes from `tools/downstream.py` for each of the seven moved
names, with duplicate rows combined. Each existing transitive consumer retains the
same actual maps after the reflexive coefficient identifications, so its statement
is neither weakened nor strengthened. Only the item is adapted; no existing module
held by another group is edited. The last four rows are new modules in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.ChernFlagFormula | G4 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.LocalizedTopChern | E5 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDncComparisons | G3 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.SmoothPurityMap | R2 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.WeilFourierInversion | J6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.WeilOne | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| TargetsCheck | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.Statement | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityRelativeKummer | F4 | Same actual maps and predicates; existing signatures unchanged. |
| Sheaf.Paper.PurityRelativeKummerMaps | F4 (new in this delivery) | New dependency using the explicit canonical coefficient identifications. |
| Sheaf.Paper.PurityRelativeLineCohomology | F4 (new in this delivery) | New dependency using the explicit canonical coefficient identifications. |
| Sheaf.Paper.PurityRelativePuncturedCohomology | F4 (new in this delivery) | New dependency using the explicit canonical coefficient identifications. |
| Sheaf.Paper.PurityRelativeKummerExchange | F4 (new in this delivery) | New dependency using the explicit canonical coefficient identifications. |

## Status

landed 20261019T192725-L-1860074 2026-10-19 (merge of deliver/F4/Sheaf.Paper.PurityRelativeKummer)
