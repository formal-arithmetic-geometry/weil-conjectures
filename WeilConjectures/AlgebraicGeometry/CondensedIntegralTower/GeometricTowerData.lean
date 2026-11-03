/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralTowerStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-! # Coordinates for the geometric adjunction in condensed towers
Source: latest blueprint sk-prop-sp-tower-geometric, statement (10.17) and proof.
All systems are strict systems before localization. No normalization is imposed here.
(blueprint: sk-prop-sp-tower-geometric)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
attribute [instance] TowerSupport.openAdditive TowerSupport.openLimits
  TowerSupport.openColimits TowerSupport.properAdditive

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- Geometric tower adjunction, finite units/counits and actual reduction transitions.
The fields describe whole tower maps; equality of arbitrary derived maps is never inferred
from equality of evaluations. Source: sk-prop-sp-tower-geometric, (10.17) and following
sentence (blueprint: sk-prop-sp-tower-geometric). -/
structure GeometricAdjunction (DX : Model l E X) (DY : Model l E Y)
    (c : Compactification f) where
  construction : TowerSupport l E c
  supportClosed : ∀ C : CtfTowers l E X,
    ConstructibleTowers l E Y ((construction.functor l E c).obj C.obj)
  right : CtfTowers l E Y ⥤ CtfTowers l E X
  adjunction : ObjectProperty.lift _
    ((ConstructibleTowers l E X).ι ⋙ construction.functor l E c) supportClosed ⊣ right
  finite : FiniteAdjunctions l E DX DY c
  supportLevels : ∀ n,
    ObjectProperty.lift _ ((ConstructibleTowers l E X).ι ⋙ construction.functor l E c)
      supportClosed ⋙ ctfEvaluation l E Y n ≅
        ctfEvaluation l E X n ⋙ finite.support l E n
  rightLevels : ∀ n,
    right ⋙ ctfEvaluation l E X n ≅ ctfEvaluation l E Y n ⋙ finite.right n
  unit : ∀ n (C : CtfTowers l E X),
    (ctfEvaluation l E X n).map (adjunction.unit.app C) ≫
      (rightLevels n).hom.app _ ≫
      (finite.right n).map ((supportLevels n).hom.app C) =
        (finite.adjunction n).unit.app ((ctfEvaluation l E X n).obj C)
  counit : ∀ n (C : CtfTowers l E Y),
    (supportLevels n).inv.app (right.obj C) ≫
      (ctfEvaluation l E Y n).map (adjunction.counit.app C) =
        (finite.support l E n).map ((rightLevels n).hom.app C) ≫
          (finite.adjunction n).counit.app ((ctfEvaluation l E Y n).obj C)
  /-- Invertibility of the specified exceptional coefficient mate, including identities. -/
  finiteMateIso : ∀ {m n : ℕ} (h : m ≤ n) (K : FiniteCtf l E Y n),
    IsIso (finite.mate l E h K)
  /-- The whole compact-support comparison, normalized by the actual quotient maps.
  This is constructed before the tower right adjoint and does not assert its normalization. -/
  integralComparison : ∃ b :
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (DerivedNakayama.integerRing l E) c ⋙ DY.red ≅
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X).ι ⋙
        DX.red ⋙ construction.functor l E c,
    ∀ (n : ℕ) (M : Dbc l E X)
      (hM : ConstructibleTowers l E X (DX.red.obj M.obj)),
      (Ev l E Y n).map (b.hom.app M) ≫
        (((supportLevels n).hom.app ⟨DX.red.obj M.obj, hM⟩)).hom =
      (sectionLevels l E Y DY n).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (DerivedNakayama.integerRing l E) c).obj M.obj) ≫
        (sectionSupportCoefficientMap l E c n).app M.obj ≫
        (finiteSupport l E c n).map ((sectionLevels l E X DX n).inv.app M.obj)
  /-- The scalar square is the one induced by the actual support-tower transitions. -/
  supportReduction : ∀ {m n : ℕ} (h : m ≤ n) (C : CtfTowers l E X),
    (finite.scalarY l E h).map ((supportLevels n).inv.app C) ≫
      towerReduction l E Y DY h (finite.scalarY l E h) rfl
        ((ObjectProperty.lift _
          ((ConstructibleTowers l E X).ι ⋙ construction.functor l E c)
          supportClosed).obj C) ≫ (supportLevels m).hom.app C =
    (finite.baseChange h).inv.app ((ctfEvaluation l E X n).obj C) ≫
      (finite.support l E m).map
        (towerReduction l E X DX h (finite.scalarX l E h) rfl C)
  reduction : ∀ {m n : ℕ} (h : m ≤ n) (C : CtfTowers l E Y),
    towerReduction l E X DX h (finite.scalarX l E h) rfl (right.obj C) ≫
      (rightLevels m).hom.app C =
    (finite.scalarX l E h).map ((rightLevels n).hom.app C) ≫
      finite.mate l E h ((ctfEvaluation l E Y n).obj C) ≫
      (finite.right m).map
        (towerReduction l E Y DY h (finite.scalarY l E h) rfl C)

/-- Compact support, finite adjunctions and their actual scalar-reduction square.
This packages the compactification part of the geometric construction, before any
tower right adjoint or representing pairs are constructed.
Source: blueprint sk-prop-sp-tower-geometric, opening and transition paragraphs.
(blueprint: def-sp-condensed-geometric-tower-data) -/
structure GeometricSupport (DX : Model l E X) (DY : Model l E Y)
    (c : Compactification f) where
  construction : TowerSupport l E c
  supportClosed : ∀ C : CtfTowers l E X,
    ConstructibleTowers l E Y ((construction.functor l E c).obj C.obj)
  finite : FiniteAdjunctions l E DX DY c
  supportLevels : ∀ n,
    ObjectProperty.lift _ ((ConstructibleTowers l E X).ι ⋙ construction.functor l E c)
      supportClosed ⋙ ctfEvaluation l E Y n ≅
        ctfEvaluation l E X n ⋙ finite.support l E n
  /-- Invertibility of the specified exceptional coefficient mate, including identities. -/
  finiteMateIso : ∀ {m n : ℕ} (h : m ≤ n) (K : FiniteCtf l E Y n),
    IsIso (finite.mate l E h K)
  /-- The whole compact-support comparison, normalized by the actual quotient maps.
  This is constructed before the tower right adjoint and does not assert its normalization. -/
  integralComparison : ∃ b :
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (DerivedNakayama.integerRing l E) c ⋙ DY.red ≅
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X).ι ⋙
        DX.red ⋙ construction.functor l E c,
    ∀ (n : ℕ) (M : Dbc l E X)
      (hM : ConstructibleTowers l E X (DX.red.obj M.obj)),
      (Ev l E Y n).map (b.hom.app M) ≫
        (((supportLevels n).hom.app ⟨DX.red.obj M.obj, hM⟩)).hom =
      (sectionLevels l E Y DY n).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (DerivedNakayama.integerRing l E) c).obj M.obj) ≫
        (sectionSupportCoefficientMap l E c n).app M.obj ≫
        (finiteSupport l E c n).map ((sectionLevels l E X DX n).inv.app M.obj)
  /-- The scalar square is the one induced by the actual support-tower transitions. -/
  supportReduction : ∀ {m n : ℕ} (h : m ≤ n) (C : CtfTowers l E X),
    (finite.scalarY l E h).map ((supportLevels n).inv.app C) ≫
      towerReduction l E Y DY h (finite.scalarY l E h) rfl
        ((ObjectProperty.lift _
          ((ConstructibleTowers l E X).ι ⋙ construction.functor l E c)
          supportClosed).obj C) ≫ (supportLevels m).hom.app C =
    (finite.baseChange h).inv.app ((ctfEvaluation l E X n).obj C) ≫
      (finite.support l E m).map
        (towerReduction l E X DX h (finite.scalarX l E h) rfl C)

/-- The full-subcategory restriction of the actual compactification functor.
Source: blueprint sk-prop-sp-tower-geometric, opening paragraph.
(blueprint: def-sp-condensed-geometric-tower-data) -/
abbrev GeometricSupport.support {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (B : GeometricSupport l E DX DY c) :=
  ObjectProperty.lift _ ((ConstructibleTowers l E X).ι ⋙ B.construction.functor l E c)
    B.supportClosed

/-- Actual reduction is natural on the finite full subcategories.
Source: blueprint det-sp-coefficient-towers-abelian(3).
(blueprint: def-sp-condensed-geometric-tower-data) -/
def ctfReduction (T : Scheme.{u}) (D : Model l E T) {m n : ℕ} (h : m ≤ n)
    (S : FiniteCtf l E T n ⥤ FiniteCtf l E T m)
    (hS : S ⋙ (finiteCtf l E T m).ι =
      (finiteCtf l E T n).ι ⋙
        SheafOfModules.systemDerivedTensor D.scalar (rings l E T) h) :
    ctfEvaluation l E T n ⋙ S ⟶ ctfEvaluation l E T m where
  app C := towerReduction l E T D h S hS C
  naturality {C C'} g := by
    apply ObjectProperty.hom_ext
    dsimp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      towerReduction, ObjectProperty.homMk_hom]
    have he := (eqToHom hS).naturality ((ctfEvaluation l E T n).map g)
    simp only [eqToHom_app, Functor.comp_map, ObjectProperty.ι_map] at he
    rw [← Category.assoc, he, Category.assoc]
    have hr := (D.reduction h).naturality g.hom
    simpa only [Functor.comp_map, Functor.comp_obj, ctfEvaluation,
      ObjectProperty.lift_map, ObjectProperty.homMk_hom, ObjectProperty.ι_map,
      Category.assoc, Ev] using
      congrArg (fun z ↦ eqToHom
        (congrArg (fun F ↦ F.obj ((ctfEvaluation l E T n).obj C)) hS) ≫ z) hr


end AlgebraicGeometry.ProEtale.CondensedIntegralTower
