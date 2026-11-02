/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralTowerStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # The geometric adjunction in the current condensed tower category
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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite-level section/internal equivalence, with its actual scalar actions.
Source: det-sp-coefficient-towers-abelian (blueprint: sk-prop-sp-tower-geometric). -/
abbrev finiteSections (T : Scheme.{u}) (n : ℕ) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (finiteRing l E n) T)

/-- The inverse section equivalence is additive. Source: the exact section equivalence
(blueprint: sk-prop-sp-tower-geometric). -/
instance inverseSectionsAdditive (T : Scheme.{u}) (n : ℕ) :
    (finiteSections l E T n).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Ordinary level evaluation; its derived version is localization of this exact functor.
Source: det-sp-coefficient-towers-abelian (blueprint: sk-prop-sp-tower-geometric). -/
abbrev ev (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E T) n

/-- Evaluation into the section-module derived category.
Source: det-sp-coefficient-towers-abelian (blueprint: sk-prop-sp-tower-geometric). -/
abbrev Ev (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T) n

/-- Bounded constructible finite-Tor objects at a finite coefficient level.
Source: sk-def-sp-normalized-towers (blueprint: sk-prop-sp-tower-geometric). -/
def finiteCtf (T : Scheme.{u}) (n : ℕ) : ObjectProperty
    (DerivedCategory (SheafOfModules.systemLevel.{u + 1, u, u + 1} (rings l E T) n)) :=
  fun K ↦ constantModelBoundedConstructible (finiteRing l E n) T
      ((finiteSections l E T n).inverse.mapDerivedCategory.obj K) ∧
    DerivedCategory.finiteTorAmplitude _
      ((finiteSections l E T n).inverse.mapDerivedCategory.obj K)

/-- The finite categories used by the geometric adjunction.
Source: sk-prop-sp-tower-geometric (blueprint: sk-prop-sp-tower-geometric). -/
abbrev FiniteCtf (T : Scheme.{u}) (n : ℕ) := (finiteCtf l E T n).FullSubcategory

/-- Actual evaluation of a uniformly bounded constructible tower, retaining its object.
Source: sk-def-sp-normalized-towers (blueprint: sk-prop-sp-tower-geometric). -/
def ctfEvaluation (T : Scheme.{u}) (n : ℕ) : CtfTowers l E T ⥤ FiniteCtf l E T n :=
  ObjectProperty.lift _ ((ConstructibleTowers l E T).ι ⋙ Ev l E T n) (fun C ↦ by
    refine ⟨C.property.1 n, ?_⟩
    obtain ⟨a, b, c, d, _, _, h⟩ := C.property.2
    exact ⟨c, d, (h n).1⟩)

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The actual finite compactification functor in section coordinates.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
def finiteSupport (c : Compactification f) (n : ℕ) :=
  (finiteSections l E X n).inverse.mapDerivedCategory ⋙
    CondensedRing.rightDerivedLowerShriekOfCompactification (finiteRing l E n) c ⋙
      (finiteSections l E Y n).functor.mapDerivedCategory

/-- The ordinary open leg in section coordinates.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
def finiteOpen (c : Compactification f) (n : ℕ) :=
  (finiteSections l E X n).inverse ⋙
    CondensedRing.openImmersionLowerShriek (finiteRing l E n) c.i ⋙
      (finiteSections l E c.Z n).functor

/-- The ordinary proper leg in section coordinates.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
def finiteProper (c : Compactification f) (n : ℕ) :=
  (finiteSections l E c.Z n).inverse ⋙
    CondensedRing.lowerStar (finiteRing l E n) c.g ⋙
      (finiteSections l E Y n).functor

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- Coordinates for D(j_!) followed by Rp_* on strict systems. Level isomorphisms are
identity maps on sections, and HEq of the entire transition functions fixes the actual
semilinear transitions, including identities. The proper factor is its universal total
right derived functor, not the derived functor of the composite ordinary lower shriek.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
structure TowerSupport (c : Compactification f) where
  openLeg : Towers l E X ⥤ Towers l E c.Z
  [openAdditive : openLeg.Additive]
  [openLimits : PreservesFiniteLimits openLeg]
  [openColimits : PreservesFiniteColimits openLeg]
  properLeg : Towers l E c.Z ⥤ Towers l E Y
  [properAdditive : properLeg.Additive]
  openLevels : ∀ n, openLeg ⋙ ev l E c.Z n ≅ ev l E X n ⋙ finiteOpen l E c n
  properLevels : ∀ n, properLeg ⋙ ev l E Y n ≅ ev l E c.Z n ⋙ finiteProper l E c n
  openSections : ∀ (n : ℕ) (M : Towers l E X) (U : c.Z.ProEtᵒᵖ)
    (x : ((openLeg.obj M).level n).val.obj U),
    HEq ((((openLevels n).hom.app M).val.app U) x) x
  properSections : ∀ (n : ℕ) (M : Towers l E c.Z) (U : Y.ProEtᵒᵖ)
    (x : ((properLeg.obj M).level n).val.obj U),
    HEq ((((properLevels n).hom.app M).val.app U) x) x
  openTransition : ∀ (M : Towers l E X) {m n : ℕ} (h : m ≤ n) (U : c.Z.ProEtᵒᵖ),
    HEq (((openLeg.obj M).transition h).val.app U)
      (((finiteOpen l E c n).map (M.transition h)).val.app U)
  properTransition : ∀ (M : Towers l E c.Z) {m n : ℕ} (h : m ≤ n) (U : Y.ProEtᵒᵖ),
    HEq (((properLeg.obj M).transition h).val.app U)
      (((finiteProper l E c n).map (M.transition h)).val.app U)
  derivedProper : DerivedTowers l E c.Z ⥤ DerivedTowers l E Y
  properUnit : properLeg.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ derivedProper
  properUniversal : derivedProper.IsRightDerivedFunctor properUnit
    (HomologicalComplex.quasiIso (Towers l E c.Z) (.up ℤ))

attribute [instance] TowerSupport.openAdditive TowerSupport.openLimits
  TowerSupport.openColimits TowerSupport.properAdditive

/-- Tower compact support is exactly the two-factor compactification construction.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
def TowerSupport.functor (c : Compactification f) (S : TowerSupport l E c) :=
  S.openLeg.mapDerivedCategory ⋙ S.derivedProper

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- The finite adjunctions and scalar reductions, on the finite constructible finite-Tor
categories. All preservation facts are output fields, never assumptions of the theorem.
Source: sk-prop-sf-rf-shriek-preservation and sk-lem-sp-reduction
(blueprint: sk-prop-sp-tower-geometric). -/
structure FiniteAdjunctions (DX : Model l E X) (DY : Model l E Y)
    (c : Compactification f) where
  supportClosed : ∀ n (K : FiniteCtf l E X n),
    finiteCtf l E Y n ((finiteSupport l E c n).obj K.obj)
  scalarClosedX : ∀ {m n : ℕ} (h : m ≤ n) (K : FiniteCtf l E X n),
    finiteCtf l E X m
      ((SheafOfModules.systemDerivedTensor DX.scalar (rings l E X) h).obj K.obj)
  scalarClosedY : ∀ {m n : ℕ} (h : m ≤ n) (K : FiniteCtf l E Y n),
    finiteCtf l E Y m
      ((SheafOfModules.systemDerivedTensor DY.scalar (rings l E Y) h).obj K.obj)
  right : ∀ n, FiniteCtf l E Y n ⥤ FiniteCtf l E X n
  adjunction : ∀ n, ObjectProperty.lift _
    ((finiteCtf l E X n).ι ⋙ finiteSupport l E c n) (supportClosed n) ⊣ right n
  baseChange : ∀ {m n : ℕ} (h : m ≤ n),
    ObjectProperty.lift _ ((finiteCtf l E X n).ι ⋙
      SheafOfModules.systemDerivedTensor DX.scalar (rings l E X) h) (scalarClosedX h) ⋙
      ObjectProperty.lift _ ((finiteCtf l E X m).ι ⋙ finiteSupport l E c m)
        (supportClosed m) ≅
    ObjectProperty.lift _ ((finiteCtf l E X n).ι ⋙ finiteSupport l E c n)
      (supportClosed n) ⋙
      ObjectProperty.lift _ ((finiteCtf l E Y n).ι ⋙
        SheafOfModules.systemDerivedTensor DY.scalar (rings l E Y) h) (scalarClosedY h)

/-- The bounded finite support functor, with the same underlying objects and maps.
Source: sk-prop-sf-rf-shriek-preservation (blueprint: sk-prop-sp-tower-geometric). -/
def FiniteAdjunctions.support {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (A : FiniteAdjunctions l E DX DY c) (n : ℕ) :=
  ObjectProperty.lift _ ((finiteCtf l E X n).ι ⋙ finiteSupport l E c n) (A.supportClosed n)

/-- Actual derived scalar reduction on the source finite categories.
Source: sk-lem-sp-reduction (blueprint: sk-prop-sp-tower-geometric). -/
def FiniteAdjunctions.scalarX {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (A : FiniteAdjunctions l E DX DY c) {m n : ℕ} (h : m ≤ n) :=
  ObjectProperty.lift _ ((finiteCtf l E X n).ι ⋙
    SheafOfModules.systemDerivedTensor DX.scalar (rings l E X) h) (A.scalarClosedX h)

/-- Actual derived scalar reduction on the target finite categories.
Source: sk-lem-sp-reduction (blueprint: sk-prop-sp-tower-geometric). -/
def FiniteAdjunctions.scalarY {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (A : FiniteAdjunctions l E DX DY c) {m n : ℕ} (h : m ≤ n) :=
  ObjectProperty.lift _ ((finiteCtf l E Y n).ι ⋙
    SheafOfModules.systemDerivedTensor DY.scalar (rings l E Y) h) (A.scalarClosedY h)

/-- The counit mate c_{n,m}, defined by transposition of the scalar-reduced counit.
Source: sk-lem-sp-reduction, displayed comparison (blueprint: sk-prop-sp-tower-geometric). -/
def FiniteAdjunctions.mate {DX : Model l E X} {DY : Model l E Y}
    {c : Compactification f} (A : FiniteAdjunctions l E DX DY c)
    {m n : ℕ} (h : m ≤ n) (K : FiniteCtf l E Y n) :
    (A.scalarX l E h).obj ((A.right n).obj K) ⟶
      (A.right m).obj ((A.scalarY l E h).obj K) :=
  (A.adjunction m).homEquiv _ _
    ((A.baseChange h).hom.app ((A.right n).obj K) ≫
      (A.scalarY l E h).map ((A.adjunction n).counit.app K))

/-- The actual reduction morphism of a tower, now in its finite full subcategories.
Source: det-sp-coefficient-towers-abelian(3) (blueprint: sk-prop-sp-tower-geometric). -/
def towerReduction (T : Scheme.{u}) (D : Model l E T)
    {m n : ℕ} (h : m ≤ n)
    (S : FiniteCtf l E T n ⥤ FiniteCtf l E T m)
    (hS : S ⋙ (finiteCtf l E T m).ι =
      (finiteCtf l E T n).ι ⋙
        SheafOfModules.systemDerivedTensor D.scalar (rings l E T) h)
    (C : CtfTowers l E T) :
    S.obj ((ctfEvaluation l E T n).obj C) ⟶ (ctfEvaluation l E T m).obj C :=
  ObjectProperty.homMk
    ((eqToHom (congrArg (fun F ↦ F.obj ((ctfEvaluation l E T n).obj C)) hS)) ≫
      (D.reduction h).app C.obj)

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

/-- The dependency's specified compactificationOverField, with the Scheme/Over
coordinates written out. This makes no new Nagata choice.
Source: sk-lem-sp-tower-bound (blueprint: sk-prop-sp-tower-geometric). -/
def fieldCompactification (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] : Compactification f :=
  letI : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  letI : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  letI : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  letI : QuasiCompact (Over.mk (Y ↘ Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  letI : IsSeparated (Over.mk (Y ↘ Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  CondensedRing.compactificationOverField (k := k)
    (Over.homMk (U := Over.mk (X ↘ Spec (.of k)))
      (V := Over.mk (Y ↘ Spec (.of k))) f (comp_over f (Spec (.of k))))

/-- Smooth geometric adjunction on uniformly bounded constructible finite-Tor towers.
Source: latest blueprint sk-prop-sp-tower-geometric, full statement and proof.
Proof: form the exact levelwise extension by zero and the proper system pushforward;
localize the former and right derive the latter. Uniform bounds are the compactification
bound. The Kummer sequence and its Chern and diagonal classes are maps in strict systems.
The projective-line trace and diagonal give the unit/counit. Etale charts and two-open
Mayer--Vietoris gluing give representing pairs for a smooth morphism. Their uniform
cohomological and Tor intervals are the unions of the finitely many chart intervals.
Evaluation sends these pairs to the finite representing pairs. Uniqueness identifies
both maps with the finite unit and counit. Transpose the transition compatibility of
the whole tower counit: this is precisely mate followed by f_m^! of the actual reduction,
including m=n. No normalization assumption is used. -/
theorem sp_tower_geometric_statement
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Nonempty (GeometricAdjunction l E (model l E X) (model l E Y)
      (fieldCompactification k X Y f)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
