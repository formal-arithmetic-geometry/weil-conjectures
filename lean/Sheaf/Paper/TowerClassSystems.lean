/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Systems for canonical tower classes

Source: blueprint main-20261015, sec-smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-systems).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The small pro-etale site fits in its object universe without changing its
morphism universe. Source: the site size convention (blueprint: def-sp-tower-class-systems). -/
instance proEtaleSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

/-- The sequence site has the same object bound as the small pro-etale site.
Source: inverse-system topos (blueprint: def-sp-tower-class-systems). -/
instance sequenceSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × T.ProEt) :=
  essentiallySmallSelf.{0} _

/-- Fix the coefficient-universe sheafification witness explicitly.
Source: small-site size convention (blueprint: def-sp-tower-class-systems). -/
instance (priority := 4000) ringSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

/-- Towers of abelian sheaves. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
abbrev Ab (T : Scheme.{u}) := ℕᵒᵖ ⥤ DiagonalAb T

/-- The existing abelian structure on towers, shared by name to avoid rebuilding
its sheafification witnesses. Source: classes (1)--(2)
(blueprint: def-sp-tower-class-systems). -/
instance (priority := 3000) towerAbelian (T : Scheme.{u}) : Abelian (Ab T) :=
  inferInstance

/-- Ordinary localization. Source: classes (1)--(2)
(blueprint: def-sp-tower-class-systems). -/
instance abDerived (T : Scheme.{u}) : HasDerivedCategory.{u + 2} (Ab T) :=
  HasDerivedCategory.standard _

/-- Ext in the same localization. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance abExt (T : Scheme.{u}) : HasExt.{u + 2} (Ab T) := HasExt.standard (Ab T)

/-- Constant towers. Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def constant (T : Scheme.{u}) : DiagonalAb T ⥤ Ab T :=
  Functor.const (ℕᵒᵖ) (C := DiagonalAb T)

/-- Exactness of the actual constant-system functor.
Source: classes (2) (blueprint: def-sp-tower-class-systems).
Proof: limits and colimits in the functor category are levelwise, so the
constant-system functor preserves them, including the additive group laws. -/
theorem constant_exact (T : Scheme.{u}) :
    (constant T).Additive ∧ PreservesFiniteLimits (constant T) ∧
      PreservesFiniteColimits (constant T) := by
  sorry

/-- Additivity of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantAdditive (T : Scheme.{u}) : (constant T).Additive :=
  (constant_exact T).1

/-- Left exactness of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantLimits (T : Scheme.{u}) : PreservesFiniteLimits (constant T) :=
  (constant_exact T).2.1

/-- Right exactness of constant systems. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
instance constantColimits (T : Scheme.{u}) : PreservesFiniteColimits (constant T) :=
  (constant_exact T).2.2

/-- Integral coefficients. Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev integers (T : Scheme.{u}) :=
  (constant T).obj ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The actual roots tower. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
abbrev roots (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)

/-- Power-transition units. Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
def powerUnits (l : ℕ) (T : Scheme.{u}) : Ab T :=
  Functor.ofOpSequence (X := fun _ : ℕ ↦ Scheme.proEtaleUnitsSheaf T)
    (fun _ ↦ Scheme.proEtaleUnitsPower T l)

/-- Identity-transition units. Source: classes (1)
(blueprint: def-sp-tower-class-systems). -/
abbrev units (T : Scheme.{u}) := (constant T).obj (Scheme.proEtaleUnitsSheaf T)

/-- The exact sequence uses the actual inclusions and power maps at every positive level.
Source: classes (1) (blueprint: def-sp-tower-class-systems). -/
structure Kummer (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) where
  inclusion : roots l T ⟶ powerUnits l T
  inclusion_eq : ∀ n : ℕ,
    inclusion.app (op n) = Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1))
  power : powerUnits l T ⟶ units T
  power_eq : ∀ n : ℕ, power.app (op n) = Scheme.proEtaleUnitsPower T (l ^ (n + 1))
  zero : inclusion ≫ power = 0
  exact : (ShortComplex.mk inclusion power zero).ShortExact

/-- Ringed sequence-site systems, with the dependency's exact site universes.
Source: coefficient towers and classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev Systems (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  SemilinearSections.Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)

/-- Share the published abelian witness of the ringed sequence-site category.
Source: classes (2), the recorded system model (blueprint: def-sp-tower-class-systems). -/
instance (priority := 5000) systemsAbelian (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian (Systems T B) :=
  SemilinearSections.moduleAbelian.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op))

/-- The ordinary derived category of these systems.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
abbrev D (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  DerivedCategory (Systems T B)

/-- The actual coefficient module, not a free source-object parameter.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def coefficient (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) : Systems T B :=
  SheafOfModules.unit (SemilinearSections.ring.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)))

/-- Coefficients in degree zero. Source: classes (2)
(blueprint: def-sp-tower-class-systems). -/
abbrev unit (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  (DerivedCategory.singleFunctor (Systems T B) 0).obj (coefficient T B)

/-- The canonical forgetful functor is specified on every section, restriction and map.
These equalities identify a functor, rather than assuming a free map between categories.
Source: classes (2), modules in the inverse-system topos
(blueprint: def-sp-tower-class-systems). -/
structure Forget (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) where
  F : Systems T B ⥤ Ab T
  sections : ∀ (M : Systems T B) (n : ℕ) (U : T.ProEtᵒᵖ),
    ((F.obj M).obj (op n)).obj.obj U =
      AddCommGrpCat.of (M.val.obj (op (n, U.unop)))
  restrictions : ∀ (M : Systems T B) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
    HEq ((((F.obj M).obj (op n)).obj.map f).hom)
      ((M.val.map (Prod.mkHom (𝟙 n) f.unop).op).hom.toAddMonoidHom)
  transitions : ∀ (M : Systems T B) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ),
    HEq ((((F.obj M).map (homOfLE h).op).hom.app U).hom)
      ((M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom.toAddMonoidHom)
  morphisms : ∀ {M N : Systems T B} (f : M ⟶ N) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq ((((F.map f).app (op n)).hom.app U).hom)
      ((f.val.app (op (n, U.unop))).hom.toAddMonoidHom)
  [additive : F.Additive]
  [limits : PreservesFiniteLimits F]
  [colimits : PreservesFiniteColimits F]

attribute [instance] Forget.additive Forget.limits Forget.colimits

/-- The quotient of the constant integer tower is fixed on every constant section.
Source: classes (2), coefficient unit (blueprint: def-sp-tower-class-systems).
Proof: at each level the integer acts on the coefficient unit by its integer
multiple of one. This commutes with restrictions and quotient transitions;
the constant-sheaf universal property gives existence and uniqueness. -/
theorem integerGenerator_existsUnique (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) :
    ∃! f : integers T ⟶ F.F.obj (coefficient T B),
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
        HEq (((f.app (op n)).hom.app U)
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k))
          (k.down : (B.obj (op n)).obj.obj U) := by
  sorry

/-- The canonical integer-to-coefficient quotient, fixed by constant generators.
Source: classes (2) (blueprint: def-sp-tower-class-systems). -/
def integerGenerator (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : integers T ⟶ F.F.obj (coefficient T B) :=
  (integerGenerator_existsUnique T B F).exists.choose

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
