/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # The open-cover triangle of varying-coefficient towers

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-triangle-data).

Index `n : ℕ` denotes the paper's positive coefficient level `n + 1`.
The sequence-site presentation `SpTowerShriek.D` is the ordinary derived category
of strict towers, identified sectionwise with `spCoefficientTowers` by `Base.realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u v₀ v₁ v₂ u₀ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- The nested-open counit, written as its uniquely determined adjunction transpose.
Under the composite-left-adjoint identification this is extension of the inner counit.
Source: latest blueprint, tower-geometric Gluing paragraph; Stacks 03DI--03DJ.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def nestedCounit {C : Type u₀} {A : Type u₁} {B : Type u₂}
    [Category.{v₀} C] [Category.{v₁} A] [Category.{v₂} B]
    {r : C ⥤ A} {s : A ⥤ B} {t : C ⥤ B}
    {L : A ⥤ C} {K : B ⥤ C} (a : L ⊣ r) (b : K ⊣ t)
    (c : r ⋙ s ≅ t) (M : C) : K.obj (t.obj M) ⟶ L.obj (r.obj M) :=
  (b.homEquiv _ _).symm
    (c.inv.app M ≫ s.map (a.unit.app (r.obj M)) ≫ c.hom.app (L.obj (r.obj M)))

/-- The specified exact open restriction followed by extension by zero.
Source: latest blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
abbrev support {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SpTowerShriek.pull l E b (o.geometry j) ⋙ SpTowerShriek.openD l E b (o.openOp j)

/-- The nested-open arrow in the actual unbounded derived tower category.
Source: latest blueprint, tower-geometric Gluing paragraph; Stacks 03DI--03DJ.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def alpha {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (M : SpTowerShriek.D l E X) :
    (support l E b o k).obj M ⟶ (support l E b o j).obj M :=
  nestedCounit (o.openOp j).derivedAdjunction (o.openOp k).derivedAdjunction
    (o.comp a j ≪≫ eqToIso (congrArg
      (fun h ↦ SpTowerShriek.pull l E b (o.geometry h)) w)) M

/-- The finite counterpart uses precisely the localized ordinary finite open adjunction.
Source: latest blueprint, tower-geometric Levels paragraph; Stacks 03DI--03DJ.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def finiteAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  letI : Finite (SpTowerShriek.R l E n) := b.finite n
  (SpTowerShriek.finiteOpenAdjunction l E b j n).mapExactDerivedCategory

/-- Restriction and extension by zero with the actual finite coefficient ring.
Source: latest blueprint, tower-geometric Levels paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
abbrev finiteSupport {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  letI : Finite (SpTowerShriek.R l E n) := b.finite n
  proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j ⋙
    sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j

/-- The finite nested-open arrow, with the canonical pullback compositor.
Source: latest blueprint, tower-geometric Levels paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def finiteAlpha {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (w : a ≫ j = k) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    (finiteSupport l E b k n).obj M ⟶ (finiteSupport l E b j n).obj M :=
  letI : Finite (SpTowerShriek.R l E n) := b.finite n
  nestedCounit (finiteAdjunction l E b j n) (finiteAdjunction l E b k n)
    (proEtaleConstantRingPullbackComposition a j (SpTowerShriek.R l E n) ≪≫
      eqToIso (congrArg (fun h ↦
        proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) h) w)) M

/-- The exact evaluation comparison of open restriction followed by extension.
Source: latest blueprint, tower-geometric Levels paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def supportEvaluation {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    support l E b o j ⋙ SpTowerShriek.Ev l E X n ≅
      SpTowerShriek.Ev l E X n ⋙ finiteSupport l E b j n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (SpTowerShriek.openEvaluation l E b (o.openOp j) n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((o.geometry j).pullEvaluation n) _ ≪≫
    Functor.associator _ _ _

/-- The signed intersection arrow into the binary biproduct.
Source: latest blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def first {W U V X : Scheme.{u}} (aU : W ⟶ U) (aV : W ⟶ V)
    (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW) (M : SpTowerShriek.D l E X) :=
  biprod.lift (alpha l E b o aU jU jW wU M) (-alpha l E b o aV jV jW wV M)

/-- The sum of the two specified open counits.
Source: latest blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
def second {U V X : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X)
    [IsOpenImmersion jU] [IsOpenImmersion jV] (M : SpTowerShriek.D l E X) :=
  biprod.desc ((o.openOp jU).derivedAdjunction.counit.app M)
    ((o.openOp jV).derivedAdjunction.counit.app M)

end AlgebraicGeometry.ProEtale.TowerOpenCover
