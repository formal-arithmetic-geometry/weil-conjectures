/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
public import Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Exact.Basic

/-! # Representing counits for binary gluing of coefficient towers

Source: blueprint, latest, sec-smooth-purity, det-sp-tower-gluing, Gluing paragraph
(blueprint: lem-sp-tower-binary-counit-representability).

We use the published ringed sequence-site presentation of ordinary strict towers.
All full-subcategory conditions are transported from the existing unnormalized
constructible finite-Tor tower predicate. Index n means positive level n+1.
Compact support on an open is normalized as open extension followed by F_h;
sequenceOpenComposition identifies it with the precomposed compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₀ v₁ w₀ w₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerBinaryCounit

open SpTowerShriek SpTowerBinaryCtfFibre

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b) (q : SpTowerCalculus.Coordinates l E b)

/-- The existing unnormalized predicate in the published sequence-site coordinates.
Source: blueprint, standing C_T convention
(blueprint: lem-sp-tower-binary-counit-representability). -/
abbrev good (T : Scheme.{u}) (M : D l E T) : Prop :=
  spConstructibleTorTowers l E T (q.abelian T)
    ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj M)

/-- The canonical exact open-extension functor.
Source: blueprint, Gluing, j_D! (blueprint: lem-sp-tower-binary-counit-representability). -/
abbrev extension {Z : Scheme.{u}} (U : Z.Opens) := openD l E b (o.openOp U.ι)

/-- F_D in the open-composition normalization, using the same compactification for h.
Source: blueprint, Gluing, F_(h|D) = F_h j_D!
(blueprint: lem-sp-tower-binary-counit-representability). -/
abbrev support {Z Y : Scheme.{u}} {h : Z ⟶ Y} (c : Compactification h) (U : Z.Opens) :=
  extension l E b o U ⋙ F l E b o c

/-- A representing counit, tested on precisely the recorded full subcategory.
Source: blueprint, Gluing, local pairs
(blueprint: lem-sp-tower-binary-counit-representability). -/
def Represents {T Y : Scheme.{u}} (F₀ : D l E T ⥤ D l E Y)
    (P : D l E T) (K : D l E Y) (e : F₀.obj P ⟶ K) : Prop :=
  ∀ N : D l E T, good l E b q T N →
    Function.Bijective (fun a : N ⟶ P ↦ F₀.map a ≫ e)

/-- The nested-open map, defined by the canonical open adjunctions, not by evaluation.
Source: blueprint, Gluing, nested counits
(blueprint: lem-sp-tower-binary-counit-representability). -/
def nested {Z : Scheme.{u}} {U V : Z.Opens} (i : U ≤ V) (P : D l E V.toScheme) :
    (extension l E b o U).obj ((restrictionBetween l E b o i).obj P) ⟶
      (extension l E b o V).obj P :=
  ((o.openOp U.ι).derivedAdjunction.homEquiv _ _).symm
    ((restrictionBetween l E b o i).map ((o.openOp V.ι).derivedAdjunction.unit.app P) ≫
      (restrictionComp l E b o i).inv.app ((extension l E b o V).obj P))

/-- Restrict a representing counit using the specified nested-open counit.
Source: blueprint, Gluing, restriction pairs
(blueprint: lem-sp-tower-binary-counit-representability). -/
def restrictedCounit {Z Y : Scheme.{u}} {h : Z ⟶ Y} (c : Compactification h)
    {U V : Z.Opens} (i : U ≤ V) (P : D l E V.toScheme) (K : D l E Y)
    (e : (support l E b o c V).obj P ⟶ K) :
    (support l E b o c U).obj ((restrictionBetween l E b o i).obj P) ⟶ K :=
  (F l E b o c).map (nested l E b o i P) ≫ e

/-- The overlap term of the signed open-cover triangle.
Source: blueprint, Gluing, A_M (blueprint: lem-sp-tower-binary-counit-representability). -/
abbrev coverA {Z : Scheme.{u}} (U V : Z.Opens) (M : D l E Z) :=
  (extension l E b o (U ⊓ V)).obj ((restriction l E b o (U ⊓ V)).obj M)

/-- The binary direct-sum term of the signed open-cover triangle.
Source: blueprint, Gluing, B_M (blueprint: lem-sp-tower-binary-counit-representability). -/
abbrev coverB {Z : Scheme.{u}} (U V : Z.Opens) (M : D l E Z) :=
  (extension l E b o U).obj ((restriction l E b o U).obj M) ⊞
    (extension l E b o V).obj ((restriction l E b o V).obj M)

/-- A canonical positive component of the signed cover arrow, including restriction
composition. Source: blueprint, Gluing, nested-open maps
(blueprint: lem-sp-tower-binary-counit-representability). -/
def coverComponent {Z : Scheme.{u}} {U V : Z.Opens} (i : U ≤ V) (M : D l E Z) :=
  (extension l E b o U).map ((restrictionComp l E b o i).hom.app M) ≫
    nested l E b o i ((restriction l E b o V).obj M)

/-- The (1,-1) arrow, with its canonical nested-open components.
Source: blueprint, Gluing, s_M (blueprint: lem-sp-tower-binary-counit-representability). -/
def coverS {Z : Scheme.{u}} (U V : Z.Opens) (M : D l E Z) :
    coverA l E b o U V M ⟶ coverB l E b o U V M :=
  biprod.lift (coverComponent l E b o (inf_le_left : U ⊓ V ≤ U) M)
    (-coverComponent l E b o (inf_le_right : U ⊓ V ≤ V) M)

/-- The (1,1) arrow consists of the two actual open adjunction counits.
Source: blueprint, Gluing, t_M (blueprint: lem-sp-tower-binary-counit-representability). -/
def coverT {Z : Scheme.{u}} (U V : Z.Opens) (M : D l E Z) :
    coverB l E b o U V M ⟶ M :=
  biprod.desc ((o.openOp U.ι).derivedAdjunction.counit.app M)
    ((o.openOp V.ι).derivedAdjunction.counit.app M)

/-- The five-term contravariant Hom row is exact at its three interior terms.
The first arrow is the signed shifted cover arrow supplied by triangle rotation.
Source: blueprint, Gluing, five-term Hom segment
(blueprint: lem-sp-tower-binary-counit-representability). -/
def HomFiveExact {C₀ : Type v₀} [Category.{w₀} C₀] [Preadditive C₀]
    [HasShift C₀ ℤ] {A B M : C₀} (s : A ⟶ B) (t : B ⟶ M)
    (d : M ⟶ (shiftFunctor C₀ (1 : ℤ)).obj A) (G : C₀) : Prop :=
  Function.Exact
    (fun f : (shiftFunctor C₀ (1 : ℤ)).obj B ⟶ G ↦
      -(shiftFunctor C₀ (1 : ℤ)).map s ≫ f)
    (fun f : (shiftFunctor C₀ (1 : ℤ)).obj A ⟶ G ↦ d ≫ f) ∧
  Function.Exact (fun f : (shiftFunctor C₀ (1 : ℤ)).obj A ⟶ G ↦ d ≫ f)
    (fun f : M ⟶ G ↦ t ≫ f) ∧
  Function.Exact (fun f : M ⟶ G ↦ t ≫ f) (fun f : B ⟶ G ↦ s ≫ f)

/-- The image Hom row, written before conjugating by the exact functor's shift iso.
This keeps the connecting arrow and its sign explicit without choosing a shift iso.
Source: blueprint, Gluing, lower five-term Hom segment
(blueprint: lem-sp-tower-binary-counit-representability). -/
def ImageHomFiveExact {C₀ : Type v₀} {C₁ : Type v₁} [Category.{w₀} C₀] [Preadditive C₀]
    [HasShift C₀ ℤ] [Category.{w₁} C₁] [Preadditive C₁] (F₀ : C₀ ⥤ C₁)
    {A B M : C₀} (s : A ⟶ B) (t : B ⟶ M)
    (d : M ⟶ (shiftFunctor C₀ (1 : ℤ)).obj A) (K : C₁) : Prop :=
  Function.Exact
    (fun f : F₀.obj ((shiftFunctor C₀ (1 : ℤ)).obj B) ⟶ K ↦
      F₀.map (-(shiftFunctor C₀ (1 : ℤ)).map s) ≫ f)
    (fun f : F₀.obj ((shiftFunctor C₀ (1 : ℤ)).obj A) ⟶ K ↦ F₀.map d ≫ f) ∧
  Function.Exact
    (fun f : F₀.obj ((shiftFunctor C₀ (1 : ℤ)).obj A) ⟶ K ↦ F₀.map d ≫ f)
    (fun f : F₀.obj M ⟶ K ↦ F₀.map t ≫ f) ∧
  Function.Exact (fun f : F₀.obj M ⟶ K ↦ F₀.map t ≫ f)
    (fun f : F₀.obj B ⟶ K ↦ F₀.map s ≫ f)

/-- The four outer vertical maps in the five-term Hom comparison.
Source: blueprint, Gluing, outer local representing bijections
(blueprint: lem-sp-tower-binary-counit-representability). -/
def OuterBijective {C₀ : Type v₀} {C₁ : Type v₁} [Category.{w₀} C₀] [HasShift C₀ ℤ]
    [Category.{w₁} C₁]
    (F₀ : C₀ ⥤ C₁) {A B G : C₀} {K : C₁} (e : F₀.obj G ⟶ K) : Prop :=
  (Function.Bijective (fun f : B ⟶ G ↦ F₀.map f ≫ e)) ∧
  (Function.Bijective (fun f : A ⟶ G ↦ F₀.map f ≫ e)) ∧
  (Function.Bijective (fun f : (shiftFunctor C₀ (1 : ℤ)).obj A ⟶ G ↦ F₀.map f ≫ e)) ∧
  (Function.Bijective (fun f : (shiftFunctor C₀ (1 : ℤ)).obj B ⟶ G ↦ F₀.map f ≫ e))

/-- The two prescribed local equations for a lift of the counits.
Source: blueprint, Gluing, counit lift
(blueprint: lem-sp-tower-binary-counit-representability). -/
def LiftEquations {Z Y : Scheme.{u}} {h : Z ⟶ Y} (c₀ : Compactification h)
    (U V : Z.Opens) {P : D l E U.toScheme} {Q : D l E V.toScheme}
    {K : D l E Y} (eU : (support l E b o c₀ U).obj P ⟶ K)
    (eV : (support l E b o c₀ V).obj Q ⟶ K) {G : D l E Z}
    (aU : (restriction l E b o U).obj G ≅ P)
    (aV : (restriction l E b o V).obj G ≅ Q) (e : (F l E b o c₀).obj G ⟶ K) : Prop :=
  (F l E b o c₀).map ((o.openOp U.ι).derivedAdjunction.counit.app G) ≫ e =
      (support l E b o c₀ U).map aU.hom ≫ eU ∧
  (F l E b o c₀).map ((o.openOp V.ι).derivedAdjunction.counit.app G) ≫ e =
      (support l E b o c₀ V).map aV.hom ≫ eV

/-- The compatible pair of local counits, as one map from F_h(B_G).
It uses the additive image of the two biproduct projections.
Source: blueprint, Gluing, beta (blueprint: lem-sp-tower-binary-counit-representability). -/
def beta {Z Y : Scheme.{u}} {h : Z ⟶ Y} (c₀ : Compactification h)
    (U V : Z.Opens) {P : D l E U.toScheme} {Q : D l E V.toScheme}
    {K : D l E Y} (eU : (support l E b o c₀ U).obj P ⟶ K)
    (eV : (support l E b o c₀ V).obj Q ⟶ K) {G : D l E Z}
    (aU : (restriction l E b o U).obj G ≅ P)
    (aV : (restriction l E b o V).obj G ≅ Q) :
    (F l E b o c₀).obj (coverB l E b o U V G) ⟶ K :=
  (F l E b o c₀).map biprod.fst ≫ (support l E b o c₀ U).map aU.hom ≫ eU +
    (F l E b o c₀).map biprod.snd ≫ (support l E b o c₀ V).map aV.hom ≫ eV

/-- Equality of the global representing map on an open extension with its local
representing map under the actual open adjunction. It includes all shifts of N.
Source: blueprint, Gluing, identification of the outer columns
(blueprint: lem-sp-tower-binary-counit-representability). -/
def OpenThetaEquation {Z Y : Scheme.{u}} {h : Z ⟶ Y} (c₀ : Compactification h)
    (D₀ : Z.Opens) {P : D l E D₀.toScheme} {K : D l E Y}
    (eD : (support l E b o c₀ D₀).obj P ⟶ K) {G : D l E Z}
    (aD : (restriction l E b o D₀).obj G ≅ P) (e : (F l E b o c₀).obj G ⟶ K) : Prop :=
  ∀ (N : D l E D₀.toScheme), good l E b q D₀.toScheme N →
    ∀ f : (extension l E b o D₀).obj N ⟶ G,
      (F l E b o c₀).map f ≫ e =
        (support l E b o c₀ D₀).map
          (((o.openOp D₀.ι).derivedAdjunction.homEquiv N G) f ≫ aD.hom) ≫ eD

end AlgebraicGeometry.ProEtale.SpTowerBinaryCounit
