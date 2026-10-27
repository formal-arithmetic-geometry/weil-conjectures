/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.Paper.PurityRelativeKummer
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact

/-! # Concentration of the Kummer restriction triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
lem-pur-gysin-structure.proof.md, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration).

Restriction is the actual open-unit map followed by the inverse direct-image compositor.
The triangle is unrotated, fixing the sign of its connecting map. The degree-zero
normalization is the existing canonical good-truncation normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MonoidalCategory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Tensor an orientation inverse and a coefficient-unit comparison, then use the left
unitor. Source: blueprint tensor-unit computation, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def orientationTensorUnitIso {D : Type v} [Category.{w} D] [MonoidalCategory D]
    {A C : D} (θ : A ≅ C) (η : A ≅ 𝟙_ D) (M : D) : C ⊗ M ≅ M :=
  whiskerRightIso (θ.symm ≪≫ η) M ≪≫ λ_ M

/-- The tensor-unit conclusion, with its map fixed by the orientation and unit comparison.
The test family is explicit, so it can consist exactly of degree-zero module sheaves.
Source: blueprint tensor-unit computation, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def OrientationTensorUnitConclusions {D : Type v} [Category.{w} D] [MonoidalCategory D]
    {A C : D} {I : Type u} (S : I → D) (θ : A ≅ C) (η : A ≅ 𝟙_ D) : Prop :=
  ∀ M : I, ∃ e : C ⊗ S M ≅ S M, e = orientationTensorUnitIso θ η (S M)

/-- The ordinary finite-coefficient sheaf category used by the affine-line datum.
Source: blueprint affine-line conventions
(blueprint: lem-pur-kummer-triangle-concentration). -/
abbrev KummerSheaves (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)

/-- The two actual derived direct images, indexed by whether the line is punctured.
Source: blueprint restriction triangle, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerImage (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) (punctured : Bool) :
    DerivedCategory (P.KummerSheaves Y) :=
  if punctured then
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true)
  else
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (lineProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Line Y) true)

/-- Derived open restriction r, using the canonical composition identification.
Source: blueprint restriction triangle, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerRestriction (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    P.kummerImage h Y false ⟶ P.kummerImage h Y true :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (lineProjection Y)).rightDerivedFunctor.map
        (P.relativeUnit h (openImmersion Y) true) ≫
    (ProEtale.finiteDirectImageComposition P.Coefficient
      (openImmersion Y) (lineProjection Y)).inv.app (P.derivedSheaf h (Punctured Y) true)

/-- The canonical identification of the constant sheaf with the sheaf tensor unit.
Source: blueprint constant coefficient unit and the comparison inverse image
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerConstantUnit (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    P.constant Y ≅ 𝟙_ (P.KummerSheaves Y) :=
  ProEtale.comparisonUpperStarUnitIso P.Coefficient Y

/-- The constant coefficient object in degree zero is the derived tensor unit.
Source: blueprint tensor-unit computation, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerDerivedUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    P.derivedSheaf h Y false ≅ 𝟙_ (DerivedCategory (P.KummerSheaves Y)) :=
  (DerivedCategory.singleFunctor (P.KummerSheaves Y) 0).mapIso (P.kummerConstantUnit Y) ≪≫
    DerivedCategory.singleFunctorObjUnitIso (P.KummerSheaves Y)

/-- The canonical associated-module realization, with coefficient finiteness supplied
by the actual quotient construction. Source: blueprint finite coefficient conventions
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerIntrinsicRealization (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    DerivedCategory (P.KummerSheaves Y) ⥤ Scheme.proEtaleDerivedCategory Y P.Ring :=
  have : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory

/-- The actual boundary-generator map, expressed in H0(B[2]) by the standard shift.
Source: blueprint restriction triangle, first paragraph
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerBoundaryZero (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (B : DerivedCategory (P.KummerSheaves Y))
    (b : B ⟶ P.kummerImage h Y false) (δ : P.kummerImage h Y true ⟶ B⟦(1 : ℤ)⟧) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).obj
      (B⟦(2 : ℤ)⟧) :=
  P.kummerGenerator h Y a ≫ DerivedCategory.HomologySequence.δ
    (Triangle.mk b (P.kummerRestriction h Y) δ) 1 2 ≫
      ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).inv.app B

/-- Membership in the recorded finite-Tor constructible subcategory, in the native
fixed-coefficient presentation. Source: blueprint finite-Tor conclusion
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerConstructibleFiniteTor (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    ObjectProperty (DerivedCategory (P.KummerSheaves Y)) :=
  ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y

/-- The recorded Tor interval [0,0], for arbitrary degree-zero test sheaves.
Source: blueprint tensor-unit conclusion
(blueprint: lem-pur-kummer-triangle-concentration). -/
def kummerTorZero (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    ObjectProperty (DerivedCategory (P.KummerSheaves Y)) :=
  ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) Y 0 0

/-- Concentration, the actual Kummer boundary normalization, constructibility and
Tor interval [0,0], for every unrotated distinguished restriction triangle.
Source: blueprint main-20261015, sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md,
first paragraph (blueprint: lem-pur-kummer-triangle-concentration).

Proof:
1. The Grothendieck abelian module categories and additive left exact direct images
allow derived-functor-negative-vanishing at b=0, so both images vanish in negative degrees.
2. RelativeKummer gives the affine-line unit isomorphism, punctured-line vanishing in
degrees at least two, and the actual generator gamma=kummerGenerator. Compatibility of
the units with open restriction gives H0(r) invertible. The affine image is degree zero.
3. The unrotated long exact sequence gives H0(B)=H1(B)=0 and makes its actual connecting
map delta:H1(Q) -> H2(B) an isomorphism.
4. For m<0 or m>=3 the outer groups H^(m-1)(Q), H^m(P) vanish, so H^m(B)=0.
The cochain shift identifies H0(B[2]) with H2(B).
5. GoodTruncationNormalization, computed by the truncation inclusion and cycles quotient,
induces the identity on H0. Compose its inverse with the single complex of delta gamma
and the inverse shift comparison to obtain theta with precisely the asserted H0 map.
6. This identifies the only nonzero cohomology sheaf with the globally constant free
rank-one A sheaf. One stratum proves constructibility; use no strata on the empty base.
7. Tensoring the degree-zero coefficient unit with a complex is that same complex,
with the same differential, so the unit complex is K-flat.
8. Tensor theta inverse, then the canonical coefficient-unit comparison and left unitor.
For every module sheaf, including nonflat ones, this identifies the derived tensor with
that sheaf in degree zero. Thus its Tor interval is [0,0], proving membership in D^b_ctf. -/
theorem kummer_triangle_concentration (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (B : DerivedCategory (P.KummerSheaves Y))
    (b : B ⟶ P.kummerImage h Y false) (δ : P.kummerImage h Y true ⟶ B⟦(1 : ℤ)⟧)
    (hT : Triangle.mk b (P.kummerRestriction h Y) δ ∈ distTriang _) :
    IsIso (P.relativeUnit h (lineProjection Y) true) ∧
    IsIso ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).map
      (P.kummerRestriction h Y)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) m).obj
        (P.kummerImage h Y false))) ∧
    (∀ m : ℤ, m ≠ 0 → m ≠ 1 → IsZero
      ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) m).obj
        (P.kummerImage h Y true))) ∧
    IsIso (P.kummerGenerator h Y a) ∧
    IsIso (DerivedCategory.HomologySequence.δ
      (Triangle.mk b (P.kummerRestriction h Y) δ) 1 2) ∧
    (∀ m : ℤ, m ≠ 2 →
      IsZero ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) m).obj B)) ∧
    ∃ (hC : ∀ m : ℤ, m ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) m).obj (B⟦(2 : ℤ)⟧)))
      (θ : P.derivedSheaf h Y false ≅ B⟦(2 : ℤ)⟧),
      (DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).map
          (DerivedCategory.goodTruncationNormalization (B⟦(2 : ℤ)⟧) hC).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (P.KummerSheaves Y) 0).hom.app
          ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).obj (B⟦(2 : ℤ)⟧)) = 𝟙 _ ∧
      θ.hom = (DerivedCategory.singleFunctor (P.KummerSheaves Y) 0).map
        (P.kummerBoundaryZero h Y a B b δ) ≫
        (DerivedCategory.goodTruncationNormalization (B⟦(2 : ℤ)⟧) hC).inv ∧
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (P.KummerSheaves Y) 0).inv.app
          (P.constant Y) ≫
        (DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).map θ.hom ≫
        ((DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).hom.app B =
        P.kummerGenerator h Y a ≫ DerivedCategory.HomologySequence.δ
          (Triangle.mk b (P.kummerRestriction h Y) δ) 1 2 ∧
      Nonempty (P.constant Y ≅
        (DerivedCategory.homologyFunctor (P.KummerSheaves Y) 0).obj (B⟦(2 : ℤ)⟧)) ∧
      Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos Y
        ((P.kummerIntrinsicRealization Y).obj (B⟦(2 : ℤ)⟧)) ∧
      P.kummerConstructibleFiniteTor Y (B⟦(2 : ℤ)⟧) ∧
      P.kummerTorZero Y (B⟦(2 : ℤ)⟧) ∧
      OrientationTensorUnitConclusions
        (D := DerivedCategory (P.KummerSheaves Y))
        (DerivedCategory.singleFunctor (P.KummerSheaves Y) 0).obj
        θ (P.kummerDerivedUnit h Y) := by
  sorry

end WeilConjectures.PurityFiniteSetting
