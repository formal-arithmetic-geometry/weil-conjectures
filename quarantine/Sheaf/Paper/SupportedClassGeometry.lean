/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.FiniteTorAmplitudeSites

/-! # SupportedClassGeometry

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-class-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- The finite-Tor constructible input predicate, using the dependency's ordinary-etale
presentation and the very same positive coefficient index.
Source: blueprint Step 1, hypotheses
(blueprint: def-pur-supported-class-geometry). -/
abbrev CompactProductInput (P : PurityFiniteSetting.{u}) (X : AlgebraicGeometry.Scheme.{u}) :=
  finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos X

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- The projection square used by the recorded supported pullback.
Source: blueprint Step 1, pulled-back supports
(blueprint: def-pur-supported-class-geometry). -/
def compactProductPullbackSquare {C X Y : Scheme.{u}} (i : C ⟶ X) (v : Y ⟶ X) :
    ChosenCartesianSquare (pullback.fst i v) (pullback.snd i v) i v where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := by simp
  hom_snd := by simp

/-- The canonical map from the product support to the intersection of the pulled-back
supports. Its projections are the literal pullback lifts.
Source: blueprint Step 1, identification of supports
(blueprint: def-pur-supported-class-geometry). -/
def compactProductIntersectionMap {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    pullback (i ≫ f) (j ≫ g) ⟶
      pullback (pullback.snd i (pullback.fst f g)) (pullback.snd j (pullback.snd f g)) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _) (supportedProductImmersion f g i j)
      (by simp only [supportedProductImmersion, pullback.map, pullback.lift_fst]))
    (pullback.lift (pullback.snd _ _) (supportedProductImmersion f g i j)
      (by simp only [supportedProductImmersion, pullback.map, pullback.lift_snd]))
    (by simp only [pullback.lift_snd])

/-- The two projections from the intersection have equal composites to the base.
Source: blueprint Step 1, identification of supports
(blueprint: def-pur-supported-class-geometry).
Proof: use the two defining pullback conditions over X and Y, then the condition
of their intersection, and finally pr_X followed by f equals pr_Y followed by g. -/
theorem compactProductIntersectionInverse_condition {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    (pullback.fst (pullback.snd i (pullback.fst f g))
      (pullback.snd j (pullback.snd f g)) ≫ pullback.fst i (pullback.fst f g)) ≫ (i ≫ f) =
    (pullback.snd (pullback.snd i (pullback.fst f g))
      (pullback.snd j (pullback.snd f g)) ≫ pullback.fst j (pullback.snd f g)) ≫ (j ≫ g) := by
  sorry

/-- The projection-normalized map from the intersection back to the product support.
Source: blueprint Step 1, identification of supports
(blueprint: def-pur-supported-class-geometry). -/
def compactProductIntersectionInverse {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    pullback (pullback.snd i (pullback.fst f g)) (pullback.snd j (pullback.snd f g)) ⟶
      pullback (i ≫ f) (j ≫ g) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst i (pullback.fst f g))
    (pullback.snd _ _ ≫ pullback.fst j (pullback.snd f g))
    (compactProductIntersectionInverse_condition f g i j)

/-- The inverse support identification commutes with the ambient immersion.
Source: blueprint Step 1, identification of supports
(blueprint: def-pur-supported-class-geometry).
Proof: both projections to X and Y are the defining pullback projections, so
pullback extensionality proves the equality. -/
theorem compactProductIntersectionInverse_comm {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    compactProductIntersectionInverse f g i j ≫ supportedProductImmersion f g i j =
      ProEtale.cupIntersection (pullback.snd i (pullback.fst f g))
        (pullback.snd j (pullback.snd f g)) := by
  sorry

/-- Pull back the two classes, take the recorded supported cup, and identify the
intersection support with the actual product support by its projection-normalized map.
Source: blueprint Step 1, last cup-product clause
(blueprint: def-pur-supported-class-geometry). -/
def compactProductPulledCup (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b r s : ℤ)
    (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s) :
    P.FunctorialCupH pro (supportedProductImmersion f g i j) (a + b) (r + s) :=
  P.functorialCupChangeSupport pro (supportedProductImmersion f g i j)
    (ProEtale.cupIntersection (pullback.snd i (pullback.fst f g))
      (pullback.snd j (pullback.snd f g)))
    (compactProductIntersectionInverse f g i j)
    (compactProductIntersectionInverse_comm f g i j) (a + b) (r + s)
    (P.functorialCup pro (pullback.toBase f g)
      (pullback.snd i (pullback.fst f g)) (pullback.snd j (pullback.snd f g)) a b r s
      (P.functorialCupPullback pro i (pullback.snd i (pullback.fst f g))
        (pullback.fst f g) (pullback.fst i (pullback.fst f g))
        (compactProductPullbackSquare i (pullback.fst f g)) f a r α)
      (P.functorialCupPullback pro j (pullback.snd j (pullback.snd f g))
        (pullback.snd f g) (pullback.fst j (pullback.snd f g))
        (compactProductPullbackSquare j (pullback.snd f g)) g b s β))

/-- The actual coefficient unit in degree zero.
Source: blueprint Step 1, supported-class representatives
(blueprint: def-pur-supported-class-geometry). -/
abbrev compactProductUnit (P : PurityFiniteSetting.{u}) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u + 1} P.Coefficient) 0).obj
    (ModuleCat.of P.Coefficient P.Coefficient)

/-- Multiplication of the two coefficient units, using the ordinary tensor map
and the canonical degree-zero localization comparison.
Source: blueprint Step 1, coefficient multiplication
(blueprint: def-pur-supported-class-geometry). -/
def compactProductUnitMultiplication (P : PurityFiniteSetting.{u}) :
    P.compactProductUnit ⊗ P.compactProductUnit ⟶ P.compactProductUnit :=
  ProEtale.cupSingleTensorMap (ModuleCat.of P.Coefficient P.Coefficient)
      (ModuleCat.of P.Coefficient P.Coefficient) ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} P.Coefficient) 0).map
      (λ_ (ModuleCat.of P.Coefficient P.Coefficient)).hom

/-- The closed supported coefficient unit is the recorded supported-Hom source.
Source: blueprint Step 1, supported-class representatives
(blueprint: def-pur-supported-class-geometry).
Proof: unfold supportedCoefficients, functorialCupSource at false and constantEtale.
Both sides are the direct image of the same constant coefficient unit. -/
theorem compactProductCoefficientUnit_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (supportedCoefficients P.Coefficient i).obj (ModuleCat.of P.Coefficient P.Coefficient) =
      P.functorialCupSource false i := by
  sorry

/-- Convert the recorded Hom representative into the same representative out of
C_i(A[0]), through the canonical exact-functor degree-zero comparison.
Source: blueprint Step 1, supported adjunction representatives
(blueprint: def-pur-supported-class-geometry). -/
def compactProductClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (a r : ℤ) (α : P.FunctorialCupH false i a r) :=
  ((supportedCoefficients P.Coefficient i).mapDerivedCategorySingleFunctor 0).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient) ≫
    (P.functorialCupSingle false X).map (eqToHom (P.compactProductCoefficientUnit_eq i)) ≫ α

/-- Pull back a supported morphism before specializing the finite coefficient datum.
Source: blueprint Step 1, exterior class representatives
(blueprint: def-pur-supported-class-geometry). -/
def compactProductClassPullbackGeneric (A : Type (u + 1)) [CommRing A]
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : Y ⟶ X)
    (M : DerivedCategory (ModuleCat.{u + 1} A))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (supportedCoefficients A i).mapDerivedCategory.obj M ⟶ K) :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
    (upperStar (ModuleCat.{u + 1} A) p)).hom.app M ≫
    (compactProductPullback (ModuleCat.{u + 1} A) p).map α ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).inv.app K

/-- Pull back an arbitrary supported morphism through the exact/left-derived
comparison; this specializes the same construction as the two support counits.
Source: blueprint Step 1, exterior class representatives
(blueprint: def-pur-supported-class-geometry). -/
def compactProductClassPullback (P : PurityFiniteSetting.{u})
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : Y ⟶ X)
    (M : DerivedCategory (ModuleCat.{u + 1} P.Coefficient))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (α : (supportedCoefficients P.Coefficient i).mapDerivedCategory.obj M ⟶ K) :=
  compactProductClassPullbackGeneric P.Coefficient i p M K α

/-- The canonical conversion from the tensor coefficient source to the supported
coefficient unit used by the recorded cup product.
Source: blueprint Step 1, comparison of supported classes
(blueprint: def-pur-supported-class-geometry). -/
def compactProductClassSource (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportedCoefficients P.Coefficient i).mapDerivedCategory.map
      P.compactProductUnitMultiplication ≫
    ((supportedCoefficients P.Coefficient i).mapDerivedCategorySingleFunctor 0).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient) ≫
    (P.functorialCupSingle false X).map (eqToHom (P.compactProductCoefficientUnit_eq i))

end WeilConjectures.PurityFiniteSetting
