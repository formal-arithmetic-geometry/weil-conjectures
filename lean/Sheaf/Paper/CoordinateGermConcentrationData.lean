/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCoordinateSupport
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SupportedCupFunctoriality
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # Concentrated supported coordinate germs and etale transfer

Source: Stacks Project, Etale Cohomology, Tag 09XP; Homology, Tag 0118;
blueprint main-20261015, frame-independence, coordinate-model Steps 5--7
(blueprint: def-pur-coordinate-germ-concentration-data).

All support maps below are the existing kernel-normalized maps. The coordinate
class is fixed by its ordered Cartier--Kummer product, and the hypothesis on
orientation maps is an equation on every coefficient, without choosing a basis.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Cache the published small localization at the coefficient universe.
Source: Grothendieck abelian module categories
(blueprint: def-pur-coordinate-germ-concentration-data). -/
instance transferModuleHasDerived (P : PurityFiniteSetting.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} P.Coefficient) :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _

/-- Reuse the supported-cup localization on ordinary etale sheaves.
Source: the ordinary supported-cup derived category
(blueprint: def-pur-coordinate-germ-concentration-data). -/
instance transferSheafHasDerived (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  P.functorialCupHasDerived false X

/-- The normal affine space. Source: coordinate-model Step 5, Stacks 01M0
(blueprint: def-pur-coordinate-germ-concentration-data). -/
abbrev transferNormal (P : PurityFiniteSetting.{u}) (b : ℕ) :=
  AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k))

/-- The ordered coordinates, using precisely the Mathlib affine-space coordinates.
Source: coordinate-model Step 5 (blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferCoordinates (B : Scheme.{u}) (b : ℕ) :
    Fin b → Γ(AffineSpace (ULift.{u} (Fin b)) B, ⊤) :=
  fun i ↦ AffineSpace.coord B (ULift.up i)

/-- The zero section as the closed subscheme cut out by the coordinate ideal.
Source: coordinate-model Step 5 (blueprint: def-pur-coordinate-germ-concentration-data). -/
abbrev transferZero (B : Scheme.{u}) (b : ℕ) :=
  (AffineSpace (ULift.{u} (Fin b)) B).zeroLocusSubschemeι
    (Set.range (transferCoordinates B b))

/-- The coefficient line is the sections of the actual signed finite Tate sheaf over k.
Source: the input line L_(r-b), Stacks 03PK
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferLine (P : PurityFiniteSetting.{u}) (r : ℤ) : ModuleCat.{u + 1} P.Coefficient :=
  (P.functorialCupTwist false (Spec (.of P.field.k)) r).obj.obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of P.field.k)))))

/-- Degree-zero coefficient sheaves in the bounded-below category.
Source: finite twists and bounded-below derived functors
(blueprint: def-pur-coordinate-germ-concentration-data). -/
abbrev transferSingle (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.functorialCupTwist false X r)

/-- The field complex, with its ordinary small-etale module coefficients.
Source: Stacks 09XP, K_r in the statement
(blueprint: def-pur-coordinate-germ-concentration-data). -/
abbrev transferField (P : PurityFiniteSetting.{u}) (b : ℕ) (r : ℤ) :=
  (Functor.rightDerivedFunctorPlus.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 1}
    (Etale.coordinateGlobalSupport P.Coefficient
      (transferZero (Spec (.of P.field.k)) b))).obj
      (P.transferSingle (P.transferNormal b) r)

/-- The actual stalk of derived support, expressed by the existing derived-stalk functor.
Source: Stacks 09XP, supported-stalk derivation identification
(blueprint: def-pur-coordinate-germ-concentration-data). -/
abbrev transferStalk (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (r : ℤ) :=
  (Functor.rightDerivedFunctorPlus.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 1}
    (Etale.coordinateSupportedStalk P.Coefficient i t)).obj
    (P.transferSingle X r)

/-- Exact inverse image of the coefficient sheaf, with the canonical signed-twist map.
Source: Stacks 03PK, finite-twist pullback, including evaluation on negative powers
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferTwistPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategoryPlus.obj
      (P.transferSingle X r) ≅ P.transferSingle Y r :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f) 0).app (P.functorialCupTwist false X r) ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (P.functorialCupEtaleTwistPullback f aX r)

/-- The normalized supported germ after the canonical coefficient pullback.
Source: Stacks 09XP, coordinate-model Step 5
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferGerm (P : PurityFiniteSetting.{u}) (b : ℕ) {Z Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ P.transferNormal b)
    (hf : Set.range i.base = f.base ⁻¹'
      Set.range (transferZero (Spec (.of P.field.k)) b).base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y) (r : ℤ) :
    P.transferField b r ⟶ P.transferStalk i t r :=
  (Etale.coordinateDerivedGlobalToStalk P.Coefficient
    (transferZero (Spec (.of P.field.k)) b) i f hf t).app
      (P.transferSingle (P.transferNormal b) r) ≫
    (Functor.rightDerivedFunctorPlus.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 1}
      (Etale.coordinateSupportedStalk P.Coefficient i t)).map
        (P.transferTwistPullback f (P.transferNormal b ↘ Spec (.of P.field.k)) r).hom

/-- The ordered ordinary etale coordinate product is the unique ordinary witness of
the published ordered Kummer boundary product. Source: Cartier--Kummer ordinary
witness, supported cup, and Stacks 09XP
(blueprint: def-pur-coordinate-germ-concentration-data).
Proof: each principal boundary has the ordinary etale Cartier--Kummer witness.
Exact site comparison preserves localization boundaries and the specified supported
cup. Induction in the ordered coordinates gives the displayed equality, starting
with the coefficient unit for b=0. Full faithfulness of finite etale-origin derived
comparison gives uniqueness. No purity or concentration is used here. -/
theorem transferCoordinateClass_existsUnique (P : PurityFiniteSetting.{u}) (b : ℕ) :
    ∃! c : P.FunctorialCupH false (transferZero (Spec (.of P.field.k)) b)
        (2 * (b : ℤ)) b,
      P.functorialCupCompare _ (2 * (b : ℤ)) b c =
        P.frameBoundaryProduct (P.transferNormal b)
          (P.transferNormal b ↘ Spec (.of P.field.k)) b
          (transferCoordinates (Spec (.of P.field.k)) b) := by
  sorry

/-- The coordinate product, selected only from its unique ordered normalization.
Source: Cartier--Kummer ordinary witness and supported cup
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferCoordinateClass (P : PurityFiniteSetting.{u}) (b : ℕ) :=
  (P.transferCoordinateClass_existsUnique b).choose

/-- A coefficient v determines its actual global section on the normal space, by
constant-sheaf adjunction and the signed-twist pullback. Source: Stacks 03PK
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferCoefficientSection (P : PurityFiniteSetting.{u}) (b : ℕ) (s : ℤ)
    (v : P.transferLine s) :
    P.constantEtale (P.transferNormal b) ⟶ P.functorialCupTwist false (P.transferNormal b) s :=
  (P.functorialCupConstantPullback false
      (P.transferNormal b ↘ Spec (.of P.field.k))).inv ≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (P.transferNormal b ↘ Spec (.of P.field.k))).map
        (((constantSheafAdj (Spec (.of P.field.k)).smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)
          (Scheme.Etale.isTerminalMkId (Spec (.of P.field.k)))).homEquiv _ _).symm
            (ModuleCat.ofHom
              ((LinearMap.id : P.Coefficient →ₗ[P.Coefficient] P.Coefficient).smulRight v))) ≫
    (P.functorialCupEtaleTwistPullback (P.transferNormal b ↘ Spec (.of P.field.k))
      (𝟙 (Spec (.of P.field.k))) s).hom

/-- Tensor the ordered coordinate class with every element of the coefficient line.
The cup uses the prescribed signed tensor product, including negative powers.
Source: the input orientation formula c_N tensor v, Stacks 09XP and 03PK
(blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferTwistedCoordinateClass (P : PurityFiniteSetting.{u}) (b : ℕ) (r : ℤ)
    (v : P.transferLine (r - b)) :
    P.FunctorialCupH false (transferZero (Spec (.of P.field.k)) b) (2 * (b : ℤ)) r :=
  P.functorialCupReindex false _ (add_zero _) (add_sub_cancel _ _)
    (P.functorialCupChangeSupport false (transferZero (Spec (.of P.field.k)) b)
      (AlgebraicGeometry.ProEtale.cupIntersection
        (transferZero (Spec (.of P.field.k)) b) (𝟙 (P.transferNormal b)))
      (pullback.fst _ _) rfl _ _
      (P.functorialCup false (P.transferNormal b ↘ Spec (.of P.field.k))
        (transferZero (Spec (.of P.field.k)) b) (𝟙 (P.transferNormal b))
        (2 * (b : ℤ)) 0 b (r - b) (P.transferCoordinateClass b)
        ((P.functorialCupSingle false (P.transferNormal b)).map
            (P.functorialCupFullSupportIso false (P.transferNormal b)).hom ≫
          (P.functorialCupSingle false (P.transferNormal b)).map
            (P.transferCoefficientSection b (r - b) v) ≫
          (shiftFunctorZero _ ℤ).inv.app _)))

/-- Ordinary supported-coefficient adjunction for the literal restriction kernel.
The epic quotient normalization determines it uniquely. Source: Stacks 09XP
(blueprint: def-pur-coordinate-germ-concentration-data).
Proof: apply the constant-sheaf adjunction to the support kernel. A constant-sheaf
map vanishes on the complementary open precisely when it factors through the closed
constant quotient. This gives the displayed Hom equivalence, natural in M and F.
The quotient is epic, so its normalization determines that equivalence uniquely. -/
theorem transferSupportAdjunction_existsUnique (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! a : Etale.supportedCoefficients A i ⊣ Etale.coordinateGlobalSupport A i,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (Etale.coordinateGlobalSupport A i).obj F),
      Etale.supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
          (Scheme.Etale.isTerminalMkId X)).homEquiv M F).symm
          (f ≫ kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op)) := by
  sorry

/-- Select the adjunction with its unique quotient normalization.
Source: Stacks 09XP (blueprint: def-pur-coordinate-germ-concentration-data). -/
def transferSupportAdjunction (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  (transferSupportAdjunction_existsUnique A i).choose

end WeilConjectures.PurityFiniteSetting
