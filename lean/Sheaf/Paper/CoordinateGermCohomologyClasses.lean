/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.CoordinateGermConcentrationData
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Etale transfer of concentrated supported coordinate germs

Source: Stacks 09XP, conditional coordinate-model Steps 5--7
(blueprint: def-pur-coordinate-germ-cohomology-classes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The supported cohomology class of a normalized supported derived arrow.
The formula is the actual derived adjoint followed by evaluation at 1 on H^0,
with the canonical shift comparison. Source: Stacks 09XP
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferClassValue (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (q r : ℤ)
    (α : P.FunctorialCupH false i q r) :
    (DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1}
      (ModuleCat.{u + 1} P.Coefficient)
      q).obj ((Etale.coordinateGlobalSupport P.Coefficient i).rightDerivedFunctorPlus.obj
        (P.transferSingle X r)) :=
  ((DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1}
    (ModuleCat.{u + 1} P.Coefficient) 0).shiftIso
      q 0 q (add_zero _)).hom.app
      ((Etale.coordinateGlobalSupport P.Coefficient i).rightDerivedFunctorPlus.obj
        (P.transferSingle X r))
    ((DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1}
      (ModuleCat.{u + 1} P.Coefficient) 0).map
      (((Adjunction.derivedPlus.{u + 1, u + 1, u + 2, u + 2, u + 1, u + 1}
        (transferSupportAdjunction P.Coefficient
          i)).homEquiv _ _)
        (((Etale.supportedCoefficients P.Coefficient
            i).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              (ModuleCat.of P.Coefficient P.Coefficient) ≫
          DerivedCategory.Plus.ι.preimage
            ((DerivedCategory.Plus.singleFunctorιIso _ 0).hom.app
                ((Etale.supportedCoefficients P.Coefficient
                  i).obj
                    (ModuleCat.of P.Coefficient P.Coefficient)) ≫
              α ≫
              (DerivedCategory.Plus.ι.commShiftIso q).inv.app
                (P.transferSingle X r))) ≫
        ((Etale.coordinateGlobalSupport P.Coefficient
          i).rightDerivedFunctorPlus.commShiftIso
            q).hom.app (P.transferSingle X r))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso.{u + 1}
        (ModuleCat.{u + 1} P.Coefficient) 0).inv.app
          (ModuleCat.of P.Coefficient P.Coefficient) (1 : P.Coefficient)))

/-- Ordinary supported global cohomology, at the existing small localization.
Source: Stacks 09XP (blueprint: def-pur-coordinate-germ-cohomology-classes). -/
abbrev transferGlobal (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (r : ℤ) :=
  (Etale.coordinateGlobalSupport P.Coefficient i).rightDerivedFunctorPlus.obj
    (P.transferSingle X r)

/-- The degree-q coefficient cohomology functor.
Source: bounded-below derived categories
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
abbrev transferH (P : PurityFiniteSetting.{u}) (q : ℤ) :=
  DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1}
    (ModuleCat.{u + 1} P.Coefficient) q

/-- The global-to-stalk germ on one scheme, with the identity coefficient pullback.
Source: Stacks 09XP, literal kernel germ
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferLocalGerm (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (aX : X ⟶ Spec (.of P.field.k))
    (r : ℤ) : P.transferGlobal i r ⟶ P.transferStalk i t r :=
  (Etale.coordinateDerivedGlobalToStalk P.Coefficient i i (𝟙 X) rfl t).app
    (P.transferSingle X r) ≫
    (Etale.coordinateSupportedStalk P.Coefficient i t).rightDerivedFunctorPlus.map
      (P.transferTwistPullback (𝟙 X) aX r).hom

/-- Projection on the normal coordinates over an arbitrary base.
Source: Mathlib affine-space base change
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
abbrev transferProjection (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) := AffineSpace.map (ULift.{u} (Fin b)) aB

/-- The base zero section, represented by the Cartesian inverse image of the origin.
This is canonically B, including for b=0 and for non-Noetherian affine B.
Source: affine space and Stacks 09XP
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
abbrev transferBaseZero (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) :=
  pullback.snd (transferZero (Spec (.of P.field.k)) b) (P.transferProjection b aB)

/-- The canonical chosen square, without any extra Cartesian hypothesis.
Source: the fibre-product universal property
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferBaseSquare (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) :
    ChosenCartesianSquare
      (pullback.fst (transferZero (Spec (.of P.field.k)) b) (P.transferProjection b aB))
      (P.transferBaseZero b aB) (transferZero (Spec (.of P.field.k)) b)
      (P.transferProjection b aB) where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The actual supported pullback of c_N tensor v on the affine base space.
Source: Stacks 09XP and the normalized supported-cup pullback
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferBaseClass (P : PurityFiniteSetting.{u}) (b : ℕ) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℤ) (v : P.transferLine (r - b)) :
    P.FunctorialCupH false (P.transferBaseZero b aB) (2 * (b : ℤ)) r :=
  P.functorialCupPullback false (transferZero (Spec (.of P.field.k)) b)
    (P.transferBaseZero b aB) (P.transferProjection b aB)
    (pullback.fst (transferZero (Spec (.of P.field.k)) b) (P.transferProjection b aB))
    (P.transferBaseSquare b aB) (P.transferNormal b ↘ Spec (.of P.field.k))
    (2 * (b : ℤ)) r (P.transferTwistedCoordinateClass b r v)

/-- Restriction of supported stalks, using the literal-kernel normalization and the
specified signed coefficient comparison. Source: Stacks 09XP
(blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferRestriction (P : PurityFiniteSetting.{u}) {C X D Y : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (j : D ⟶ Y) [IsClosedImmersion j]
    (e : Y ⟶ X) [Etale e] (he : Set.range j.base = e.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    P.transferStalk i (t ≫ e) r ⟶ P.transferStalk j t r :=
  (Etale.coordinateDerivedStalkRestriction P.Coefficient i j e he t).app
    (P.transferSingle X r) ≫
    (Etale.coordinateSupportedStalk P.Coefficient j t).rightDerivedFunctorPlus.map
      (P.transferTwistPullback e aX r).hom

/-- Literal-kernel etale restriction as a unique natural transformation.
Source: Stacks 09XP and 03S2
(blueprint: def-pur-coordinate-germ-cohomology-classes).
Proof: on W etale over Y both kernels are the kernel of F(W) to F(W minus D).
The identity of this submodule commutes with restrictions and maps of sheaves.
The kernel inclusion is monic, so the inclusion equation determines the map. -/
theorem transferSupportRestriction_existsUnique (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ Y) [IsClosedImmersion j] (e : Y ⟶ X) [Etale e]
    (he : Set.range j.base = e.base ⁻¹' Set.range i.base) :
    ∃! α : Etale.coordinateSupportSheaf P.Coefficient i ⋙
        Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e ⟶
      Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e ⋙
        Etale.coordinateSupportSheaf P.Coefficient j,
      ∀ F, α.app F ≫ (Etale.coordinateSupportInclusion P.Coefficient j).app
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).obj F) =
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).map
          ((Etale.coordinateSupportInclusion P.Coefficient i).app F) := by
  sorry

/-- The support exchange determined by its kernel-inclusion equation.
Source: Stacks 09XP (blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferSupportRestriction (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ Y) [IsClosedImmersion j] (e : Y ⟶ X) [Etale e]
    (he : Set.range j.base = e.base ⁻¹' Set.range i.base) :=
  (P.transferSupportRestriction_existsUnique i j e he).choose

/-- Derive the literal-kernel exchange, using exact etale inverse image.
Source: Stacks 09XP (blueprint: def-pur-coordinate-germ-cohomology-classes). -/
def transferDerivedSupportRestriction (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ Y) [IsClosedImmersion j] (e : Y ⟶ X) [Etale e]
    (he : Set.range j.base = e.base ⁻¹' Set.range i.base) :=
  Functor.rightDerivedFunctorPlusBaseChange (P.transferSupportRestriction i j e he)

end WeilConjectures.PurityFiniteSetting
