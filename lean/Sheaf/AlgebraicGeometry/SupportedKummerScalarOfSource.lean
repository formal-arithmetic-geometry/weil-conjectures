/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Sheaf.AlgebraicGeometry.SupportedKummerRootScalarUnit
import Sheaf.AlgebraicGeometry.SupportedKummerIntegralEquation
import all Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.AlgebraicGeometry.ScalarUnitExt
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

/-! # Assembly of normalized supported Kummer coefficient squares -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC vC wC uB vB wB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local instance 10000] cachedAbSheafify cachedModSheafify
open Scheme
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

private theorem boundary_forget
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)} {n : ℕ}
    (κ : Ext P Q n) :
    (κ.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)).mapExactFunctor
        (RawModuleScalarComparison.forget R T) =
      κ.mapExactFunctor (RawModuleScalarComparison.forget S T) := by
  have h := Ext.mapExactFunctor_comp_mk₀_eq_sheaf
    (Sheaf.restrictScalars T.smallEtaleTopology φ) (RawModuleScalarComparison.forget R T)
    (RawModuleScalarComparison.forget S T) (Iso.refl _) κ
  simpa only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id,
    Ext.mk₀_id_comp] using h.symm


private theorem boundary_scalar_square
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q P' Q' : C} {I Y : B} (a : I ⟶ F.obj P)
    (r : Y ⟶ F.obj Q) (η : P ⟶ P') (θ : Q ⟶ Q')
    (b : Ext I Y 2) (k : Ext P Q 2) (k' : Ext P' Q' 2)
    (hinj : Function.Injective (fun c : Ext P Q' 2 ↦
      (Ext.mk₀ a).comp (c.mapExactFunctor F) (zero_add 2)))
    (hk : (Ext.mk₀ a).comp (k.mapExactFunctor F) (zero_add 2) =
      b.comp (Ext.mk₀ r) (add_zero 2))
    (hk' : (Ext.mk₀ (a ≫ F.map η)).comp (k'.mapExactFunctor F) (zero_add 2) =
      b.comp (Ext.mk₀ (r ≫ F.map θ)) (add_zero 2)) :
    (Ext.mk₀ η).comp k' (zero_add 2) = k.comp (Ext.mk₀ θ) (add_zero 2) := by
  apply hinj
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀_assoc, hk', ← Ext.comp_assoc_of_third_deg_zero, hk]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

-- Keep the concrete sheaf constructions out of the Ext associativity calculation.
attribute [local irreducible] ordinaryFiniteRootMap supportedIntegralGenerator
  cartierPoleBoundary

/-- A normalized supported constant scalar unit extends the normalized supported
Kummer boundary square to the target root line.
Source: blueprint lem-amb-cartier-kummer-map, final scalar-extension paragraph;
Stacks 03PL and 07A6 (blueprint: lem-asd-supported-kummer-scalar-of-source).

Proof: take the normalized root-line derived unit. The given constant coefficient
map preserves the integral supported generator, and the root-line map preserves the
root coefficient generator. Both normalized boundaries satisfy their integral pole
and Kummer equations. The integral supported derived unit detects equality on Ext.
Apply that injection, use exact-functor composition coherence, and reassociate the
Yoneda products; both sides become the same integral boundary followed by the target
root coefficient map. Combine this square with the two derived units. -/
theorem supported_kummer_scalar_of_source
    {R A : Type (u + 1)} [CommRing R] [Finite R] [CommRing A] [Finite A]
    (φ : R →+* A) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hR : (N : R) = 0) (hA : (N : A) = 0) (hT : IsUnit (N : Γ(T, ⊤)))
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (finiteEtaleTateLine T N A hA) 2)
    (κ₀ : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (finiteEtaleTateLine T N R hR) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ)
    (hκ₀ : SupportedKummerBoundary R N hR i hI hT κ₀)
    (η : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant A D))
    (hη : ∀ (W : D.Etaleᵒᵖ) (r : R),
      η.hom.app W ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app W r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W (φ r))
    (huI : SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η)) :
    SupportedKummerScalar φ N hR hA i κ₀ κ := by
  obtain ⟨θ, hθ, hθunit⟩ := supported_kummer_root_scalar_unit φ T N hN hR hA hT
  unfold SupportedKummerScalar
  refine ⟨η, θ, hη, hθ, ?_, hθunit, ?_⟩
  · exact huI
  · let U := RawModuleScalarComparison.forget R T
    let V := Sheaf.restrictScalars T.smallEtaleTopology φ
    have hu := scalar_unit_ext_bijective U
      (Q := V.obj (finiteEtaleTateLine T N A hA)) (supportedIntegralGenerator R i)
      (supported_integral_derived_unit T N hN R hR i) 2
    have hsource : supportedIntegralGenerator R i ≫
        U.map ((lowerStar (ModuleCat.{u + 1} R) i).map η) =
        supportedIntegralGenerator A i := by
      unfold supportedIntegralGenerator
      change (lowerStar AddCommGrpCat.{u + 1} i).map (ordinaryFiniteIntegralGenerator R D) ≫
        (lowerStar AddCommGrpCat.{u + 1} i).map
          ((RawModuleScalarComparison.forget R D).map η) = _
      rw [← Functor.map_comp, generator_scalar D φ η hη]
    have hroot : ordinaryFiniteRootMap R N hR T ≫ U.map θ =
        ordinaryFiniteRootMap A N hA T := by
      unfold ordinaryFiniteRootMap
      ext W z
      change θ.hom.app W (finiteEtaleTateOneGenerator R N T hR W 1 z) =
        finiteEtaleTateOneGenerator A N T hA W 1 z
      simpa only [map_one] using hθ W 1 z
    apply boundary_scalar_square U (supportedIntegralGenerator R i)
      (ordinaryFiniteRootMap R N hR T) ((lowerStar (ModuleCat.{u + 1} R) i).map η) θ
      ((cartierPoleBoundary i hI).comp (T.kummerSequence_shortExact N hT).extClass rfl)
      κ₀ (κ.mapExactFunctor V) hu.injective
      (supported_kummer_integral_equation R N hR i hI hT κ₀ hκ₀)
    rw [hsource, hroot]
    erw [boundary_forget φ T κ]
    exact supported_kummer_integral_equation A N hA i hI hT κ hκ


end AlgebraicGeometry.Etale
