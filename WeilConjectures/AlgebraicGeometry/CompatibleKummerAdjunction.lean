/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompatibleKummerCoefficients.CompatibleKummerCoefficientData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Derived free coefficients for the native Kummer boundary

Source: Stacks 07A6 and 09T5, native coefficient adjunction in Step 6
(blueprint: lem-pur-compatible-kummer-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

variable (ell : ℕ) [Fact ell.Prime]

/-- The free coefficient functor is additive, including for finite coefficients.
Source: Stacks 03EK (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: its forgetful right adjoint is additive, hence the left adjoint is additive. -/
instance compatibleKummerFree_additive (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell) :
    (Mod.free (condensedRingObj (c.obj ell) T)).Additive :=
  (Mod.freeForgetAdjunction _).left_adjoint_additive

/-- Free coefficients send K-flat quasi-isomorphisms to quasi-isomorphisms.
Source: Stacks 064K (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: an acyclic K-flat complex stays acyclic under tensoring with the
coefficient ring. The forgetful functor reflects exactness, so the free module
complex is acyclic. Apply this to the K-flat acyclic mapping cone of the map. -/
instance compatibleKummerFree_preservesKFlatQuasiIso (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell) :
    (Mod.free (condensedRingObj (c.obj ell) T)).PreservesKFlatQuasiIso := by
  apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  let R := condensedRingObj (c.obj ell) T
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa R
  have hl := ht.of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight R) _).app K).symm
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ (Mod.forget R)).1 (hl n)

/-- The derived free/forgetful adjunction imposes no flatness on the coefficient ring.
Source: Stacks 07A6 and 09T5 (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: derive the ordinary free/forgetful adjunction using K-flat resolutions
on abelian sheaves and K-injective resolutions on modules. Forgetting scalars
is exact, so its derived functor is its termwise functor. -/
def compatibleKummerFreeDerivedAdjunction (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell) :
    (Mod.free (condensedRingObj (c.obj ell) T)).leftDerivedFunctor ⊣
      (Mod.forget (condensedRingObj (c.obj ell) T)).mapDerivedCategory :=
  (Mod.freeForgetAdjunction _).derivedAdjunction.ofNatIsoRight
    (Mod.forget (condensedRingObj (c.obj ell) T)).rightDerivedFunctorIsoMapDerivedCategory

set_option maxHeartbeats 800000 in
-- The native ring presentation requires additional elaboration for linearity.
/-- Free coefficients on the abelian tensor unit are the regular module.
Source: Stacks 03EK (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: the right unitor is linear for the free and regular actions, by the
monoidal coherence identities. -/
def compatibleKummerFreeUnitIso (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell) :
    (Mod.free (condensedRingObj (c.obj ell) T)).obj (𝟙_ _) ≅
      Mod.regular (condensedRingObj (c.obj ell) T) := by
  let R := condensedRingObj (c.obj ell) T
  exact Mod.isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

/-- Derived free coefficients compute the regular module on the integral unit.
Source: Stacks 07A6 and 09T5 (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: the abelian tensor unit is flat, so its single complex is K-flat. The
counit of the derived free functor is therefore invertible there. Combine that
counit with the single-complex comparison and the ordinary free-unit unitor.
Finally use the monoidal constant-sheaf identification of the integral constant. -/
def compatibleKummerDerivedFreeUnitIso (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell) :
    (Mod.free (condensedRingObj (c.obj ell) T)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (CompatibleKummerCoefficients.integralConstant T)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (c.line ell T 0) := by
  let C := Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}
  let R := condensedRingObj (c.obj ell) T
  let F := Mod.free R
  let K := (CochainComplex.singleFunctor C 0).obj (𝟙_ C)
  have hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K :=
    (CochainComplex.kFlat_single_obj_iff_flat _ 0).2
      (ObjectProperty.flat_of_isDualizable isDualizable_unit)
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  let e : F.leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Mod.regular R) :=
    F.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso C).symm.app K) ≪≫
      asIso (F.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≪≫
      DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app (𝟙_ C)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Mod C R) 0).symm.app
        (F.obj (𝟙_ C))) ≪≫
      (DerivedCategory.singleFunctor (Mod C R) 0).mapIso
        (compatibleKummerFreeUnitIso ell T c)
  exact F.leftDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor C 0).mapIso
        (Functor.Monoidal.εIso (constantSheaf (ProEt.topology T)
          AddCommGrpCat.{u + 1})).symm) ≪≫ e

/-- Additive derived adjuncts with integral source and native module target.
Source: Stacks 07A6 and 09T5 (blueprint: lem-pur-compatible-kummer-adjunction).
Proof: use the derived free/forgetful Hom bijection. Its source is the
regular module by the K-flat unit computation. The target is transported through
forgetful functor comparisons with shifts and single objects. All these maps
are additive, and Ext identifies additively with shifted derived morphisms. -/
def compatibleKummerExtEquiv (T : Scheme.{u}) (c : PurityTransport.Coefficient ell)
    (Q : Mod (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
      (condensedRingObj (c.obj ell) T)) (n : ℕ) :
    Ext (c.line ell T 0) Q n ≃+
      Ext (CompatibleKummerCoefficients.integralConstant T) Q.X n := by
  let C := Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}
  let R := condensedRingObj (c.obj ell) T
  let F := (Mod.free R).leftDerivedFunctor
  let G := (Mod.forget (D := C) R).mapDerivedCategory
  let I := (DerivedCategory.singleFunctor C 0).obj
    (CompatibleKummerCoefficients.integralConstant T)
  let N := ((DerivedCategory.singleFunctor _ 0).obj Q) ⟦(n : ℤ)⟧
  let a := compatibleKummerFreeDerivedAdjunction ell T c
  have : F.Additive := a.left_adjoint_additive
  let e := compatibleKummerDerivedFreeUnitIso ell T c
  let e₁ : (((DerivedCategory.singleFunctor _ 0).obj (c.line ell T 0)) ⟶ N) ≃+
      (F.obj I ⟶ N) :=
    { Iso.homCongr e.symm (Iso.refl N) with
      map_add' := by
        intro x y
        change e.hom ≫ (x + y) ≫ (Iso.refl N).hom =
          e.hom ≫ x ≫ (Iso.refl N).hom + e.hom ≫ y ≫ (Iso.refl N).hom
        simp only [Preadditive.comp_add, Preadditive.add_comp] }
  let t : G.obj N ≅ ((DerivedCategory.singleFunctor C 0).obj Q.X) ⟦(n : ℤ)⟧ :=
    (G.commShiftIso (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso ((Mod.forget R).mapDerivedCategorySingleFunctor 0 |>.app Q)
  let e₂ : (I ⟶ G.obj N) ≃+
      (I ⟶ ((DerivedCategory.singleFunctor C 0).obj Q.X) ⟦(n : ℤ)⟧) :=
    { Iso.homCongr (Iso.refl I) t with
      map_add' := by
        intro x y
        change (Iso.refl I).inv ≫ (x + y) ≫ t.hom =
          (Iso.refl I).inv ≫ x ≫ t.hom + (Iso.refl I).inv ≫ y ≫ t.hom
        simp only [Preadditive.comp_add, Preadditive.add_comp] }
  exact Ext.homAddEquiv.trans
    ((e₁.trans (a.homAddEquiv I N)).trans e₂) |>.trans Ext.homAddEquiv.symm

/-- The additive native boundary before verifying its unit normalization.
Source: compatible-root Kummer construction, Step 6
(blueprint: lem-pur-compatible-kummer-adjunction).
Proof: composition with the given positive Kummer class is additive. Transport
this composite through the inverse additive derived coefficient adjunct. -/
def compatibleKummerAdditiveBoundary (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell)
    (κ : Ext (Scheme.proEtaleUnitsSheaf T) (c.line ell T 1).X 1) :
    Ext (CompatibleKummerCoefficients.integralConstant T) (Scheme.proEtaleUnitsSheaf T) 1 →+
      Ext (c.line ell T 0) (c.line ell T 1) 2 :=
  (compatibleKummerExtEquiv ell T c (c.line ell T 1) 2).symm.toAddMonoidHom.comp {
    toFun := fun α ↦ α.comp κ rfl
    map_zero' := by simp
    map_add' := by intros; simp }

/-- A computed generator formula for the additive equivalence gives the exact adjunct law.
Source: compatible-root Kummer construction, Step 6
(blueprint: lem-pur-compatible-kummer-adjunction).
Proof: the additive boundary is the inverse equivalence of the composite with
kappa. Apply the equivalence to both sides of the claimed equality and use its
two inverse identities. The generator formula identifies its value on b. -/
theorem compatibleKummerAdditiveBoundary_adjunct (T : Scheme.{u})
    (c : PurityTransport.Coefficient ell)
    (hη : ∀ b : Ext (c.line ell T 0) (c.line ell T 1) 2,
      compatibleKummerExtEquiv ell T c (c.line ell T 1) 2 b =
        (Ext.mk₀ (CompatibleKummerCoefficients.generator ell c T)).comp
          (b.mapExactFunctor (Mod.forget (condensedRingObj (c.obj ell) T))) (zero_add 2))
    (κ : Ext (Scheme.proEtaleUnitsSheaf T) (c.line ell T 1).X 1)
    (α : Ext (CompatibleKummerCoefficients.integralConstant T)
      (Scheme.proEtaleUnitsSheaf T) 1)
    (b : Ext (c.line ell T 0) (c.line ell T 1) 2) :
    cartierScalarBoundaryEquation (Mod.forget (condensedRingObj (c.obj ell) T))
        (CompatibleKummerCoefficients.generator ell c T) b α κ ↔
      compatibleKummerAdditiveBoundary ell T c κ α = b := by
  change (Ext.mk₀ (CompatibleKummerCoefficients.generator ell c T)).comp
      (b.mapExactFunctor (Mod.forget (condensedRingObj (c.obj ell) T))) (zero_add 2) =
    α.comp κ rfl ↔ _
  rw [← hη b]
  change compatibleKummerExtEquiv ell T c (c.line ell T 1) 2 b =
      (α.comp κ rfl : Ext (CompatibleKummerCoefficients.integralConstant T)
        (c.line ell T 1).X 2) ↔
    (compatibleKummerExtEquiv ell T c (c.line ell T 1) 2).symm (α.comp κ rfl) = b
  constructor
  · intro h
    apply (compatibleKummerExtEquiv ell T c (c.line ell T 1) 2).injective
    simpa only [AddEquiv.apply_symm_apply] using h.symm
  · intro h
    rw [← h]
    exact AddEquiv.apply_symm_apply _ _

end AlgebraicGeometry.ProEtale
