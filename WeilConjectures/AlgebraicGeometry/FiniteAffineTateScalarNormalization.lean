/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarBalancingExistence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization

/-! # Root normalization and flat-single invertibility of affine Tate scalar maps

Source: Charts of reduction-exceptional, retained Steps 4 and 10
(blueprint: lem-sp-finite-affine-tate-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

open Scheme
open ProEtale in
private theorem chartTateOneScalar_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (ProEtale.chartEtaleTateOneScalarIso φ T N hA hB).hom =
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
        (ProEtale.reductionEtaleTateMap φ T N hA hB) := by
  let J := T.smallEtaleTopology
  let rA := finiteEtaleTwistScalar N A hA
  let rB := finiteEtaleTwistScalar N B hB
  have hr : rB = φ.comp rA := by
    apply Subsingleton.elim
  let a := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rA).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let b := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rB).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let c := a.comp (etaleSheafExtendScalarsAdjunction φ T)
  let r : Sheaf.restrictScalars J φ ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rA)) ≅
      sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rB) :=
    NatIso.ofComponents (fun L ↦
    Functor.isoWhiskerLeft L.obj (ModuleCat.restrictScalarsComp' rA φ rB hr).symm)
    (by intro L M f; ext W x; rfl)
  let e := (c.ofNatIsoRight r).leftAdjointUniq b
  let P := finiteEtaleMuModulePresheaf T N
  have he : (a.homEquiv _ _
      ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P))) =
        b.unit.app P ≫ r.inv.app _ := by
    have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app (c.ofNatIsoRight r) b P
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
    have hh' := (Iso.eq_comp_inv (r.app _)).2 hh
    exact hh'
  have hτ : (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P) =
      reductionEtaleTateMap φ T N hA hB := by
    apply (reductionEtaleTateMap_existsUnique φ T N hA hB).unique
      (y₁ := (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P))
      (y₂ := reductionEtaleTateMap φ T N hA hB) ?_
      (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec
    intro W x z
    have hh := congrArg (fun η ↦ (η.app W) z) he
    change _ = _ at hh
    let τ : finiteEtaleTateLine T N A hA ⟶
        (Sheaf.restrictScalars J φ).obj (finiteEtaleTateLine T N B hB) :=
      (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P)
    have h1 : τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z) =
        finiteEtaleTateOneGenerator B N T hB W 1 z := hh
    have hs (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0) (v : R) :
        finiteEtaleTateOneGenerator R N T hR W v z =
          v • finiteEtaleTateOneGenerator R N T hR W 1 z := by
      let _ := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N W)
      let q := (toSheafify J (P ⋙ ModuleCat.extendScalars
        (finiteEtaleTwistScalar N R hR))).app W
      change q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
        (Module.compHom _ (finiteEtaleTwistScalar N R hR)) _ v z) =
          v • q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
            (Module.compHom _ (finiteEtaleTwistScalar N R hR)) _ (1 : R) z)
      rw [← map_smul]
      congr 1
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N R hR)
          v 1 (show P.obj W from z)).symm
    change τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W x z) = _
    rw [hs A hA x, map_smul]
    change φ x • (show (finiteEtaleTateLine T N B hB).obj.obj W from
      τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z)) = _
    have h1B : (show (finiteEtaleTateLine T N B hB).obj.obj W from
        τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z)) =
          finiteEtaleTateOneGenerator B N T hB W 1 z := h1
    exact (congrArg (fun t : (finiteEtaleTateLine T N B hB).obj.obj W ↦ φ x • t) h1B).trans
      (hs B hB (φ x)).symm
  have heq : ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (reductionEtaleTateMap φ T N hA hB) = e.hom.app P := by
    apply ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).injective
    exact (Equiv.apply_symm_apply _ _).trans hτ.symm
  change (ProEtale.chartEtaleTateOneScalarIso φ T N hA hB).hom = _
  exact heq.symm

open WeilConjectures.PurityFiniteSetting in
private theorem chartTateScalar_eq_balancing
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    ProEtale.chartEtaleTateScalarIso φ T N hA hB = balancingFamily φ N hA hB T := by
  funext r
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    apply Iso.ext
    exact chartTateOneScalar_eq φ T N hA hB
  | more r ih₀ ih₁ =>
    apply Iso.ext
    simp only [ProEtale.chartEtaleTateScalarIso, balancingFamily, Iso.trans_hom]
    rw [ih₁]
    congr 1
    exact congrArg (fun f ↦ MonoidalCategory.tensorHom
      (balancingFamily φ N hA hB T (r + 1)).hom f)
      (chartTateOneScalar_eq φ T N hA hB)

private theorem finiteAffineTateScalarMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    IsIso (finiteAffineTateScalarMap φ T N hA hB d) := by
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist T N A hA d) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line T N hN
        (fun x ↦ by
          simpa only [map_natCast] using
            hT.map (T.presheaf.germ ⊤ x (by trivial)).hom) A hA d).2.2.1
  have hsingle : IsIso (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
      (Scheme.finiteEtaleTateTwist T N A hA d)) := by
    let E := ProEtale.etaleSheafExtendScalars φ T
    let U := Sheaf.restrictScalars T.smallEtaleTopology φ
    let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ T
    exact ProEtale.reductionFlatSingleAdjunct_isIso E U
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T) (L := scalarExtension φ T)
      (purityScalarAdjunction φ T) _ hflat
  unfold finiteAffineTateScalarMap
  infer_instance

/-- The explicit chart family has the prescribed root/scalar normalization, and its
actual derived scalar/single maps are invertible on every nonnegative Tate power.

Source: Charts, retained Steps 4 and 10; the flat rank-one Tate calculation
(blueprint: lem-sp-finite-affine-tate-scalar-normalization).
Proof: uniqueness of adjoints computes the degree-one chart map on the scalar unit.
It sends the root generator with coefficient one to the same root generator.
Linearity gives the formula for every coefficient. Induct on ordered tensor powers,
using the oplax tensorator, to identify the chart family with the constructed
balancing family. Its generator formula, zero-power unit and successor recursion
are the required normalization. Finally, the Tate sheaf is flat; its single complex
is K-flat, so its scalar/single adjunct is invertible. Compose it with the single
of the ordinary balancing isomorphism. This also treats the tensor unit (power zero),
zero rings and empty schemes; it assumes no flatness of B over A. The existing
unique normalized source family gives the scalar-unit and shifted zero-power unit
equations. Balancing uniqueness identifies the explicit family with that family,
giving its coefficient-unit and zero-power source equations for arbitrary inputs. -/
theorem finiteAffineTateScalar_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    WeilConjectures.PurityFiniteSetting.IsFiniteTateScalarBalancing φ N hA hB T
        (ProEtale.chartEtaleTateScalarIso φ T N hA hB) ∧
      WeilConjectures.PurityFiniteSetting.IsFiniteTateScalarLineNormalized φ N hA hB T
          (ProEtale.chartEtaleTateScalarIso φ T N hA hB) ∧
        (∀ d : ℕ, IsIso (finiteAffineTateScalarMap φ T N hA hB d)) ∧
      WeilConjectures.PurityFiniteSetting.IsFiniteTateScalarSourceUnitNormalized
        φ N hA hB T (ProEtale.chartEtaleTateScalarIso φ T N hA hB) ∧
      WeilConjectures.PurityFiniteSetting.IsFiniteTateScalarSourceZeroNormalized
        φ N hA hB T (ProEtale.chartEtaleTateScalarIso φ T N hA hB) := by
  have hbal : WeilConjectures.PurityFiniteSetting.IsFiniteTateScalarBalancing
      φ N hA hB T (ProEtale.chartEtaleTateScalarIso φ T N hA hB) := by
    rw [chartTateScalar_eq_balancing]
    open WeilConjectures.PurityFiniteSetting in
      refine ⟨?_, rfl, fun _ ↦ rfl⟩
    intro r U a b z
    rw [map_smul]
    dsimp only [id]
    erw [WeilConjectures.PurityFiniteSetting.balancingNormalized φ N hA hB T r U a z]
    simpa only [mul_comm] using
      WeilConjectures.PurityFiniteSetting.balancingPowerCoefficient B N hB T r U (φ a) b z
  obtain ⟨β, hβ, _⟩ :=
    (WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization
      φ N hN hA hB T (fun x ↦ by
        simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2
  have heq : β = ProEtale.chartEtaleTateScalarIso φ T N hA hB :=
    WeilConjectures.PurityFiniteSetting.balancing_unique φ N hA hB T _ _ hβ.1 hbal
  subst β
  exact ⟨hbal, hβ.2.1, finiteAffineTateScalarMap_isIso φ T N hN hA hB hT,
    hβ.2.2.2.1, hβ.2.2.2.2⟩

end AlgebraicGeometry.Etale
