/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.Paper.FibreFunctorBasepointTransportData
public import Sheaf.Paper.LisseRationalScalarFiberMaps
public import Sheaf.Paper.IntegralFibreScalarComparison

/-! # Rational coefficient comparisons and their path squares
Source: Deligne, Weil II (1.1.1) c), d), pp.146-147.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme
private theorem ringToTensorUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (r : R →+* S) (M : ModuleCat.{u + 1} R) (x : M) :
    (((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r)).hom.app M)
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app M x) =
      (1 : S) ⊗ₜ[R,r] x := by
  exact ConcreteCategory.congr_hom
    ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit_leftAdjointUniq_hom_app
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r) M) x

private theorem tensorToRingUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (r : R →+* S) (M : ModuleCat.{u + 1} R) (x : M) :
    (((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r)).inv.app M)
        ((1 : S) ⊗ₜ[R,r] x) =
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app M x := by
  rw [Adjunction.leftAdjointUniq_inv_app]
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).unit_leftAdjointUniq_hom_app
        (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r) M) x

private theorem ringCompUnit {R S A : Type (u + 1)} [Ring R] [Ring S] [Ring A]
    (α : R →+* S) (q : S →+* A) (M : ModuleCat.{u + 1} R) (x : M) :
    (ModuleCat.ringExtensionComp.{u + 1, u + 1} α q).hom.app M
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} q).unit.app _
          ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app M x)) =
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (q.comp α)).unit.app M x := by
  let adj₁ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α
  let adj₂ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} q
  let adj₃ := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (q.comp α)
  exact ConcreteCategory.congr_hom ((adj₁.comp adj₂).unit_leftAdjointUniq_hom_app
    (adj₃.ofNatIsoRight (ModuleCat.restrictScalarsComp α q)) M) x

private theorem ringCompInvUnit {R S A : Type (u + 1)} [Ring R] [Ring S] [Ring A]
    (α : R →+* S) (q : S →+* A) (M : ModuleCat.{u + 1} R) (x : M) :
    (ModuleCat.ringExtensionComp.{u + 1, u + 1} α q).inv.app M
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} (q.comp α)).unit.app M x) =
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} q).unit.app _
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app M x) := by
  rw [← ringCompUnit α q M x]
  exact ConcreteCategory.congr_hom
    ((ModuleCat.ringExtensionComp.{u + 1, u + 1} α q).app M).hom_inv_id _

private theorem ringMapUnit {R S : Type (u + 1)} [Ring R] [Ring S]
    (r : R →+* S) {M N : ModuleCat.{u + 1} R} (f : M ⟶ N) (x : M) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} r).map f
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app M x) =
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app N (f x) :=
  (ConcreteCategory.congr_hom
    ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.naturality f) x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem ringUnitEq {R S : Type (u + 1)} [CommRing R] [CommRing S]
    {r s : R →+* S} (h : r = s) (M : ModuleCat.{u + 1} R) (x : M) :
    ((eqToIso (congrArg (fun q : R →+* S ↦
      (ModuleCat.ringExtendScalars.{u + 1, u + 1} q :
        ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)) h)).hom.app M)
        ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).unit.app M x) =
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} s).unit.app M x := by
  cases h
  rfl

private theorem tensorCompInvUnit {R S A : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing A]
    (r : R →+* S) (s : S →+* A) (M : ModuleCat.{u + 1} R) (x : M) :
    (ModuleCat.extendScalarsComp.{u + 1, u + 1} r s).inv.app M
        ((1 : A) ⊗ₜ[S,s] ((1 : S) ⊗ₜ[R,r] x)) =
      (1 : A) ⊗ₜ[R,s.comp r] x := by
  rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul.{u + 1, u + 1} r s M x]
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalarsComp.{u + 1, u + 1} r s).app M).hom_inv_id _

private theorem tensorAlgebraIso_unit {R A : Type (u + 1)}
    [CommRing R] [CommRing A] [Algebra R A] (M : ModuleCat.{u + 1} R) (x : M) :
    (tensorAlgebraIso (A := A) M).hom ((1 : A) ⊗ₜ[R,algebraMap R A] x) =
      (1 : A) ⊗ₜ[R] x := by
  rfl

private theorem tensorAlgebraIso_inv_unit {R A : Type (u + 1)}
    [CommRing R] [CommRing A] [Algebra R A] (M : ModuleCat.{u + 1} R) (x : M) :
    (tensorAlgebraIso (A := A) M).inv ((1 : A) ⊗ₜ[R] x) =
      (1 : A) ⊗ₜ[R,algebraMap R A] x := by
  rfl

private theorem scalarUnitChain {R S E L K : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing E] [CommRing L] [CommRing K]
    [Algebra R E] [Algebra S L] (α : R →+* S) (j : E →+* K) (k : L →+* K)
    (hα : (k.comp (algebraMap S L)).comp α = j.comp (algebraMap R E))
    (M : ModuleCat.{u + 1} R) (N : ModuleCat.{u + 1} S)
    (c : (ModuleCat.ringExtendScalars.{u + 1, u + 1} α).obj M ⟶ N) (x : M) :
    let r := j.comp (algebraMap R E)
    let q := k.comp (algebraMap S L)
    let eR := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r)
    let eS := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} q).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q)
    ((ModuleCat.extendScalars k).map (tensorAlgebraIso (A := L) N).hom)
      ((ModuleCat.extendScalarsComp.{u + 1, u + 1} (algebraMap S L) k).hom.app N
        (eS.hom.app N
          ((ModuleCat.ringExtendScalars.{u + 1, u + 1} q).map c
            ((ModuleCat.ringExtensionComp.{u + 1, u + 1} α q).inv.app M
              ((eqToIso (congrArg (fun f : R →+* K ↦
                ModuleCat.ringExtendScalars.{u + 1, u + 1} f) hα.symm)).hom.app M
                (eR.inv.app M
                  ((ModuleCat.extendScalarsComp.{u + 1, u + 1} (algebraMap R E) j).inv.app M
                    ((ModuleCat.extendScalars j).map (tensorAlgebraIso (A := E) M).inv
                      ((1 : K) ⊗ₜ[E,j] ((1 : E) ⊗ₜ[R] x)))))))))) =
      (1 : K) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[S]
        (c ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app M x))) := by
  dsimp only
  rw [ModuleCat.ExtendScalars.map_tmul, tensorAlgebraIso_inv_unit,
    tensorCompInvUnit, tensorToRingUnit, ringUnitEq, ringCompInvUnit,
    ringMapUnit, ringToTensorUnit, ModuleCat.extendScalarsComp_hom_app_one_tmul,
    ModuleCat.ExtendScalars.map_tmul, tensorAlgebraIso_unit]
  exact hα.symm

private theorem algebra_smul_unit_tensor {R A : Type (u + 1)}
    [CommRing R] [CommRing A] [Algebra R A] (M : ModuleCat.{u + 1} R)
    (a : A) (x : M) :
    (a • ((1 : A) ⊗ₜ[R] x) : A ⊗[R] M) = a ⊗ₜ[R] x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem scalar_smul_unit_tensor {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat.{u + 1} R)
    (a : S) (x : M) :
    a • ((1 : S) ⊗ₜ[R,f] x) = a ⊗ₜ[R,f] x := by
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private theorem scalarId_apply {R : Type (u + 1)} [CommRing R]
    (M : ModuleCat.{u + 1} R) (a : R) (x : M) :
    (ModuleCat.extendScalarsId.{u + 1, u + 1} R).hom.app M
      (a ⊗ₜ[R,RingHom.id R] x) = a • x := by
  have h : a ⊗ₜ[R,RingHom.id R] x =
      a • ((1 : R) ⊗ₜ[R,RingHom.id R] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [h, map_smul, ModuleCat.extendScalarsId_hom_app_one_tmul]

private theorem tensor_coefficients {R E K : Type (u + 1)}
    [CommRing R] [CommRing E] [CommRing K] [Algebra R E]
    (j : E →+* K) (M : ModuleCat.{u + 1} R) (a : K) (b : E) (x : M) :
    a ⊗ₜ[E,j] (b ⊗ₜ[R] x) =
      (a * j b) • ((1 : K) ⊗ₜ[E,j] ((1 : E) ⊗ₜ[R] x)) := by
  let := j.toAlgebra
  change a ⊗ₜ[E] (b ⊗ₜ[R] x) =
    (a * j b) • ((1 : K) ⊗ₜ[E] ((1 : E) ⊗ₜ[R] x))
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    RingHom.algebraMap_toAlgebra, Algebra.smul_def, mul_comm, one_mul] using
      (TensorProduct.smul_tmul (R := E) b a ((1 : E) ⊗ₜ[R] x)).symm

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
private theorem rationalScalarFiberIso_unit (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)
    (F : LisseRationalSheaf l E Y)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom
        ((1 : K) ⊗ₜ[E,j] ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E] x)) =
      (1 : K) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        (integralFibreScalarUnit l Y y E L ι F.integral x)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let α := lisseIntegerInclusion l E L ι
  let r := j.comp (algebraMap R E)
  let q := k.comp (algebraMap S L)
  have hα : q.comp α = r := by
    ext a
    change k (α a : L) = j (a : E)
    have ha : (α a : L) = ι (a : E) :=
      (lisseIntegerInclusion_exists l E L ι).choose_spec a
    exact (congrArg k ha).trans (congrArg (fun f : E →+* K ↦ f (a : E)) hjk)
  let M := lisseIntegralFiber l E Y y F.integral
  let N := lisseIntegralFiber l L Y y
    ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F.integral)
  let c := lisseIntegralScalarFiberComparison Y y l E L ι F.integral
  let eR := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r)
  let eS := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} q).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q)
  unfold integralFibreScalarUnit
  unfold lisseRationalScalarFiberIso lisseIntegralRationalFiberKNatIso
    lisseIntegralScalarFiberKNatIso integralFibreScalarIso lisseIntegralScalarExtension
  with_unfolding_all
    change
      ((ModuleCat.extendScalars k).map (tensorAlgebraIso (A := L) N).hom)
        ((ModuleCat.extendScalarsComp.{u + 1, u + 1} (algebraMap S L) k).hom.app N
          (eS.hom.app N
            ((ModuleCat.ringExtendScalars.{u + 1, u + 1} q).map c
              ((ModuleCat.ringExtensionComp.{u + 1, u + 1} α q).inv.app M
                ((eqToIso (congrArg (fun f : R →+* K ↦
                  ModuleCat.ringExtendScalars.{u + 1, u + 1} f) hα.symm)).hom.app M
                  (eR.inv.app M
                    ((ModuleCat.extendScalarsComp.{u + 1, u + 1} (algebraMap R E) j).inv.app M
                      ((ModuleCat.extendScalars j).map (tensorAlgebraIso (A := E) M).inv
                        ((1 : K) ⊗ₜ[E,j] ((1 : E) ⊗ₜ[R] x)))))))))) =
        (1 : K) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[S]
          (c ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} α).unit.app M x)))
  exact scalarUnitChain α j k hα M N c x

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
/-- The scalar comparison on arbitrary pure tensors.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison).
Proof: balance the inner rational coefficient into K, use K-linearity and the unit
calculation, and balance back on the target. -/
theorem rationalScalarFiberIso_tensor (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)
    (F : LisseRationalSheaf l E Y) (a : K) (b : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom
        (a ⊗ₜ[E,j] (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x)) =
      (a * j b) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        (integralFibreScalarUnit l Y y E L ι F.integral x)) := by
  rw [tensor_coefficients j _ a b x]
  change (lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom.hom
    ((a * j b) • _) = _
  rw [map_smul, rationalScalarFiberIso_unit]
  exact scalar_smul_unit_tensor k _ (a * j b) _

/-- Rational scalar comparison into an arbitrary common coefficient field.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison). -/
@[irreducible]
def rationalFibreComparisonIso (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j) :
    lisseRationalFiberFunctor l E Y y ⋙ ModuleCat.extendScalars j ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalFiberFunctor l L Y y ⋙
        ModuleCat.extendScalars k :=
  lisseRationalFiberComparisonNatIso Y y l E L ι K j k hjk _ _
    (lisseRationalFiberFunctor_obj l E Y y) (lisseRationalFiberFunctor_obj l L Y y)
    (lisseRationalFiberFunctor_map_spec l E Y y)
    (lisseRationalFiberFunctor_map_spec l L Y y)

set_option maxRecDepth 2000 in
/-- Pure-tensor evaluation after transporting the recorded rational fibre objects.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison).
Proof: cancel the two object transports in the comparison and apply its tensor formula. -/
theorem rationalFibreComparisonIso_tensor (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)
    (F : LisseRationalSheaf l E Y) (a : K) (b : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (ModuleCat.extendScalars k).map
      (eqToHom (lisseRationalFiberFunctor_obj l L Y y
        ((lisseRationalScalarExtension l E Y L ι).obj F)))
      ((rationalFibreComparisonIso l Y y E L ι K j k hjk).hom.app F
        (a ⊗ₜ[E,j] (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x)))) =
      (a * j b) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        (integralFibreScalarUnit l Y y E L ι F.integral x)) := by
  let he := lisseRationalFiberFunctor_obj l E Y y F
  let hl := lisseRationalFiberFunctor_obj l L Y y
    ((lisseRationalScalarExtension l E Y L ι).obj F)
  have hj : (ModuleCat.extendScalars j).map (eqToHom he)
      (a ⊗ₜ[E,j] (eqToHom he.symm (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x))) =
        a ⊗ₜ[E,j] (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x) := by
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact congrArg (fun v ↦ a ⊗ₜ[E,j] v)
      (ConcreteCategory.congr_hom (eqToIso he).inv_hom_id _)
  have hk (v : (ModuleCat.extendScalars k).obj
      (lisseRationalFiber l L Y y ((lisseRationalScalarExtension l E Y L ι).obj F))) :
      (ModuleCat.extendScalars k).map (eqToHom hl)
        ((ModuleCat.extendScalars k).map (eqToHom hl.symm) v) = v :=
    ConcreteCategory.congr_hom ((ModuleCat.extendScalars k).mapIso (eqToIso hl)).inv_hom_id v
  unfold rationalFibreComparisonIso lisseRationalFiberComparisonNatIso
    lisseRationalFiberComparison
  change (ModuleCat.extendScalars k).map (eqToHom hl)
    ((ModuleCat.extendScalars k).map (eqToHom hl.symm)
      ((lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom
        ((ModuleCat.extendScalars j).map (eqToHom he)
          (a ⊗ₜ[E,j] (eqToHom he.symm
            (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x)))))) = _
  rw [hk, hj]
  exact rationalScalarFiberIso_tensor l Y y E L ι K j k hjk F a b x

set_option maxRecDepth 2000 in
/-- Pure-tensor evaluation with the target object transport left on the output.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison).
Proof: cancel scalar extension of the target object isomorphism. -/
theorem rationalFibreComparisonIso_apply (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)
    (F : LisseRationalSheaf l E Y) (a : K) (b : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (rationalFibreComparisonIso l Y y E L ι K j k hjk).hom.app F
        (a ⊗ₜ[E,j] (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x))) =
      (ModuleCat.extendScalars k).map
        (eqToHom (lisseRationalFiberFunctor_obj l L Y y
          ((lisseRationalScalarExtension l E Y L ι).obj F)).symm)
        ((a * j b) ⊗ₜ[L,k] ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
          (integralFibreScalarUnit l Y y E L ι F.integral x))) := by
  let h := lisseRationalFiberFunctor_obj l L Y y
    ((lisseRationalScalarExtension l E Y L ι).obj F)
  apply (ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalars k).map (eqToHom h))).injective
  exact (rationalFibreComparisonIso_tensor l Y y E L ι K j k hjk F a b x).trans
    (ConcreteCategory.congr_hom ((ModuleCat.extendScalars k).mapIso (eqToIso h)).inv_hom_id _).symm

set_option maxRecDepth 2000 in
/-- Pure-tensor comparison with scalar-extension object transport inside the tensor.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison).
Proof: evaluate scalar extension of the target object transport on a pure tensor. -/
theorem rationalFibreComparisonIso_tmul (K : Type (u + 1)) [Field K]
    (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)
    (F : LisseRationalSheaf l E Y) (a : K) (b : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    (rationalFibreComparisonIso l Y y E L ι K j k hjk).hom.app F
        (a ⊗ₜ[E,j] (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x))) =
      (a * j b) ⊗ₜ[L,k] (eqToHom (lisseRationalFiberFunctor_obj l L Y y
        ((lisseRationalScalarExtension l E Y L ι).obj F)).symm
        ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
          (integralFibreScalarUnit l Y y E L ι F.integral x))) := by
  exact (rationalFibreComparisonIso_apply l Y y E L ι K j k hjk F a b x).trans
    (ModuleCat.ExtendScalars.map_tmul _ _ _ _)

variable [Algebra E L] (ha : algebraMap E L = ι.toRingHom)

set_option backward.isDefEq.respectTransparency false in
/-- The rational scalar comparison with its final identity extension removed.
Source: Weil II (1.1.1) c), d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison). -/
@[irreducible]
def rationalFibreScalarIso :
    lisseRationalFiberFunctor l E Y y ⋙ ModuleCat.extendScalars (algebraMap E L) ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalFiberFunctor l L Y y := by
  have hjk : (RingHom.id L).comp ι.toRingHom = algebraMap E L := ha.symm
  exact rationalFibreComparisonIso l Y y E L ι L
      (algebraMap E L) (RingHom.id L) hjk ≪≫
    Functor.isoWhiskerLeft (lisseRationalScalarExtension l E Y L ι)
      (Functor.isoWhiskerLeft (lisseRationalFiberFunctor l L Y y)
        (ModuleCat.extendScalarsId.{u + 1, u + 1} L) ≪≫ Functor.rightUnitor _)

set_option maxRecDepth 2000 in
/-- The rational scalar comparison is the canonical pure-tensor map.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-rational-fibre-scalar-comparison).
Proof: apply the comparison formula with common field L, then remove extension by
the identity. Its component sends a tensor v to a times v; linear object transport
and tensor balancing give the stated product of coefficients. -/
theorem rationalFibreScalarIso_tensor (F : LisseRationalSheaf l E Y) (a : L) (b : E)
    (x : (lisseIntegralFiberFunctor l E Y y).obj F.integral) :
    eqToHom (lisseRationalFiberFunctor_obj l L Y y
      ((lisseRationalScalarExtension l E Y L ι).obj F))
      ((rationalFibreScalarIso l Y y E L ι ha).hom.app F
        (a ⊗ₜ[E,algebraMap E L]
          (eqToHom (lisseRationalFiberFunctor_obj l E Y y F).symm
            (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] x)))) =
      (a * ι b) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        ((integralFibreScalarIso l Y y E L ι).hom.app F.integral
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseIntegerInclusion l E L ι) _ 1 x)) := by
  let H := (lisseRationalScalarExtension l E Y L ι).obj F
  let hL := lisseRationalFiberFunctor_obj l L Y y H
  unfold rationalFibreScalarIso
  change eqToHom hL
    ((ModuleCat.extendScalarsId.{u + 1, u + 1} L).hom.app
      ((lisseRationalFiberFunctor l L Y y).obj H)
      ((rationalFibreComparisonIso l Y y E L ι L
        (algebraMap E L) (RingHom.id L) ha.symm).hom.app F
        (a ⊗ₜ[E,algebraMap E L] (eqToHom
          (lisseRationalFiberFunctor_obj l E Y y F).symm (b ⊗ₜ[_] x))))) = _
  rw [rationalFibreComparisonIso_apply, ModuleCat.ExtendScalars.map_tmul,
    scalarId_apply]
  change (eqToHom hL).hom (_ • _) = _
  rw [map_smul]
  let v : lisseRationalFiber l L Y y H :=
    (1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L]
      (integralFibreScalarUnit l Y y E L ι F.integral x)
  change (a * (algebraMap E L) b) • (eqToHom hL (eqToHom hL.symm v)) = _
  refine (congrArg (fun v ↦ (a * (algebraMap E L) b) • v)
    ((eqToIso hL).toLinearEquiv.apply_symm_apply v)).trans ?_
  dsimp only [v]
  simp only [ha]
  exact (algebra_smul_unit_tensor _ (a * ι b) _).trans
    (congrArg (fun v ↦ (a * ι b) ⊗ₜ[Padic.coefficientExtensionIntegers l L] v)
      (integralFibreScalarUnit_eq l Y y E L ι F.integral x))

end AlgebraicGeometry.Scheme
