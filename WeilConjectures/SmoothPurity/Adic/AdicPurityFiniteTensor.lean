/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import WeilConjectures.SmoothPurity.Adic.AdicPurityTwistRestrictionComponents
import WeilConjectures.SmoothPurity.Adic.AdicPurityFiniteTensorComponents
/-! # Derived reduction of the root-normalized integral twist
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: def-pur-adic-finite-tensor-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

omit [Fact l.Prime] hInvert in
private theorem adicTensor_ext
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (F H K : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {f g : (SheafOfModules.siteSheafTensorRight H).obj F ⟶ K}
    (h : ∀ (W : T.ProEtᵒᵖ) (x : F.val.obj W) (y : H.val.obj W),
      f.val.app W (SheafOfModules.siteSheafTensorTmul F H W x y) =
        g.val.app W (SheafOfModules.siteSheafTensorTmul F H W x y)) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv
    (SheafOfModules.siteTensorPresheaf F.val H.val) K).injective
  ext W : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact h W x y

omit [Fact l.Prime] hInvert in
private theorem adicTensor_map
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (F F' H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (f : F ⟶ F') (W : T.ProEtᵒᵖ) (x : F.val.obj W) (y : H.val.obj W) :
    ((SheafOfModules.siteSheafTensorRight H).map f).val.app W
        (SheafOfModules.siteSheafTensorTmul F H W x y) =
      SheafOfModules.siteSheafTensorTmul F' H W (f.val.app W x) y := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _)).unit.naturality
        (SheafOfModules.siteTensorHom f.val H.val)
  exact (congrArg (fun k ↦ k.app W (x ⊗ₜ[R.obj.obj W] y)) h).symm

/-- The actual ordinary finite tensor-by-line functor.
Source: blueprint twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityFiniteSheafTwist (d : ℕ) :=
  SheafOfModules.siteSheafTensorRight
    (A := integralCoefficientCommRingSheaf l E T n)
    (finiteCoefficientTwist l E T n (d : ℤ))

/-- The ordinary twist/restriction comparison is uniquely specified on all balanced
local tensors, using the root-normalized quotient map already constructed.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: send x tensor y to x tensor c_d(y). The quotient-line equations make this
balanced over the completed coefficient sheaf. It commutes with restriction and
therefore sheafifies. On a cover trivializing the integral line it is the identity
on the finite module, so it is invertible. Local tensor generation proves uniqueness. -/
theorem adicPurityTwistRestriction_existsUnique (d : ℕ) :
    ∃! e : scalarReductionRestriction l E T n ⋙ integralSheafTwist l E T (d : ℤ) ≅
      adicPurityFiniteSheafTwist l E n T d ⋙ scalarReductionRestriction l E T n,
      ∀ (M : scalarReductionTarget l E T n) (W : T.ProEtᵒᵖ)
        (x : M.val.obj W) (y : (integralTwistLine l E T (d : ℤ)).val.obj W),
        (e.hom.app M).val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted l E T) _ _ W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W x
              ((adicPurityRootQuotients l E n T d).val.app W y) := by
  choose e he using adicPurityTwistRestriction_component l E n T d
  let c : scalarReductionRestriction l E T n ⋙ integralSheafTwist l E T (d : ℤ) ≅
      adicPurityFiniteSheafTwist l E n T d ⋙ scalarReductionRestriction l E T n :=
    NatIso.ofComponents e (by
      intro M N f
      apply adicTensor_ext T
      intro W x y
      change (e N).hom.val.app W
          (((integralSheafTwist l E T (d : ℤ)).map
            ((scalarReductionRestriction l E T n).map f)).val.app W
              (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ W x y)) =
        ((adicPurityFiniteSheafTwist l E n T d).map f).val.app W
          ((e M).hom.val.app W
            (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ W x y))
      have hm := adicTensor_map T
        (R := completedIntegralCommRingSheafUnrestricted l E T)
        ((scalarReductionRestriction l E T n).obj M)
        ((scalarReductionRestriction l E T n).obj N) (integralTwistLine l E T (d : ℤ))
        ((scalarReductionRestriction l E T n).map f) W x y
      have hf := adicTensor_map T (R := integralCoefficientCommRingSheaf l E T n)
        M N (finiteCoefficientTwist l E T n (d : ℤ)) f W x
        ((adicPurityRootQuotients l E n T d).val.app W y)
      exact (congrArg ((e N).hom.val.app W) hm).trans
        ((he N W (f.val.app W x) y).trans
          (hf.symm.trans (congrArg
            (((adicPurityFiniteSheafTwist l E n T d).map f).val.app W)
            (he M W x y).symm))))
  refine ⟨c, he, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply adicTensor_ext T
  intro W x y
  exact (hc' M W x y).trans (he M W x y).symm

/-- The ordinary comparison, with its pure-tensor normalization retained.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityTwistRestriction (d : ℕ) :=
  (adicPurityTwistRestriction_existsUnique l E n T d).exists.choose

/-- Exactness of the finite tensor-by-line functor, inherited from its invertible line.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: the finite twisting line is locally free of rank one, hence tensoring with it
is locally isomorphic to the identity. Addition, kernels and cokernels descend from
these local identifications. -/
theorem adicPurityFiniteSheafTwist_exact (d : ℕ) :
    (adicPurityFiniteSheafTwist l E n T d).Additive ∧
      PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d) ∧
      PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d) := by
  exact coefficientTwistLine_exact T (purTwistFiniteOne T l E n) (d : ℤ)
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_additive (d : ℕ) :
    (adicPurityFiniteSheafTwist l E n T d).Additive :=
  (adicPurityFiniteSheafTwist_exact l E n T d).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_limits (d : ℕ) :
    PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d) :=
  (adicPurityFiniteSheafTwist_exact l E n T d).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_colimits (d : ℕ) :
    PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d) :=
  (adicPurityFiniteSheafTwist_exact l E n T d).2.2

omit hInvert in
private theorem adicUnit_surjective
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
    (W : T.ProEtᵒᵖ) : Function.Surjective
      (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W) := by
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap T
    (Padic.coefficientExtensionRing l E (n + 1))
  let P := (ProEtale.finiteCoefficientModulePresheaf T.ProEt
    (finiteTateCoefficient l E n)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app P
  have : IsIso η := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify (ProEt.topology T) P.presheaf)
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
        AddCommGrpCat.{u + 1})).obj M).property
  exact (ConcreteCategory.bijective_of_isIso
    ((PresheafOfModules.evaluation _ W).map η)).2

omit hInvert in
private theorem adicUnit_map
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
    (f : M ⟶ N) (W : T.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E (n + 1))).functor.map f).val.app W
        (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W x) =
      sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
        N W (f.hom.app W x) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap T
      (Padic.coefficientExtensionRing l E (n + 1)))).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
          (finiteTateCoefficient l E n)).map f.hom)
  exact (congrArg (fun k ↦ k.app W x) h).symm

omit hInvert in
private theorem adicFixedTensor_map
    (M N L : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
    (f : M ⟶ N) (W : T.ProEtᵒᵖ) (x : M.obj.obj W) (y : L.obj.obj W) :
    ((tensorRight L).map f).hom.app W
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M L).app W
            (x ⊗ₜ[finiteTateCoefficient l E n] y)) =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) N L).app W
          (f.hom.app W x ⊗ₜ[finiteTateCoefficient l E n] y) := by
  have h := Functor.LaxMonoidal.μ_natural_left
    (sheafToPresheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) f L
  exact (congrArg (fun k ↦ k.app W (x ⊗ₜ[finiteTateCoefficient l E n] y)) h).symm

/-- Intrinsic and fixed-coefficient tensor-by-line functors agree on every local pure
tensor. The scalar-unit sections specify the realization map uniquely.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: both tensor constructions sheafify the same balanced tensors. Send the scalar-unit
section of m tensor y to the scalar-unit section of m tensor y in the fixed tensor.This
 respects locally constant coefficients and restrictions. Such sections locally
generate, giving uniqueness and an inverse. -/
theorem adicPurityFiniteTensorRealization_existsUnique (d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        adicPurityFiniteSheafTwist l E n T d ≅
      tensorRight (finiteTateProSheaf l E n T d) ⋙
        (sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor,
      ∀ (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
        (W : T.ProEtᵒᵖ) (x : M.obj.obj W)
        (y : (finiteCoefficientTwist l E T n (d : ℤ)).val.obj W),
        (e.hom.app M).val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W
            (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W x) y) =
        sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
          (M ⊗ finiteTateProSheaf l E n T d) W
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M
              (finiteTateProSheaf l E n T d)).app W (x ⊗ₜ[finiteTateCoefficient l E n] y)) := by
  choose e he using adicPurityFiniteTensor_component l E n T d
  let c : (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        adicPurityFiniteSheafTwist l E n T d ≅
      tensorRight (finiteTateProSheaf l E n T d) ⋙
        (sfIntrinsicModuleEquivalence T
          (Padic.coefficientExtensionRing l E (n + 1))).functor :=
    NatIso.ofComponents e (by
      intro M N f
      apply adicTensor_ext T
      intro W x y
      obtain ⟨x, rfl⟩ := adicUnit_surjective l E n T M W x
      change (e N).hom.val.app W
          (((adicPurityFiniteSheafTwist l E n T d).map
            ((sfIntrinsicModuleEquivalence T
              (Padic.coefficientExtensionRing l E (n + 1))).functor.map f)).val.app W
                (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ W
                  (sfIntrinsicRealizationUnit T
                    (Padic.coefficientExtensionRing l E (n + 1)) M W x) y)) =
        ((sfIntrinsicModuleEquivalence T
          (Padic.coefficientExtensionRing l E (n + 1))).functor.map
            ((tensorRight (finiteTateProSheaf l E n T d)).map f)).val.app W
              ((e M).hom.val.app W
                (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} _ _ W
                (sfIntrinsicRealizationUnit T
                  (Padic.coefficientExtensionRing l E (n + 1)) M W x) y))
      let F := (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing l E (n + 1))).functor
      let L := finiteCoefficientTwist l E T n (d : ℤ)
      let Lf := finiteTateProSheaf l E n T d
      let η := sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
      let μ := Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
      have hm := adicTensor_map T (R := integralCoefficientCommRingSheaf l E T n)
        (F.obj M) (F.obj N) L (F.map f) W (η M W x) y
      have hu := adicUnit_map l E n T M N f W x
      have hv := adicUnit_map l E n T (M ⊗ Lf) (N ⊗ Lf)
        ((tensorRight Lf).map f) W ((μ M Lf).app W (x ⊗ₜ[finiteTateCoefficient l E n] y))
      have ht := adicFixedTensor_map l E n T M N Lf f W x y
      have hh := congrArg (η (N ⊗ Lf) W) ht
      exact (congrArg ((e N).hom.val.app W) hm).trans
        ((congrArg (fun z ↦ (e N).hom.val.app W
          (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (A := integralCoefficientCommRingSheaf l E T n) (F.obj N) L W z y)) hu).trans
          ((he N W (f.hom.app W x) y).trans
            (hh.symm.trans (hv.symm.trans
              (congrArg ((F.map ((tensorRight Lf).map f)).val.app W)
                (he M W x y).symm))))))
  refine ⟨c, he, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply adicTensor_ext T
  intro W x y
  obtain ⟨x, rfl⟩ := adicUnit_surjective l E n T M W x
  exact (hc' M W x y).trans (he M W x y).symm

/-- The finite ordinary tensor realization with its scalar-unit normalization.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityFiniteTensorRealization (d : ℕ) :=
  (adicPurityFiniteTensorRealization_existsUnique l E n T d).exists.choose

/-- The ordinary intrinsic tensor realization preserves zero arrows.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: realization is additive and tensoring with the finite line is additive. Their
composite therefore sends the zero linear map to the zero linear map, on every section. -/
theorem adicPurityFiniteTensorComposite_zero (d : ℕ) :
    ((sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      adicPurityFiniteSheafTwist l E n T d).PreservesZeroMorphisms := by
  let : (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E (n + 1))).functor.Additive := by
    change (ProEtale.finiteCoefficientIntrinsicRealization T
      (Padic.coefficientExtensionRing l E (n + 1))).Additive
    infer_instance
  let : (adicPurityFiniteSheafTwist l E n T d).Additive :=
    (adicPurityFiniteSheafTwist_exact l E n T d).1
  constructor
  intro M N
  change (adicPurityFiniteSheafTwist l E n T d).map
    ((sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E (n + 1))).functor.map (0 : M ⟶ N)) = 0
  rw [Functor.map_zero, Functor.map_zero]

attribute [instance] adicPurityFiniteTensorComposite_zero

end TwistReduction
end WeilConjectures
