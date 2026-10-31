/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefFiniteHomSiteDescentData
import all WeilConjectures.AlgebraicGeometry.FiniteHomOrdinaryRestrictionChain

/-! # The normalized site chain tensorator on total generators -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local instance] ProEtale.finiteCoefficientIntrinsicMonoidal
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- A pure tensor in a specified total-degree summand on the etale site.
Source: Stacks 06YN (blueprint: lem-coef-finite-hom-site-chain-generators). -/
def finiteHomEtaleTotalGenerator (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    (((finiteHomCochainTensorGeneral _).obj (P, Q)).X k).obj.obj (op U) :=
  (HomologicalComplex.ιTensorObj P Q p q k hpq).hom.app (op U)
    (ProEtale.finiteCoefficientEtalePure X
      (Padic.coefficientExtensionRing l E (n + 1)) (P.X p) (Q.X q) U x y)

private theorem intrinsicTotalGenerator_eq (A : Type u) [CommRing A] [Finite A]
    (P Q : CochainComplex (Scheme.proEtaleRingModules X
      (Scheme.proEtaleConstantRing X A)) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
      (Scheme.proEtaleConstantRing X A) P Q p q k hpq U x y =
    (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ)
      p q k hpq).val.app U
      (ProEtale.finiteCoefficientIntrinsicPure X A (P.X p) (Q.X q) U x y) := by
  unfold coefficientTensorGenerator ProEtale.finiteCoefficientIntrinsicPure
  rw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  rfl

private theorem sections_of_comp_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N L K : SheafOfModules.{u + 1} R}
    {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ L} {i : L ⟶ K}
    (w : f ≫ g = h ≫ i) (U : Cᵒᵖ) (x : M.val.obj U) :
    g.val.app U (f.val.app U x) = i.val.app U (h.val.app U x) := by
  have hw := congrArg (fun t ↦ t.val.app U x) w
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] using hw

private theorem generator_of_equations (A : Type u) [CommRing A] [Finite A]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) [G.Additive]
    (s : ∀ (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (U : X.Etale),
      M.obj.obj (op U) → (G.obj M).val.obj (op (X.toProEt.obj U)))
    (hs : ∀ {M N} (f : M ⟶ N) (U : X.Etale) (x : M.obj.obj (op U)),
      (G.map f).val.app (op (X.toProEt.obj U)) (s M U x) =
        s N U (f.hom.app (op U) x))
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (he : ∀ M N U x y,
      (e.hom.app (M, N)).val.app (op (X.toProEt.obj U))
        (s (M ⊗ N) U (ProEtale.finiteCoefficientEtalePure X A M N U x y)) =
      ProEtale.finiteCoefficientIntrinsicPure X A (G.obj M) (G.obj N)
        (op (X.toProEt.obj U)) (s M U x) (s N U y))
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q)
    (ha : FiniteCoefficientTotalComparison.normalizedTensorEquation G e P Q a)
    (p q k : ℤ) (hpq : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    (a.hom.f k).val.app (op (X.toProEt.obj U))
      (s ((HomologicalComplex.tensorObj P Q).X k) U
        ((HomologicalComplex.ιTensorObj P Q p q k hpq).hom.app (op U)
          (ProEtale.finiteCoefficientEtalePure X A (P.X p) (Q.X q) U x y))) =
    coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
      (Scheme.proEtaleConstantRing X A)
      ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq (op (X.toProEt.obj U))
      (s (P.X p) U x) (s (Q.X q) U y) := by
  have hc := sections_of_comp_eq (ha p q k hpq) (op (X.toProEt.obj U))
    (s (P.X p ⊗ Q.X q) U
      (ProEtale.finiteCoefficientEtalePure X A (P.X p) (Q.X q) U x y))
  erw [hs, he] at hc
  erw [intrinsicTotalGenerator_eq]
  exact hc

private theorem comparisonSection_naturality (A : Type u) [CommRing A]
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (U : X.Etale) (x : M.obj.obj (op U)) :
    ((ProEtale.finiteCoefficientIntrinsicComparison X A).map f).val.app
      (op (X.toProEt.obj U)) (ProEtale.finiteCoefficientComparisonSection X A M U x) =
    ProEtale.finiteCoefficientComparisonSection X A N U (f.hom.app (op U) x) := by
  exact nuSection_naturalityGeneral X A f U x

private theorem chain_generator_general (A : Type u) [CommRing A] [Finite A]
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    (a : FiniteCoefficientTotalComparison.ChainIso
      (ProEtale.finiteCoefficientIntrinsicComparison X A) P Q)
    (ha : ProEtale.FiniteCoefficientChainTensorNormalization X A P Q a)
    (p q k : ℤ) (hpq : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    (a.hom.f k).val.app (op (X.toProEt.obj U))
      (ProEtale.finiteCoefficientComparisonSection X A
        ((HomologicalComplex.tensorObj P Q).X k) U
        ((HomologicalComplex.ιTensorObj P Q p q k hpq).hom.app (op U)
          (ProEtale.finiteCoefficientEtalePure X A (P.X p) (Q.X q) U x y))) =
    coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
      (Scheme.proEtaleConstantRing X A)
      (((ProEtale.finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((ProEtale.finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex
        (.up ℤ)).obj Q) p q k hpq (op (X.toProEt.obj U))
      (ProEtale.finiteCoefficientComparisonSection X A (P.X p) U x)
      (ProEtale.finiteCoefficientComparisonSection X A (Q.X q) U y) := by
  obtain ⟨e, he, hchain⟩ := ha
  exact generator_of_equations X A (ProEtale.finiteCoefficientIntrinsicComparison X A)
    (ProEtale.finiteCoefficientComparisonSection X A)
    (comparisonSection_naturality X A) e he P Q a hchain p q k hpq U x y

/-- The site comparison preserves every pure total-complex generator.
Source: Stacks 00YV, 03EK, 06YN; blueprint thm-coef-finite-hom
(blueprint: lem-coef-finite-hom-site-chain-generators).
Proof: write the generator as the total summand inclusion of an ordinary pure
tensor. Naturality of the inverse-image section moves the inclusion outside the
section. The defining summand equation of the chain tensorator and the ordinary
pure-tensor normalization then give the intrinsic summand inclusion of the two
inverse-image sections, which is precisely the intrinsic total generator. -/
theorem finiteHomNuChainTensor_generator (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    ((finiteHomNuChainTensor l E X n P Q).hom.f k).val.app (op (X.toProEt.obj U))
      (finiteHomNuSection l E X n
        (((finiteHomCochainTensorGeneral _).obj (P, Q)).X k) U
        (finiteHomEtaleTotalGenerator l E X n P Q p q k hpq U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((finiteHomNuComplex l E X n).obj P) ((finiteHomNuComplex l E X n).obj Q)
        p q k hpq (op (X.toProEt.obj U))
        (finiteHomNuSection l E X n (P.X p) U x)
        (finiteHomNuSection l E X n (Q.X q) U y) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have hnorm : FiniteHomNuChainTensorNormalization l E X n P Q
      (finiteHomNuChainTensor l E X n P Q) :=
    (ProEtale.finiteCoefficientIntrinsicChainTensor_existsUnique X
      (Padic.coefficientExtensionRing l E (n + 1)) P Q).choose_spec.1
  exact chain_generator_general X (Padic.coefficientExtensionRing l E (n + 1))
    P Q (finiteHomNuChainTensor l E X n P Q) hnorm p q k hpq U x y

end WeilConjectures
