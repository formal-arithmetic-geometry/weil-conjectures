/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedUnderivedData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Laws for the normalized native ringed total comparison

Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

/-- The signed summand and bifunctor naturality laws for the canonical total map.
Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).

Proof: expand the generic `mapBifunctorComparison` and the total-complex flip
isomorphism.  The former gives naturality and the latter gives the Koszul scalar
on each homogeneous summand; the normalized underived comparison identifies the
component with `U.underived`. -/
theorem native_weil_tensor_ringed_chain_laws
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (sign : ∀ (_p _q : ℤ)
      {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z), Y ⟶ Z)
    (hsign : ∀ (_p _q : ℤ)
      {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z),
      sign _p _q _f =
        letI : AddCommGroup (Y ⟶ Z) :=
          @Preadditive.homGroup
            (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
            _ inferInstance Y Z
        ZSMul.zsmul ((_p * _q).negOnePow : ℤ) _f)
    (τ : (Functor.postcompose₂.obj b.native.functor).obj T ⟶
      (((Functor.whiskeringLeft₂
        (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).obj b.native.functor).obj
          b.native.functor).obj
        (MonoidalCategory.curriedTensor
          (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip)
    (hτ : ∀ P Q : ProEtaleWeilSheaf k₀ l X,
      (τ.app P).app Q = (U.underived P Q).hom)
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
            (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hchain : ∀ P Q,
      (chain P Q).hom =
        (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q ≫
          (HomologicalComplex.mapBifunctorFlipIso
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
            (MonoidalCategory.curriedTensor
              (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)) (.up ℤ)).hom)) :
    (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
      b.native.functor.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) ≫
          (chain P Q).hom.f n =
        sign p q ((U.underived (P.X p) (Q.X q)).hom ≫
          RingedForgetTensorTransposition.tensorSummand b.J b.R
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)) ∧
      (∀ (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (b.native.functor.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
          (chain P Q).hom ≫
            (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
              (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
                ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
