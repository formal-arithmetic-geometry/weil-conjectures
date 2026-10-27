/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W8
-/
module

public import Sheaf.Paper.NativeWeilTensorRingedUnderivedData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Total-complex data for normalized native ringed tensor comparisons

This module records the total comparison, its homogeneous summand formula, and
naturality.  The scalar sign is a parameter so this interface can be used with
the item module's specified normalization.
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

structure NativeWeilRingedTensorChainData
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (sign : ∀ (_p _q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z), Y ⟶ Z) where
  chain (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q T) ≅
      (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
          (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
  summand (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    b.native.functor.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) ≫
        (chain P Q).hom.f n =
      sign p q ((U.underived (P.X p) (Q.X q)).hom ≫
        RingedForgetTensorTransposition.tensorSummand b.J b.R
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)
  naturality (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (f : P ⟶ P') (g : Q ⟶ Q') :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
      (chain P Q).hom ≫
        (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
          (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))

/-- The total comparison, summand equation, and naturality.
Source: Stacks 06YN and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data). -/
theorem native_weil_tensor_ringed_chain_data
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (sign : ∀ (_p _q : ℤ)
      {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (_f : Y ⟶ Z), Y ⟶ Z) :
    Nonempty (NativeWeilRingedTensorChainData b T adj U sign) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
