/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueProjective
import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.NilpotentDerivedUpperBoundSupplement
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.NilpotentProjectiveModuleLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Idempotents

/-! # Detecting Tor amplitude of a finite-quotient constant model

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I)
(blueprint: lem-weil-pbc-finite-quotient-model-tor-amplitude).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem zero_of_nilpotent_reduction
    {B : Type t} [CommRing B] (J : Ideal B) (k : ℕ) (hk : J ^ k = ⊥)
    (N : ModuleCat.{t} B)
    (hN : IsZero ((ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj N)) : IsZero N := by
  have := ModuleCat.subsingleton_of_isZero hN
  let e := TensorProduct.quotTensorEquivQuotSMul N J
  let e' : (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj N ≃ₗ[B ⧸ J]
      (N ⧸ J • (⊤ : Submodule B N)) :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul a x }
  have : Subsingleton (N ⧸ J • (⊤ : Submodule B N)) := e'.symm.injective.subsingleton
  have htop : J • (⊤ : Submodule B N) = ⊤ := by
    apply top_unique
    intro x _
    exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  have hp (m : ℕ) : J ^ m • (⊤ : Submodule B N) = ⊤ := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Submodule.mul_smul, htop, ih]
  have hz : (⊤ : Submodule B N) = ⊥ := by rw [← hp k, hk, Submodule.bot_smul]
  have : Subsingleton N := ⟨fun x y ↦ by
    have hx : x = 0 := hz.le (Submodule.mem_top (x := x))
    have hy : y = 0 := hz.le (Submodule.mem_top (x := y))
    exact hx.trans hy.symm⟩
  exact ModuleCat.isZero_of_subsingleton N

end AlgebraicGeometry.Scheme
