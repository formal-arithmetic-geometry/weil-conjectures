/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! Ambient comparison required by condensed kernel-transform composition.

This is the compact-support base-change, projection-formula, tensor-coherence and
compact-support-composition calculation on the triple fibre product.

The remaining proof is the full six-functor coherence calculation described by the
source paragraph; it is split from the bounded restriction and Fourier specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Comparison of the two kernel functors after restricting their input to bounded
constructible complexes, with bounded constructible kernels. -/
theorem condensedKernelTransform_comp_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (p : ℕ) [Fact p.Prime]
    (hΛ : ∃ (l : ℕ) (_hl : Fact l.Prime), l ≠ p ∧ ((∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} l))))
    (hp : IsUnit (p : MonObj.Γ Λ))
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    {S V V' V'' : Scheme.{u}}
    [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [V'.Over (Spec (.of k))] [V''.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (V' ↘ Spec (.of k))]
    [QuasiCompact (V' ↘ Spec (.of k))] [IsSeparated (V' ↘ Spec (.of k))]
    [LocallyOfFiniteType (V'' ↘ Spec (.of k))]
    [QuasiCompact (V'' ↘ Spec (.of k))] [IsSeparated (V'' ↘ Spec (.of k))]
    (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)
    (c₁₂ : Compactification (pullback.snd π π'))
    (c₂₃ : Compactification (pullback.snd π' π''))
    (c₁₃ : Compactification (pullback.snd π π''))
    (c₁₃conv : Compactification (pullback.tripleProj₁₃ π π' π''))
    (𝒦 : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π π'))
      Ab.{u + 1}) (condensedRingObj Λ (pullback π π'))))
    (𝒦' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π' π''))
      Ab.{u + 1}) (condensedRingObj Λ (pullback π' π''))))
    (h𝒦 : boundedConstructible (condensedRingObj Λ (pullback π π')) 𝒦)
    (h𝒦' : boundedConstructible (condensedRingObj Λ (pullback π' π'')) 𝒦')
    (a b : ℤ) :
    Nonempty (
      (boundedConstructible (condensedRingObj Λ V)).ι ⋙
      (((upperStar Λ (pullback.fst π π')).leftDerivedFunctor ⋙ tensorRight 𝒦 ⋙
        rightDerivedLowerShriekOfCompactification Λ c₁₂ ⋙ shiftFunctor _ a) ⋙
      ((upperStar Λ (pullback.fst π' π'')).leftDerivedFunctor ⋙ tensorRight 𝒦' ⋙
        rightDerivedLowerShriekOfCompactification Λ c₂₃ ⋙ shiftFunctor _ b)) ≅
      (boundedConstructible (condensedRingObj Λ V)).ι ⋙
      (upperStar Λ (pullback.fst π π'')).leftDerivedFunctor ⋙
        tensorRight ((rightDerivedLowerShriekOfCompactification Λ c₁₃conv).obj
          ((tensorRight ((upperStar Λ
            (pullback.snd (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
              𝒦')).obj
            ((upperStar Λ
              (pullback.fst (pullback.snd π π') (pullback.fst π' π''))).leftDerivedFunctor.obj
              𝒦))) ⋙
        rightDerivedLowerShriekOfCompactification Λ c₁₃ ⋙ shiftFunctor _ (a + b)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
