/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineLimit
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineComplete
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstruction

/-! # Coherent formal modules on an affine scheme

Stacks Project, Tag 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Coherent formal modules on Spec A are finite modules over the I-adic completion.
The cones specify the underlying inverse limits and their maps, while the scalar equation
specifies the componentwise action of the completion. Index `op n` means level `n + 1`
(Stacks, Tag 087W). -/
theorem coherentFormalModules_affine (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ∃ E : CoherentFormalModule (Spec (CommRingCat.of A)) J ≌
      ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N),
    ∃ p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (E.functor.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A),
    (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))) ∧
    (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (E.functor.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (E.functor.obj F).obj))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (E.functor.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x) ∧
    Nonempty (E.inverse ⋙ ObjectProperty.ι (IsCoherentFormalModule J) ≅
      ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J) := by
  obtain ⟨L, p, hlimit, hnatural, hquotient, hscalar⟩ :=
    coherentFormalModules_affine_limit A I J hJ
  obtain ⟨ε⟩ := coherentFormalModules_affine_complete A I J hJ L p
    hlimit hnatural hscalar
  obtain ⟨η⟩ := coherentFormalModules_affine_reconstruction A I J hJ L p
    hnatural hquotient
  let Q := coherentFormalModules_affine_quotientFunctor A I J hJ
  let E := CategoryTheory.Equivalence.mk L Q η.symm ε
  refine ⟨E, p, hlimit, hnatural, hquotient, hscalar, ?_⟩
  exact ⟨Iso.refl _⟩

end AlgebraicGeometry
