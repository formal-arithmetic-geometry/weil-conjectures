/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.NativeFrobeniusRingedModel
public import Sheaf.Paper.NativeWeilClosedModels

/-! # The specified ordinary Hom comparison as a natural isomorphism

Source: the Hom comparison and naturality of the ordinary Frobenius ringed model.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Assemble precisely the model's ordinary Hom maps.
Source: native Frobenius ringed model, ordinary Hom naturality.
(blueprint: lem-sf-native-normalized-ordinary-hom).

Proof: apply NatIso.ofComponents to A.hom. Its naturality is exactly
A.hom_naturality, and the component equation is definitional. -/
theorem normalized_ordinary_hom
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X) :
    ∃ h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R)) ⋙ A.E.functor ≅
        (A.E.functor.op.prod A.E.functor) ⋙ Functor.uncurry.obj
          (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      ∀ M N, h.hom.app (op M, N) = (A.hom M N).hom := by
  exact ⟨NatIso.ofComponents (fun MN ↦ A.hom MN.1.unop MN.2)
    (fun fg ↦ A.hom_naturality fg.1.unop fg.2), fun _ _ ↦ rfl⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
