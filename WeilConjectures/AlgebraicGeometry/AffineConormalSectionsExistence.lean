/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.AffineIdealTensorSections
import Mathlib.LinearAlgebra.TensorProduct.Quotient

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The affine conormal linear equivalence and its compatibility with the adjunction unit
(Stacks, Tags 01R3, 01I9 and 00DF). -/
theorem affine_conormal_sections_existence {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
      ∀ (U : X.affineOpens) (R : Type v) [CommRing R]
        (r : R ≃+* Γ(X, U.1)) (I : Ideal R),
        I = RingHom.ker ((i.app U.1).hom.comp (r : R →+* Γ(X, U.1))) →
        ∃ e : LinearEquiv (r : R →+* Γ(X, U.1))
            (σ' := (r.symm : Γ(X, U.1) →+* R)) I.Cotangent
            Γ((pushforward i).obj ((tensorPullback i).obj i.ker.toModules), U.1),
          ∀ (a : I) (s : Γ(i.ker.toModules, U.1)),
            i.ker.toModulesι.app U.1 s = r (a : R) →
            e (I.toCotangent a) =
              ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).app U.1 s := by
  intro U R _ r I hI
  obtain ⟨c, hc⟩ := affine_ideal_tensor_sections i U R r I hI
  let t : (TensorProduct R I (R ⧸ I)) ≃ₗ[R] I.Cotangent :=
    TensorProduct.tensorQuotEquivQuotSMul I I
  refine ⟨t.symm.trans c, ?_⟩
  intro a s hs
  have ht : t (TensorProduct.tmul R a (1 : R ⧸ I)) = I.toCotangent a := by
    change TensorProduct.quotTensorEquivQuotSMul I I
      (TensorProduct.comm R I (R ⧸ I) (TensorProduct.tmul R a (1 : R ⧸ I))) = _
    rw [TensorProduct.comm_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rfl
  change c (t.symm (I.toCotangent a)) = _
  rw [← ht, t.symm_apply_apply]
  exact hc a s hs

end AlgebraicGeometry.Scheme.Modules
