/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.TensorFreeFrameCoordinates

/-!
# Natural coordinates from a specified tensor-pullback frame

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-linear-free-frame-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem frobenius_expansion
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (n p : ℕ) (e : M ≃ₗ[R] (Fin n → R)) (f : M →+ M)
    (hf : ∀ (c : R) (m : M), f (c • m) = c ^ p • f m) (m : M) (i : Fin n) :
    e (f m) i = ∑ j, e (f (e.symm (Pi.single j 1))) i * (e m j) ^ p := by
  classical
  have hm : ∑ j, (e m j) • e.symm (Pi.single j 1) = m := by
    apply e.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← hm, map_sum, map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

set_option maxHeartbeats 600000 in
-- Checking the tensor-section coercions requires a larger kernel budget.
/-- A specified finite free frame gives a natural Frobenius matrix on the etale slice.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb,
first paragraph (the matrix description after choosing a frame).
(blueprint: lem-fd-frobenius-linear-free-frame-coordinates).

Proof: for h:W -> V, use the inverse unit-normalized tensor-pullback composition
comparison, the tensor-to-abstract pullback comparison, the pullback of the given
frame, and the free-pullback comparison to identify E_W with the free module on W.
Apply global sections and reindex ULift (Fin n) by Fin n. Naturality of the
adjunction units and their composition comparisons says that these identifications
carry the restricted frame sections and dual coordinate maps to those on W. In
particular they commute with restriction of every section over V, including h=id.
Let a_ij be coordinate i of F applied to frame section j over V. Naturality of F
shows that its value on the restricted frame is obtained by restricting these
coefficients. Every section on W is the finite sum of its coefficients times the
frame sections; additivity and F(cm)=c^p F(m) then give the displayed matrix formula.
No affineness, characteristic assumption, or invertibility of F is needed for this
frame comparison. Empty test objects and rank zero satisfy the same identities.
-/
theorem frobenius_linear_free_frame_coordinates
    (p : ℕ)
    (S : Scheme.{u})
    (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (V : S.Etale) (n : ℕ)
    (α : (Modules.tensorPullback V.hom).obj E ≅
      SheafOfModules.free (R := V.left.ringCatSheaf) (ULift.{u} (Fin n))) :
  ∃ (e : ∀ (W : S.Etale), (W ⟶ V) →
        Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃+ (Fin n → Γ(W.left, ⊤)))
      (a : Fin n → Fin n → Γ(V.left, ⊤)),
      (∀ (W : S.Etale) (h : W ⟶ V)
        (m : Γ((Modules.tensorPullback V.hom).obj E, ⊤)) (i : Fin n),
        e W h ((Modules.etaleTensorSectionsSheaf E).obj.map h.op m) i =
          h.left.appTop (e V (𝟙 V) m i)) ∧
      (∀ (W : S.Etale) (h : W ⟶ V)
        (m : Γ((Modules.tensorPullback W.hom).obj E, ⊤)) (i : Fin n),
        e W h (F.hom.app (op W) m) i =
          ∑ j, h.left.appTop (a i j) * (e W h m j) ^ p) := by
  classical
  obtain ⟨e, henat⟩ := exists_natural_tensor_free_frame_coordinates S E V n α
  let v : Fin n → Γ((Modules.tensorPullback V.hom).obj E, ⊤) :=
    fun j ↦ (e V (𝟙 V)).symm (Pi.single j 1)
  let a : Fin n → Fin n → Γ(V.left, ⊤) :=
    fun i j ↦ e V (𝟙 V) (F.hom.app (op V) (v j)) i
  refine ⟨fun W h ↦ (e W h).toAddEquiv, a, henat, ?_⟩
  intro W h m i
  let w : Fin n → Γ((Modules.tensorPullback W.hom).obj E, ⊤) :=
    fun j ↦ (e W h).symm (Pi.single j 1)
  have hv (j : Fin n) : (Modules.etaleTensorSectionsSheaf E).obj.map h.op (v j) = w j := by
    apply (e W h).injective
    funext k
    rw [henat]
    simp only [v, w, LinearEquiv.apply_symm_apply, Pi.single_apply]
    split_ifs <;> simp
  have hwF (j : Fin n) :
      e W h (F.hom.app (op W) (w j)) i = h.left.appTop (a i j) := by
    have hn := congrArg (fun f ↦ f (v j)) (F.hom.naturality h.op)
    simp only [AddCommGrpCat.comp_apply, hv] at hn
    rw [hn, henat]
  let FW : Γ((Modules.tensorPullback W.hom).obj E, ⊤) →+
      Γ((Modules.tensorPullback W.hom).obj E, ⊤) := (F.hom.app (op W)).hom
  have hs : ∀ (c : Γ(W.left, ⊤))
      (s : Γ((Modules.tensorPullback W.hom).obj E, ⊤)),
      FW (c • s) = c ^ p • FW s := by
    intro c s
    exact hF W c s
  change e W h (FW m) i = ∑ j, h.left.appTop (a i j) * (e W h m j) ^ p
  rw [frobenius_expansion n p (e W h) FW hs]
  apply Finset.sum_congr rfl
  intro j _
  change e W h (F.hom.app (op W) (w j)) i * (e W h m j) ^ p = _
  rw [hwF]

end AlgebraicGeometry.Scheme
