/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients

/-! # A normalized isomorphism between strict root systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem padic_map_smul_target {l : ℕ} [Fact l.Prime]
    {M N : Type (u + 1)} [AddCommGroup M] [Module (ULift.{u + 1} ℤ_[l]) M]
    [AddCommGroup N] [Module (ULift.{u + 1} ℤ_[l]) N]
    (n : ℕ) (hN : ∀ y : N, (l ^ n) • y = 0) (f : M →+ N)
    (r : ULift.{u + 1} ℤ_[l]) (x : M) : f (r • x) = r • f x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (r.down.appr_spec n)
  have hr : r - (r.down.appr n : ULift.{u + 1} ℤ_[l]) =
      (ULift.up a) * (l : ULift.{u + 1} ℤ_[l]) ^ n := by
    apply ULift.ext
    exact ha.symm
  have split (y : M) :
      r • y = (l ^ n) • (ULift.up a • y) + r.down.appr n • y := by
    conv_lhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
    rw [add_smul, mul_comm (ULift.up a), mul_smul]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [split, map_add, map_nsmul, hN, zero_add, map_nsmul]
  conv_rhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
  rw [add_smul, mul_comm (ULift.up a), mul_smul]
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hN, zero_add]

private theorem restriction_killed (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : ((r.F.obj M).obj (op n)).obj.obj U) :
    (l ^ (n + 1)) • x = 0 := by
  have h := r.scalars M n U (l ^ (n + 1)) x
  have hz : PadicInt.toZModPow (n + 1) ((l : ℤ_[l]) ^ (n + 1)) = 0 := by
    rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  change ((l : ULift.{u + 1} ℤ_[l]) ^ (n + 1)) • x =
    ((PadicInt.toZModPow (n + 1)) ((l : ℤ_[l]) ^ (n + 1))).val • x at h
  rw [hz, ZMod.val_zero, zero_nsmul] at h
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h

private def liftToRestriction (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (n : ℕ)
    (Q : DiagonalMod l T)
    (f : (diagonalForget l T).obj Q ⟶
      (diagonalForget l T).obj ((r.F.obj M).obj (op n))) :
    Q ⟶ (r.F.obj M).obj (op n) :=
  ObjectProperty.homMk
    { app U := by
        let g : Q.obj.obj U →+ (((r.F.obj M).obj (op n)).obj.obj U) := (f.hom.app U).hom
        exact ModuleCat.ofHom
          { toFun := g
            map_add' := g.map_add
            map_smul' z x := padic_map_smul_target (n + 1)
              (restriction_killed l T r M n U) g z x }
      naturality U V g := by
        apply (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
          AddCommGrpCat.{u + 1}).map_injective
        exact f.hom.naturality g }

/-- Lift the prescribed additive root identification to the strict Z_l-module systems.
Source: diagonal tower trace proof (1), root-system identification, and the scalar
restriction convention in the geometric classes construction.
(blueprint: lem-sfb-diagonal-trace-normalized-root-iso).

Proof: the restricted target at level n is killed by l^(n+1). An additive map into
such a target is Z_l-linear: approximate a scalar by an integer modulo l^(n+1)
and the error term acts by zero. Apply this to roots.hom followed by
k.lineForget.inv. Faithfulness proves naturality, and reflection of isomorphisms
by forgetting scalars makes the resulting strict-system map invertible. -/
theorem diagonalTrace_normalizedRootIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) :
    ∃ e : H ≅ r.F.obj (lineModule l (ULift.{u} (Padic l)) c),
      Functor.whiskerRight e.hom (diagonalForget l T) =
        roots.hom ≫ k.lineForget.inv := by
  let tau := roots.hom ≫ k.lineForget.inv
  let h : H ⟶ r.F.obj (lineModule l (ULift.{u} (Padic l)) c) :=
    { app n := liftToRestriction l T r _ n.unop (H.obj n) (tau.app n)
      naturality n m f := by
        ext U x
        exact congrArg (fun a ↦ a.hom.app U x) (tau.naturality f) }
  have hh : Functor.whiskerRight h (diagonalForget l T) = tau := by
    ext n U x
    rfl
  have : (diagonalForget l T).ReflectsIsomorphisms := by
    unfold diagonalForget
    infer_instance
  have (n : ℕᵒᵖ) : IsIso (h.app n) := by
    have he : (diagonalForget l T).map (h.app n) = tau.app n :=
      NatTrans.congr_app hh n
    have : IsIso ((diagonalForget l T).map (h.app n)) := by
      rw [he]
      dsimp only [tau, NatTrans.comp_app]
      infer_instance
    exact isIso_of_reflects_iso _ (diagonalForget l T)
  have : IsIso h := NatIso.isIso_of_isIso_app h
  exact ⟨asIso h, hh⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
