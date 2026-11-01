/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceResidueRestriction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientIdentification
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceLineIdentification

/-! # Scalar restriction and coefficient cones at one site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
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

private def liftRestrictionCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶
      r.F.obj M ⋙ diagonalForget l T) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ r.F.obj M where
  app n := liftToRestriction l T r M n.unop Q (π.app n)
  naturality a b g := by
    ext U x
    exact congrArg (fun k ↦ k.hom.app U x) (π.naturality g)

private def transportRestrictionCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T) (H : ℕᵒᵖ ⥤ DiagonalAb T)
    (e : r.F.obj M ⋙ diagonalForget l T ≅ H)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶ H) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ r.F.obj M :=
  liftRestrictionCone l T r M Q (π ≫ e.inv)

private theorem transportRestrictionCone_section (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T) (H : ℕᵒᵖ ⥤ DiagonalAb T)
    (e : r.F.obj M ⋙ diagonalForget l T ≅ H)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶ H)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : Q.obj.obj U) :
    (e.hom.app (op n)).hom.app U
      (((transportRestrictionCone l T r M Q H e π).app (op n)).hom.app U x) =
        (π.app (op n)).hom.app U x := by
  have h := congrArg (fun k ↦ k.hom.app U ((π.app (op n)).hom.app U x))
    (NatTrans.congr_app e.inv_hom_id (op n))
  exact h

private def coefficientCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj
      ((diagonalCompletedRestriction l T).obj
        (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))))) ⟶
    Scheme.purTwistZlTower T l ⋙
      sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  ((sheafCompose (Scheme.ProEt.topology T)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapCone
        (limit.cone (Scheme.purTwistZlTower T l))).π

private def rootCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj
      ((diagonalCompletedRestriction l T).obj (Scheme.purTwistZlModule T l))) ⟶
      roots l T := (limit.cone (roots l T)).π

-- The finite constructions do not use the derived Chern normalization.
set_option linter.unusedVariables false in
/-- The exact finite-coefficient restriction and its two normalized cones at one site.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
coefficient restriction and its coefficient-unit and Tate-line identifications.
(blueprint: lem-sfb-diagonal-trace-coefficient-restriction).

Proof: restrict each level action along the constant-section map from Z_l to
O_(ULift Q_l)/l^(n+1). Retain the additive section groups, all vertical restrictions,
all horizontal transitions, and all maps. The quotient maps commute with residues,
so these are Z_l-linear and define a functor on strict systems. The residue of z acts
as its representative natural number; this proves the prescribed scalar equation.
Kernels are sectionwise, and additive sheafification computes cokernels, so this
restriction preserves finite limits and colimits and is additive.
Identify the valuation-one subring of ULift Q_l with Z_l by the lifted identity.
Its quotients by l^(n+1) identify with Z/l^(n+1), compatibly with all quotient maps.
The resulting isomorphism of constant ring towers gives coefficientForget and sends
one to one. Extension along the same ring isomorphism has the tensor unitor as its
counit: on a pure tensor with scalar one it sends x tensor one to x. Compose this
with c.rootForget to obtain lineForget, with the required line_tensor equation.
Transport the actual completed ring projections through coefficientForget inverse,
and the actual root-limit projections through lineForget inverse. These maps are
Z_l-linear, commute with the quotient transitions, and give the two cones.
Cancelling the corresponding inverse isomorphisms proves coefficient_projection
and line_projection. These constructions include the first positive quotient and
empty sites; they impose no condition on a scheme morphism or on direct image. -/
theorem exists_diagonalTraceCoefficientRestriction (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (hc : c.Normalized l (ULift.{u} (Padic l))) :
    ∃ r : Restriction l (ULift.{u} (Padic l)) T,
      Nonempty (Coefficients l (ULift.{u} (Padic l)) T c r) := by
  obtain ⟨r⟩ := exists_diagonalTraceResidueRestriction l T
  obtain ⟨e, he⟩ := exists_diagonalTraceCoefficientIdentification l T r
  obtain ⟨f, hf⟩ := exists_diagonalTraceLineIdentification l T c r
  refine ⟨r, ⟨{
    coefficientForget := e
    coefficient_one := he
    lineForget := f
    line_tensor := hf
    coefficientProjection := transportRestrictionCone l T r _ _ _ e (coefficientCone l T)
    coefficient_projection := ?_
    lineProjection := transportRestrictionCone l T r _ _ _ f (rootCone l T)
    line_projection := ?_ }⟩⟩
  · intro n U x
    exact transportRestrictionCone_section l T r _ _ _ e (coefficientCone l T) n U x
  · intro n U x
    exact transportRestrictionCone_section l T r _ _ _ f (rootCone l T) n U x

end AlgebraicGeometry.ProEtale.DiagonalTrace
