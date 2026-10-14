/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Picard
import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv
import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion
/-!
# The canonical proper-curve Picard torsion interface

This forward-ports the interface of upstream `Curve/Jacobian.lean` to the pinned
library, which does not yet contain that module. The cokernel calculation is private;
callers use `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- The prime-to-characteristic Picard cokernel for a proper smooth curve.
Source: blueprint `lem-sc-pic-proper-ntorsion`, final cokernel calculation.
(blueprint: lem-sc-pic-proper-ntorsion-coker)

Proof: install f as the structure morphism. Connectedness and smoothness give
irreducibility, and dimension one gives smooth relative dimension one. The degree
homomorphism d is surjective by `Scheme.surjective_picDegreeHom`, and its kernel has
underlying set `f.picZero` by `Scheme.coe_ker_picDegreeHom`. Compose d with integer
cast into ZMod n. This composite is surjective, and its kernel is the nth-power image:
an nth power has degree zero modulo n; conversely, if degree(L) = n*z, choose M of
degree z. Then L / M^n has degree zero, so divisibility supplies R with
R^n = L / M^n. The class R*M has nth power L. The first isomorphism theorem gives
the required cokernel. No product decomposition or choice of a splitting is needed. -/
private theorem picQuotient
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n)) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace' f
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  -- Only the surjectivity part of the degree splitting is needed for the cokernel.
  let d := Scheme.picDegreeHom k C
  have hd : Function.Surjective d := Scheme.surjective_picDegreeHom
  let φ : C.Pic →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative.comp d
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
    obtain ⟨L, hL⟩ := hd (Multiplicative.ofAdd z)
    refine ⟨L, ?_⟩
    change Multiplicative.ofAdd ((d L).toAdd : ZMod n) = a
    rw [hL]
    exact congrArg Multiplicative.ofAdd hz
  have hker : (powMonoidHom n : C.Pic →* C.Pic).range = φ.ker := by
    ext L
    constructor
    · rintro ⟨M, rfl⟩
      change φ (M ^ n) = 1
      rw [map_pow]
      change Multiplicative.ofAdd (n • Multiplicative.toAdd (φ M)) = 1
      simp
    · intro hL
      have hz : (((d L).toAdd : ℤ) : ZMod n) = 0 := by
        exact congrArg Multiplicative.toAdd hL
      obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      obtain ⟨M, hM⟩ := hd (Multiplicative.ofAdd z)
      have hdeg : d (L / M ^ n) = 1 := by
        rw [map_div, map_pow, hM]
        have hpow : Multiplicative.ofAdd z ^ n = d L := by
          apply Multiplicative.toAdd.injective
          simpa [nsmul_eq_mul, mul_comm] using hz.symm
        simp [hpow]
      have hzero : L / M ^ n ∈ f.picZero := by
        have hker : (d.ker : Set C.Pic) = f.picZero := Scheme.coe_ker_picDegreeHom
        rw [← hker]
        exact hdeg
      obtain ⟨R, _, hR⟩ := f.pic_proper_ntorsion_div n _hn (L / M ^ n) hzero
      refine ⟨R * M, ?_⟩
      change (R * M) ^ n = L
      rw [mul_pow, hR, div_mul_cancel]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
/-- The canonical upstream Picard torsion, quotient and divisibility interface.
Source: `WeilConjectures/AlgebraicGeometry/Curve/Jacobian.lean`,
`Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` in the upstream PR snapshot.
(blueprint: lem-sc-pic-proper-ntorsion-coker)

The pinned source library predates that module. Use the existing geometric component
proofs, transport the power-map kernel to additive torsion, and transport the quotient
from multiplicative to additive notation. The degree-zero kernel is `picardZero`.
The quotient calculation is the degree-modulo-n first isomorphism theorem above. -/
theorem Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [ConnectedSpace C]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (Additive C.Pic) n ≃+
        (Fin (2 * (C ↘ Spec (.of k)).genus) → ZMod n)) ∧
      Nonempty (Additive C.Pic ⧸ (zsmulAddGroupHom (α := Additive C.Pic) n).range ≃+
        ZMod n) ∧
      Function.Surjective fun L : picardZero k C ↦ L ^ n := by
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have hdim : topologicalKrullDim C = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (C ↘ Spec (.of k)) 1
  have : IsConnectedCurve (C ↘ Spec (.of k)) :=
    { krullDim_le_one := hdim.le
      connectedSpace := inferInstance
      krullDim_eq_one := hdim }
  obtain ⟨eT⟩ := (C ↘ Spec (.of k)).pic_proper_ntorsion_torsion n hn
  obtain ⟨eQ⟩ := picQuotient (C ↘ Spec (.of k)) n hn
  let eKer : AddSubgroup.torsionBy (Additive C.Pic) n ≃+
      Additive (powMonoidHom n : C.Pic →* C.Pic).ker :=
    { toFun x := .ofMul ⟨x.val.toMul, congrArg Additive.toMul
        (AddSubgroup.torsionBy.nsmul_iff.mp x.property)⟩
      invFun x := ⟨.ofMul x.toMul.val, AddSubgroup.torsionBy.nsmul_iff.mpr
        (congrArg Additive.ofMul x.toMul.property)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
  have hRange : (zsmulAddGroupHom (α := Additive C.Pic) (n : ℤ)).range =
      (powMonoidHom n : C.Pic →* C.Pic).range.toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.toMul, by simp⟩
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, ?_⟩
      simpa using congrArg Additive.ofMul hy
  let eQuot : (Additive C.Pic ⧸
      (powMonoidHom n : C.Pic →* C.Pic).range.toAddSubgroup) ≃+
      Additive (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine ⟨⟨eKer.trans eT.toAdditive⟩,
    ⟨(QuotientAddGroup.quotientAddEquivOfEq hRange).trans
      (eQuot.trans eQ.toAdditive)⟩, ?_⟩
  intro L
  obtain ⟨M, hM, hp⟩ := (C ↘ Spec (.of k)).pic_proper_ntorsion_div n hn L (by
    rw [← Scheme.coe_ker_picDegreeHom]
    exact L.property)
  refine ⟨⟨M, ?_⟩, Subtype.ext hp⟩
  change M ∈ (picardZero k C : Set C.Pic)
  rw [Scheme.coe_ker_picDegreeHom]
  exact hM

end AlgebraicGeometry
