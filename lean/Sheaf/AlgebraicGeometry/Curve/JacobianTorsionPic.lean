/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CurveGenus
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.Curve.PicardDecomposition
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny

/-!
# Jacobian divisibility, Picard torsion and degree modulo a positive integer

Source: blueprint, `sec-picard-framework/sk-cor-jacobian-torsion/`,
`det-cor-jacobian-torsion-pic.md` (blueprint: det-cor-jacobian-torsion-pic).

The group laws on rational points and on the Picard group are written multiplicatively.
The inclusion into the Picard group is characterized by the given Jacobian representation,
so the torsion equalities concern the actual inclusion and the quotient equivalence is
specified on representatives by degree. The geometric-integrality witness only makes the
existing `IsJacobian` interface available; it is supplied in the conclusion.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Over an algebraically closed field, the points of the Jacobian of a smooth proper
connected curve are divisible. Its inclusion into the Picard group identifies its scheme
and pointwise n-torsion with all Picard n-torsion, and degree identifies Pic modulo n with
integers modulo n, for every positive n, including multiples of the characteristic.

Source: blueprint, `sec-picard-framework/sk-cor-jacobian-torsion/`,
`det-cor-jacobian-torsion-pic.md` and its proof
(blueprint: det-cor-jacobian-torsion-pic).

Proof, following the five DAG steps:
1. Smoothness and connectedness over the algebraically closed field give geometric
integrality, allowing `IsJacobian`. By sk-thm-picard-main the group-compatible Jacobian
representation identifies its rational points with Pic-zero; the inclusion i below is
characterized by sending a point to its representing line-bundle class. By
lem-sc-pic-proper-decomposition degree is surjective with this subgroup as its kernel.
2. Apply lem-sc-isogeny-surjective to J: for every positive n and point y there is a
point x with x^n = y. This includes the case where the characteristic divides n.
3. By sk-def-av-mult-n the points of J[n] are exactly the points a of J with a^n = 1,
via its kernel inclusion. If L^n = 1 in Pic, then n times its integer degree is zero.
Since n is positive, its degree vanishes, so it belongs to the image of i. The converse
follows because i is a homomorphism. These give both displayed equalities of subsets.
4. Degree modulo n descends to the quotient by nth powers, since degree of M^n is
n times degree of M. It is surjective by surjectivity of integer degree.
5. If degree L = n*m, choose M of degree m. Then L*M^(-n) has degree zero, so lies
in the image of i and has an nth root B there by step 2. Thus L = (M*B)^n. This proves
injectivity on the quotient, giving the asserted group isomorphism with its displayed
value on every representative. No choice of a splitting of degree enters that map. -/
theorem Scheme.Hom.jacobian_torsion_pic
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f] :
    ∃ (_ : GeometricallyIntegral f),
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
        (r : (picardFunctorDegree f 0).obj.RepresentableBy J)
        (_hr : IsPicardZeroMul f r),
      ∃ i : (𝟙_ (Over (Spec (.of k))) ⟶ J) →* C.Pic,
        Function.Injective i ∧ Set.range i = f.picZero ∧
        (∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ J, ∃ h,
          r.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree f 0).toFunctor).app (.op (𝟙_ (Over (Spec (.of k)))))
              ⟨Scheme.Pic.map (pullback.fst f (𝟙_ (Over (Spec (.of k)))).hom) (i a), h⟩) = a) ∧
        (∀ (n : ℕ), 0 < n →
          Function.Surjective fun a : 𝟙_ (Over (Spec (.of k))) ⟶ J ↦ a ^ n) ∧
        ∀ (n : ℕ), 0 < n →
          (Set.range (fun a : 𝟙_ (Over (Spec (.of k))) ⟶ torsionSubgroupScheme J n ↦
            i (a ≫ torsionSubgroupScheme.ι J n)) =
              i '' {a : 𝟙_ (Over (Spec (.of k))) ⟶ J | a ^ n = 1}) ∧
          (i '' {a : 𝟙_ (Over (Spec (.of k))) ⟶ J | a ^ n = 1} =
            {L : C.Pic | L ^ n = 1}) ∧
          ∃ e : C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
              Multiplicative (ZMod n),
            ∀ L : C.Pic, e (QuotientGroup.mk L) =
              Multiplicative.ofAdd ((f.picDegree L : ℤ) : ZMod n) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace' f
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have hgeo : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton f
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := hgeo
  refine ⟨hgeo, ?_⟩
  intro J _ _ r hr
  obtain ⟨Φ, hΦ⟩ := exists_picardZero_equiv_picardFunctorDegree_zero (k := k) (X := C)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_isPicardZeroMul f r hr
    (T := 𝟙_ (Over (Spec (.of k))))
    (fun L : picardZero k C ↦
      Scheme.Pic.map (pullback.fst f (𝟙_ (Over (Spec (.of k)))).hom) L.val)
    (fun a b ↦ Scheme.Pic.map_mul _ a.val b.val) Φ hΦ
  let i : (𝟙_ (Over (Spec (.of k))) ⟶ J) →* C.Pic :=
    (picardZero k C).subtype.comp ψ.symm.toMonoidHom
  have hi : Function.Injective i := Subtype.val_injective.comp ψ.symm.injective
  have hzero : (picardZero k C : Set C.Pic) = f.picZero :=
    Scheme.coe_ker_picDegreeHom
  have hrange : Set.range i = f.picZero := by
    rw [← hzero]
    ext L
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ.symm a).property
    · intro hL
      exact ⟨ψ ⟨L, hL⟩, by simp [i]⟩
  have hdiv (n : ℕ) (hn : 0 < n) :
      Function.Surjective fun a : 𝟙_ (Over (Spec (.of k))) ⟶ J ↦ a ^ n :=
    surjective_npow_points n hn
  refine ⟨i, hi, hrange, ?_, hdiv, ?_⟩
  · intro a
    obtain ⟨h, hh⟩ := hΦ (ψ.symm a)
    refine ⟨h, ?_⟩
    exact (congrArg r.homEquiv.symm hh).symm.trans
      ((hψ _).symm.trans (ψ.apply_symm_apply a))
  · intro n hn
    refine ⟨?_, ?_, ?_⟩
    · ext L
      constructor
      · rintro ⟨a, rfl⟩
        refine ⟨a ≫ torsionSubgroupScheme.ι J n, ?_, rfl⟩
        change (a ≫ torsionSubgroupScheme.ι J n) ^ n = 1
        rw [← comp_pow, torsionSubgroupScheme.ι_pow, comp_one]
      · rintro ⟨a, ha, rfl⟩
        have hker : a ≫ (𝟙 J ^ n) = 1 := by
          rw [comp_pow, Category.comp_id, ha]
        refine ⟨GrpObj.kerLift (𝟙 J ^ n) a hker, ?_⟩
        change i (GrpObj.kerLift (𝟙 J ^ n) a hker ≫ GrpObj.kerι (𝟙 J ^ n)) = i a
        rw [GrpObj.kerLift_kerι]
    · ext L
      constructor
      · rintro ⟨a, ha, rfl⟩
        change (i a) ^ n = 1
        rw [← map_pow, ha, map_one]
      · intro hL
        let d := Scheme.picDegreeHom k C
        have hd : d L = 1 := by
          have h : (d L) ^ n = 1 := by rw [← map_pow, hL, map_one]
          have hz : (n : ℤ) * Multiplicative.toAdd (d L) = 0 :=
            congrArg Multiplicative.toAdd h
          have hz' : Multiplicative.toAdd (d L) = 0 :=
            (mul_eq_zero.mp hz).resolve_left (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
          exact congrArg Multiplicative.ofAdd hz'
        have hmem : L ∈ f.picZero := by
          rw [← hzero]
          exact hd
        obtain ⟨a, ha⟩ := hrange.symm ▸ hmem
        refine ⟨a, ?_, ha⟩
        apply hi
        rw [map_pow, ha, hL, map_one]
    · obtain ⟨P0, hP0, e, hfirst, _⟩ := f.exists_mulEquiv_prod_picZero
      have hdiv0 : Function.Surjective (fun x : P0 ↦ x ^ n) := by
        intro L
        have hL : (L : C.Pic) ∈ f.picZero := by rw [← hP0]; exact L.property
        obtain ⟨a, ha⟩ := hrange.symm ▸ hL
        obtain ⟨b, hb⟩ := hdiv n hn a
        change b ^ n = a at hb
        have hbmem : i b ∈ P0 := by
          change i b ∈ (P0 : Set C.Pic)
          rw [hP0, ← hrange]
          exact ⟨b, rfl⟩
        refine ⟨⟨i b, hbmem⟩, Subtype.ext ?_⟩
        change (i b) ^ n = L.val
        rw [← map_pow, hb, ha]
      let φ : C.Pic →* Multiplicative (ZMod n) :=
        (Int.castAddHom (ZMod n)).toMultiplicative.comp
          ((MonoidHom.fst (Multiplicative ℤ) P0).comp e.toMonoidHom)
      have hφ : Function.Surjective φ := by
        intro a
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
        refine ⟨e.symm (Multiplicative.ofAdd z, 1), ?_⟩
        change Multiplicative.ofAdd (((e (e.symm (Multiplicative.ofAdd z, 1))).1.toAdd : ℤ) :
          ZMod n) = a
        simpa using congrArg Multiplicative.ofAdd hz
      have hker : (powMonoidHom n : C.Pic →* C.Pic).range = φ.ker := by
        ext L
        constructor
        · rintro ⟨M, rfl⟩
          change φ (M ^ n) = 1
          rw [map_pow]
          change Multiplicative.ofAdd (n • Multiplicative.toAdd (φ M)) = 1
          simp
        · intro hL
          have hz : (((e L).1.toAdd : ℤ) : ZMod n) = 0 :=
            congrArg Multiplicative.toAdd hL
          obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
          obtain ⟨M, hM⟩ := hdiv0 (e L).2
          refine ⟨e.symm (Multiplicative.ofAdd z, M), ?_⟩
          change (e.symm (Multiplicative.ofAdd z, M)) ^ n = L
          apply e.injective
          rw [map_pow, e.apply_symm_apply]
          apply Prod.ext
          · change Multiplicative.ofAdd (n • z) = (e L).1
            apply Multiplicative.toAdd.injective
            simpa [nsmul_eq_mul, mul_comm] using hz.symm
          · exact hM
      refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ), ?_⟩
      intro L
      change φ L = _
      change Multiplicative.ofAdd (((e L).1.toAdd : ℤ) : ZMod n) = _
      rw [hfirst]
      rfl

end AlgebraicGeometry
