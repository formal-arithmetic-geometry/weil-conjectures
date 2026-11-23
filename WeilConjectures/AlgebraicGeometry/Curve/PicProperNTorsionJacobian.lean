/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The torsion of the Picard group of a curve is the torsion of its Jacobian

For a smooth proper connected curve `C` over an algebraically closed field `k` and `n` invertible
in `k`, the `n`-torsion `Pic(C)[n]` of the Picard group is the group `J(C)[n](k)` of `k`-points of
the `n`-torsion subgroup scheme of the Jacobian: every `n`-torsion class has degree zero, and the
identification `Pic⁰(C) ≅ J(C)(k)` restricts to the `n`-torsion.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Blueprint `corollary-torsion-jacobian-field-extension--4`: `Pic(C)[n] = J(C)[n](k)`.

Let `C` be a smooth proper connected curve over an algebraically closed field `k` and let `n` be
invertible in `k`. There is a Jacobian `J` of `C`, a commutative group scheme representing the
degree-zero Picard functor `Pic⁰_{C/k}` compatibly with the group laws, such that the `n`-torsion
`Pic(C)[n]` of the Picard group (written multiplicatively, as the kernel of `L ↦ L ^ n`) is in
bijection with the `k`-points of the `n`-torsion subgroup scheme `J[n]`
(`AlgebraicGeometry.torsionSubgroupScheme`): a class `L` corresponds to the `n`-torsion point of
`J` which the representation attaches to `L`. In particular every class in `Pic(C)[n]` has degree
zero, i.e. lies in `Pic⁰(C)`.

Proof: `C` is a smooth projective geometrically integral curve, so
`AlgebraicGeometry.exists_jacobian` gives `J` with `Pic⁰(C) ≅ J(k)` as groups. An `n`-torsion
class `L` satisfies `n · deg L = 0`, so `deg L = 0` and `L ∈ Pic⁰(C)`; hence
`Pic(C)[n] = Pic⁰(C)[n] ≅ J(k)[n]`, and `J(k)[n]` is the group of `k`-points of `J[n]`
(`AlgebraicGeometry.torsionByEquiv`). -/
theorem Scheme.Hom.exists_equiv_ker_powMonoidHom_pic_torsionSubgroupScheme
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    ∃ (J : Over (Spec (.of k))) (_ : CommGrpObj J)
      (e : (picardFunctorDegree f 0).obj.RepresentableBy J),
      IsPicardZeroMul f e ∧
      ∃ ψ : (powMonoidHom n : C.Pic →* C.Pic).ker ≃
          (𝟙_ (Over (Spec (.of k))) ⟶ torsionSubgroupScheme J n),
        ∀ L, ∃ h, ψ L ≫ torsionSubgroupScheme.ι J n =
          e.homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree f 0).toFunctor).app _
              ⟨Pic.map (pullback.fst f (𝟙_ (Over (Spec (.of k)))).hom) L.1, h⟩) := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyConnected f :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed f
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : GeometricallyReduced f := Smooth.geometricallyReduced f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  obtain ⟨J, hJ, e, -, -, -, he, ψ₀, hψ₀⟩ := exists_jacobian (k := k) (X := C)
  let := hJ
  -- an `n`-torsion class has degree zero
  have hd (L : (powMonoidHom n : C.Pic →* C.Pic).ker) : L.1 ∈ picardZero k C := by
    have h : (Scheme.picDegreeHom k C L.1) ^ n = 1 := by
      rw [← map_pow, show L.1 ^ n = 1 from L.2, map_one]
    have hz : (n : ℤ) * Multiplicative.toAdd (Scheme.picDegreeHom k C L.1) = 0 :=
      congrArg Multiplicative.toAdd h
    exact congrArg Multiplicative.ofAdd
      ((mul_eq_zero.mp hz).resolve_left (Int.natCast_ne_zero.mpr hn0))
  let φ : (powMonoidHom n : C.Pic →* C.Pic).ker ≃
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) (n : ℤ) :=
    { toFun L := ⟨Additive.ofMul (ψ₀ ⟨L.1, hd L⟩), by
        rw [AddSubgroup.torsionBy.nsmul_iff]
        change Additive.ofMul ((ψ₀ ⟨L.1, hd L⟩) ^ n) = 0
        rw [← map_pow, show (⟨L.1, hd L⟩ : picardZero k C) ^ n = 1 from
          Subtype.ext L.2, map_one]
        rfl⟩
      invFun x := ⟨(ψ₀.symm x.1.toMul).1, by
        change (ψ₀.symm x.1.toMul).1 ^ n = 1
        have h : (x.1.toMul) ^ n = 1 :=
          congrArg Additive.toMul ((AddSubgroup.torsionBy.nsmul_iff).mp x.2)
        rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]⟩
      left_inv L := Subtype.ext (by simp)
      right_inv x := Subtype.ext (by simp) }
  refine ⟨J, hJ, e, he, φ.trans (torsionByEquiv J n), fun L ↦ ?_⟩
  obtain ⟨h, hL⟩ := hψ₀ ⟨L.1, hd L⟩
  refine ⟨h, ?_⟩
  rw [Equiv.trans_apply, torsionByEquiv, torsionByPointsEquiv_comp_ι]
  exact hL

end AlgebraicGeometry
