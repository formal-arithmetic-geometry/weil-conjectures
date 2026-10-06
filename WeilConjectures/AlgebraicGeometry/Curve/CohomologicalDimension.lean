/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The étale cohomological dimension of a curve

The étale cohomological dimension of a curve over an algebraically closed field is at most two,
and at most one if the curve is affine: `H^q(C_ét, F) = 0` for every torsion abelian sheaf `F`
(`CategoryTheory.Sheaf.IsTorsion`) and `q ≥ 3`, resp. `q ≥ 2`.

Neither statement needs smoothness, connectedness, or `char k` to be prime to the torsion of
`F`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`: `H^q(C, F) = 0` for `q ≥ 3`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`: `H^q(C, F) = 0` for
  `q ≥ 2` on an affine curve.
- `AlgebraicGeometry.subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero`: the
  cohomology of the constant sheaf `ℤ/d` on a smooth affine curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Vanishing in high degrees.** Let `C` be a curve over an algebraically closed field `k`.
Then `H^q(C_ét, F) = 0` for `q ≥ 3` and every torsion abelian sheaf `F` on `C_ét`: the étale
cohomological dimension of a curve over an algebraically closed field is at most two. The
sharper bound for affine `C` is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.
(blueprint: `sk-prop-cd`) -/
@[stacks 03SC "(1)"]
theorem subsingleton_sheafH_of_three_le (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) :=
  -- Proof sketch: after reducing to a smooth integral curve, the cohomology of `F` is compared
  -- with that of its pushforward from the generic point. The function field `k(C)` has
  -- cohomological dimension at most one, because every finite separable extension `L` of
  -- `k(C)` is `C₁` by Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one`, hence has
  -- `Br(L) = 0` by `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`. The `p`-primary
  -- part in characteristic `p` goes through the Artin–Schreier sequence.
  sorry

/-- **Cohomological dimension of an affine curve.** Let `C` be an affine curve over an
algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every torsion abelian
sheaf `F` on `C_ét`: the étale cohomological dimension of an affine curve over an
algebraically closed field is at most one.
(blueprint: `sk-prop-cd-affine`) -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_of_two_le_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) :=
  -- Proof sketch: degrees `q ≥ 3` are `subsingleton_sheafH_of_three_le`. In degree two one
  -- reduces to `F = ℤ/n` on a smooth integral affine curve. For `n` prime to `char k` the
  -- Kummer sequence identifies `H²(C, μₙ)` with `Pic(C)/n`, which vanishes because `Pic(C)`
  -- is `n`-divisible; the `p`-primary part is the Artin–Schreier sequence.
  sorry

end IsCurve

/-- The constant sheaf `ℤ/d` with `d ≠ 0` is a torsion sheaf: its sections are killed by
`d`. -/
lemma Scheme.isTorsion_constantZMod (X : Scheme.{u}) {d : ℕ} (hd : d ≠ 0) :
    (X.constantZMod d).IsTorsion := by
  intro U s
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, Nat.pos_of_ne_zero hd, ?_⟩
  have h₀ : d • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) = 0 := by
    ext x
    simp
  have h₁ : d • 𝟙 (X.constantZMod d) = 0 := by
    rw [← (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id,
      ← Functor.map_nsmul, h₀, Functor.map_zero]
  have h₂ := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app U) h₁
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h₂
  simpa using congrArg (fun g ↦ g.hom s) h₂

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `sbc-thm-cohomological-dimension-of-an-affine-curve`: Affine-curve cohomological
dimension.

Let `k` be algebraically closed, let `C` be a smooth affine curve over `k` and let `d ≥ 1`.
Then `H^q(C_ét, ℤ/d) = 0` for `q > 1`, and `H^0(C_ét, ℤ/d) = ℤ/d` when `C` is connected.

The vanishing is the case of the torsion sheaf `ℤ/d` of
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine` (blueprint
`sk-prop-cd-affine`), which does not need `d` to be prime to the characteristic; the degree
zero statement is `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`. -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsAffine C] {d : ℕ} (hd : d ≠ 0) :
    (∀ q, 1 < q → Subsingleton (Sheaf.H (C.constantZMod d) q)) ∧
      (ConnectedSpace C → Nonempty (Sheaf.H (C.constantZMod d) 0 ≃+ ZMod d)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve f :=
    { toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      krullDim_le_one := by
        simpa using topologicalKrullDim_le_of_smoothOfRelativeDimension f 1 }
  exact ⟨fun q hq ↦ IsCurve.subsingleton_sheafH_of_two_le_of_isAffine f _
    (C.isTorsion_constantZMod hd) q hq, fun _ ↦ C.nonempty_addEquiv_sheafH_zero_constantZMod d⟩

end AlgebraicGeometry
