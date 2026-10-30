/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.WeilMonodromyGeneral

/-!
# The Weil group inside the arithmetic fundamental group

Let `X₀` be a scheme over a finite field `K`, `π : X ⟶ X₀` the projection of its geometric
fibre and `B = (t, β)` base point data (`AlgebraicGeometry.FrobeniusBasePoint`). The abstract
Weil group `W = π₁(X, t) ⋊ ℤ` of `B` (`AlgebraicGeometry.FrobeniusBasePoint.WeilGroup`) maps to
the arithmetic fundamental group `π₁(X₀, t ≫ π) = Aut F_{t ≫ π}`: a loop `g` at `t` goes to the
induced loop `π_* g`, and the generator of `ℤ` goes to the *arithmetic Frobenius element*
`π_* β` (`AlgebraicGeometry.FrobeniusBasePoint.arithFrob`), a loop at `t ≫ π` since
`Fr ≫ π = π`. This is `AlgebraicGeometry.FrobeniusBasePoint.toArith`.

For `X₀` geometrically connected and quasi-compact quasi-separated, the homotopy exact sequence
shows:

* `π₁(X, t) → π₁(X₀, t ≫ π)` is continuous and injective
  (`AlgebraicGeometry.FrobeniusBasePoint.continuous_toArith_inl`,
  `AlgebraicGeometry.FrobeniusBasePoint.injective_toArith_inl`);
* the image of `W` is dense (`AlgebraicGeometry.FrobeniusBasePoint.denseRange_toArith`);
* the degree is continuous for the profinite topology: for every `M > 0` there is a
  neighbourhood `U` of `1` such that `toArith w ∈ U` forces `M ∣ deg w`
  (`AlgebraicGeometry.FrobeniusBasePoint.exists_nhds_forall_dvd_deg`), the stabiliser of a point of
  the geometric fibre of the constant cover of degree `M`.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry.FrobeniusBasePoint

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (B : FrobeniusBasePoint K X)

/-- The *arithmetic Frobenius element* `π_* β ∈ π₁(X₀, t ≫ π)`: the path `β : F_t ≅ F_{t ≫ Fr}`
of the geometric fibre, pushed down along the projection `π : X ⟶ X₀`, which is a loop at
`t ≫ π` since `Fr ≫ π = π`. -/
noncomputable def arithFrob : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj B.frobPath ≪≫
    eqToIso (congrArg fiber (by
      rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]))

/-- Conjugation by the arithmetic Frobenius element induces the Frobenius transport
`B.frobConj` on the image of `π₁(X, t)`. -/
theorem pullbackPathHom_frobConj (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t (B.frobConj g) =
      B.arithFrob⁻¹ * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        B.arithFrob := by
  sorry

/-- **The Weil group in the arithmetic fundamental group**: the homomorphism
`π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ π)`, `(g, n) ↦ π_* g · φⁿ` with `φ = π_* β` the arithmetic Frobenius
element. -/
noncomputable def toArith :
    B.WeilGroup →* Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  SemidirectProduct.lift (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t)
    (zpowersHom _ B.arithFrob) fun n ↦ by
      sorry

@[simp]
lemma toArith_inl (g : Aut (fiber B.t)) :
    B.toArith (SemidirectProduct.inl g) =
      pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp]
lemma toArith_inr (n : Multiplicative ℤ) :
    B.toArith (SemidirectProduct.inr n) = B.arithFrob ^ n.toAdd :=
  SemidirectProduct.lift_inr _ _ _ n

/-- The arithmetic Frobenius element is the image of the lift of the Frobenius. -/
lemma toArith_frobLift : B.toArith B.weilData.frobLift = B.arithFrob := by
  sorry

/-- The map `π₁(X, t) → π₁(X₀, t ≫ π)` is continuous. -/
theorem continuous_toArith_inl :
    Continuous fun g : Aut (fiber B.t) ↦ B.toArith (SemidirectProduct.inl g) := by
  sorry

/-- The map `π₁(X, t) → π₁(X₀, t ≫ π)` is injective (homotopy exact sequence). -/
theorem injective_toArith_inl [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber] :
    Function.Injective fun g : Aut (fiber B.t) ↦ B.toArith (SemidirectProduct.inl g) := by
  sorry

/-- **The Weil group is dense in the arithmetic fundamental group.** -/
theorem denseRange_toArith [GeometricallyConnected (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [CompactSpace X]
    [QuasiSeparatedSpace X] [ConnectedSpace X]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    DenseRange B.toArith := by
  sorry

/-- **The degree is continuous for the profinite topology**: for every `M > 0` there is a
neighbourhood `U` of `1` in `π₁(X₀, t ≫ π)` such that the degree of every element of the Weil
group mapping into `U` is divisible by `M` (`U` is the stabiliser of a point of the geometric
fibre of the constant cover of degree `M`, on which an element of degree `n` acts as the `n`-th
power of the geometric Frobenius). -/
theorem exists_nhds_forall_dvd_deg [GeometricallyConnected (X ↘ Spec (.of K))]
    [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) (M : ℕ) (hM : 0 < M) :
    ∃ U ∈ 𝓝 (1 : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))),
      ∀ w, B.toArith w ∈ U → (M : ℤ) ∣ Multiplicative.toAdd (B.weilData.deg w) := by
  sorry

end AlgebraicGeometry.FrobeniusBasePoint
