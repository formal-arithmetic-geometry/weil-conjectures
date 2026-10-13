/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# Base points for the Weil fundamental representation

Let `C₀` be a curve over the finite field `K` with Weil group `W`, presented through the étale
fundamental group `π₁(C₀, s)` at the geometric base point `s`, and let `C = C₀ ×_K K̄` be the
geometric curve with projection `C ⟶ C₀` and geometric Galois Frobenius `Fr`. The Weil
fundamental representation of a lisse Weil sheaf (`def-wf-fundamental-representation`) is the
stalk at a geometric point `t` of `C`, with the action of `π₁(C, t)` and the operator induced by
the Weil structure after "the usual transport of the stalk from `Fr(t)` to `t`". This file fixes
the auxiliary data of that construction
(`AlgebraicGeometry.WeilGroup.BasePointData`): a `K̄`-rational point `t` of `C`, a path from the
image of `t` in `C₀` to `s`, and a path `β` from `t` to `t ≫ Fr`.

A path on `C` between points with the same image in `C₀` is pushed down to an element of
`π₁(C₀, s)` (`AlgebraicGeometry.WeilGroup.BasePointData.downAut`): the base change of finite
étale `C₀`-schemes to `C` carries the fibre functors at `y` and `z` to those at their images.
This gives the map `π₁(C, t) → π₁(C₀, s)` (`geomAut`) and the lift of the Frobenius
(`frobAut`, the image of `β`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p)

/-- The auxiliary data of the Weil fundamental representation (`def-wf-fundamental-representation`):
a `K̄`-rational geometric point `t` of the geometric curve `C`, a path from its image in `C₀` to
the base point `s` of the Weil group, and a path `β` from `t` to `t ≫ Fr`. -/
structure BasePointData where
  /-- The geometric base point of the geometric curve. -/
  t : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber
  /-- The base point is `K̄`-rational. -/
  ht : t ≫ p.geometricFiberToAlgebraicClosure = 𝟙 _
  /-- A path from the image of `t` in `C₀` to the base point `s` of `W`. -/
  path : fiber (t ≫ p.geometricFiberProj) ≅ fiber W.basePoint
  /-- A path from `t` to `t ≫ Fr`. -/
  frobPath : fiber t ≅ fiber (t ≫ p.geometricGaloisFrobenius.hom)

/-- Base point data exist: the geometric curve has a `K̄`-rational point, and any two fibre
functors on the finite étale schemes over a connected scheme are isomorphic. -/
theorem nonempty_basePointData [ConnectedSpace p.geometricFiber] :
    Nonempty (BasePointData W) := by
  have := W.connectedSpace
  have : Nonempty p.geometricFiber := by
    have := W.geometricallyConnected
    infer_instance
  obtain ⟨t, ht⟩ := p.geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  exact ⟨⟨t, ht, (nonempty_iso_of_fiberFunctor _ _).some,
    (nonempty_iso_of_fiberFunctor _ _).some⟩⟩

namespace BasePointData

variable {W} (B : BasePointData W)

/-- An automorphism of the fibre functor at the image of `t` in `C₀`, as an element of
`π₁(C₀, s)`, through the path `B.path`. -/
noncomputable def toπ : Aut (fiber (B.t ≫ p.geometricFiberProj)) ≃* W.fundamentalGroup :=
  haveI := W.connectedSpace
  { toFun e := (toAutMulEquiv (fiber W.basePoint) W.fundamentalGroup).symm
      (B.path.symm ≪≫ e ≪≫ B.path)
    invFun g := B.path ≪≫ toAutMulEquiv (fiber W.basePoint) W.fundamentalGroup g ≪≫ B.path.symm
    left_inv e := by ext; simp
    right_inv g := by
      simp only [Iso.symm_self_id_assoc, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
      exact (toAutMulEquiv _ _).symm_apply_apply g
    map_mul' e e' := by
      rw [← map_mul]
      congr 1
      ext
      simp [Aut.Aut_mul_def] }

lemma toAutMulEquiv_toπ (e : Aut (fiber (B.t ≫ p.geometricFiberProj))) :
    haveI := W.connectedSpace
    toAutMulEquiv (fiber W.basePoint) W.fundamentalGroup (B.toπ e) =
      B.path.symm ≪≫ e ≪≫ B.path :=
  MulEquiv.apply_symm_apply _ _

/-- A path `δ : F_t ≅ F_y` on the geometric curve to a point `y` with the same image in `C₀` as
`t`, pushed down to an element of `π₁(C₀, s)`: the induced path `F_{t ≫ π} ≅ F_{y ≫ π}` on
`C₀` composed with `B.path`. -/
noncomputable def downAut {y : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber}
    (δ : fiber B.t ≅ fiber y) (h : y ≫ p.geometricFiberProj = B.t ≫ p.geometricFiberProj) :
    W.fundamentalGroup :=
  B.toπ (pullbackPathIso p.geometricFiberProj δ ≪≫ eqToIso (congrArg fiber h))

/-- The map `π₁(C, t) → π₁(C₀, s)` induced by base change of finite étale schemes. -/
noncomputable def geomAut : Aut (fiber B.t) →* W.fundamentalGroup where
  toFun g := B.downAut g rfl
  map_one' := by
    simp only [downAut, eqToIso_refl, Iso.trans_refl]
    rw [← map_one B.toπ]
    congr 1
    exact pullbackPathIso_refl _ _
  map_mul' g g' := by
    simp only [downAut, eqToIso_refl, Iso.trans_refl]
    rw [← map_mul]
    congr 1
    rw [Aut.Aut_mul_def, Aut.Aut_mul_def, pullbackPathIso_trans]

lemma geomAut_apply (g : Aut (fiber B.t)) :
    B.geomAut g = B.toπ (pullbackPathIso p.geometricFiberProj g) := by
  simp [geomAut, downAut]

/-- The element of `π₁(C₀, s)` attached to the path `β : F_t ≅ F_{t ≫ Fr}`: a lift of the
Frobenius, of degree one (`AlgebraicGeometry.WeilGroup.BasePointData.mem_weilGroup_frobAut`). -/
noncomputable def frobAut : W.fundamentalGroup :=
  B.downAut B.frobPath (by
    rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])

/-- The `m`-th iterate `β_m : F_t ≅ F_{t ≫ Frᵐ}` of the path `β`:
`β_{m+1} = β_m ≫ (Frᵐ)_* β`, where `(Frᵐ)_* β : F_{t ≫ Frᵐ} ≅ F_{t ≫ Fr ≫ Frᵐ}` is the path
induced by `β` along `Frᵐ`. -/
noncomputable def frobPathPow :
    (m : ℕ) → (fiber B.t ≅ fiber (B.t ≫ (p.geometricGaloisFrobenius ^ m).hom))
  | 0 => eqToIso (by rw [pow_zero]; rfl)
  | m + 1 => frobPathPow m ≪≫
      pullbackPathIso (p.geometricGaloisFrobenius ^ m).hom B.frobPath ≪≫
      eqToIso (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc])

end BasePointData

end AlgebraicGeometry.WeilGroup
