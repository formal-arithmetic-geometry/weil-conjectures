/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# The geometric fundamental group inside the Weil group

For base point data `B` of a Weil group `W` of a curve `C₀`
(`AlgebraicGeometry.WeilGroup.BasePointData`), the map `π₁(C, t) → π₁(C₀, s)` induced by base
change of finite étale schemes (`AlgebraicGeometry.WeilGroup.BasePointData.geomAut`) lands in the
Weil group with degree zero and identifies `π₁(C, t) = Aut F_t` with the geometric part
`W.geometric = ker deg`, as topological groups
(`AlgebraicGeometry.WeilGroup.BasePointData.geomEquiv`); this is the homotopy exact sequence
(`AlgebraicGeometry.WeilGroup.isEtaleQuotient`) at the base point `t`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- The image of `π₁(C, t)` in `π₁(C₀, s)` acts trivially on the constant covers. -/
theorem mem_weilGroup_geomAut (g : Aut (fiber B.t)) :
    haveI := W.geometricallyConnected
    (B.geomAut g, (1 : Multiplicative ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
  sorry

/-- The map `π₁(C, t) → W(C₀)`, `g ↦ (geomAut g, 0)`. -/
noncomputable def geomHom : Aut (fiber B.t) →* W.carrier :=
  haveI := W.geometricallyConnected
  W.weilGroupEquiv.symm.toMonoidHom.comp
    (((B.geomAut).prod (1 : Aut (fiber B.t) →* Multiplicative ℤ)).codRestrict _
      B.mem_weilGroup_geomAut)

lemma weilGroupEquiv_geomHom (g : Aut (fiber B.t)) :
    haveI := W.geometricallyConnected
    (W.weilGroupEquiv (B.geomHom g) : W.fundamentalGroup × Multiplicative ℤ) = (B.geomAut g, 1) :=
  by simp [geomHom]

lemma toFundamentalGroup_geomHom (g : Aut (fiber B.t)) :
    W.toFundamentalGroup (B.geomHom g) = B.geomAut g := by
  rw [toFundamentalGroup_apply, weilGroupEquiv_geomHom]

lemma geomHom_mem (g : Aut (fiber B.t)) : B.geomHom g ∈ W.geometric := by
  rw [MonoidHom.mem_ker, W.deg_eq]
  exact congrArg Prod.snd (B.weilGroupEquiv_geomHom g)

/-- **The geometric fundamental group is the geometric part of the Weil group**: base change of
finite étale schemes identifies `π₁(C, t) = Aut F_t` with `W.geometric = ker deg` as topological
groups (the homotopy exact sequence). -/
noncomputable def geomEquiv : Aut (fiber B.t) ≃ₜ* W.geometric :=
  sorry

lemma geomEquiv_apply (g : Aut (fiber B.t)) : (B.geomEquiv g : W.carrier) = B.geomHom g := by
  sorry

end AlgebraicGeometry.WeilGroup.BasePointData
