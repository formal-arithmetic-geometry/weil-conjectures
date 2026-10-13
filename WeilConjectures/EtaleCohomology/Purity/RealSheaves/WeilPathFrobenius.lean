/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# The Frobenius lift of base point data

For base point data `B` of a Weil group `W` (`AlgebraicGeometry.WeilGroup.BasePointData`), the
path `β : F_t ≅ F_{t ≫ Fr}` pushes down to an element `frobAut` of `π₁(C₀, s)` which lies in the
Weil group with degree one: it acts on the geometric fibres of the constant covers as the
geometric Frobenius (`AlgebraicGeometry.WeilGroup.BasePointData.mem_weilGroup_frobAut`).
Conjugation by it is the transport of `π₁(C, t)` along `Fr` and `β`
(`AlgebraicGeometry.WeilGroup.BasePointData.geomAut_frobConj`), and the iterated paths `β_m`
push down to its powers (`AlgebraicGeometry.WeilGroup.BasePointData.downAut_frobPathPow`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- Changing the path in `downAut` multiplies by the image of a loop at `t`. -/
lemma downAut_eq_mul_geomAut {y : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber}
    (δ δ' : fiber B.t ≅ fiber y) (h : y ≫ p.geometricFiberProj = B.t ≫ p.geometricFiberProj) :
    B.downAut δ h = B.downAut δ' h * B.geomAut (δ ≪≫ δ'.symm) := by
  sorry

/-- **The Frobenius lift has degree one**: the push-down of `β : F_t ≅ F_{t ≫ Fr}` acts on the
geometric fibres of the constant covers as the geometric Frobenius. -/
theorem mem_weilGroup_frobAut :
    haveI := W.geometricallyConnected
    (B.frobAut, Multiplicative.ofAdd (1 : ℤ)) ∈ weilGroup p W.basePoint W.fundamentalGroup := by
  sorry

/-- Conjugation by the Frobenius lift is the transport of loops at `t` along `Fr` and `β`:
for a loop `g` at `t`, the loop `β ≫ Fr_* g ≫ β⁻¹` maps to `frobAut⁻¹ (geomAut g) frobAut`. -/
theorem geomAut_frobConj (g : Aut (fiber B.t)) :
    B.geomAut (B.frobPath ≪≫ pullbackPathIso p.geometricGaloisFrobenius.hom g ≪≫
      B.frobPath.symm) = B.frobAut⁻¹ * B.geomAut g * B.frobAut := by
  sorry

/-- The iterated path `β_m` pushes down to the `m`-th power of the Frobenius lift. -/
theorem downAut_frobPathPow (m : ℕ)
    (h : (B.t ≫ (p.geometricGaloisFrobenius ^ m).hom) ≫ p.geometricFiberProj =
      B.t ≫ p.geometricFiberProj) :
    B.downAut (B.frobPathPow m) h = B.frobAut ^ m := by
  sorry

end AlgebraicGeometry.WeilGroup.BasePointData
