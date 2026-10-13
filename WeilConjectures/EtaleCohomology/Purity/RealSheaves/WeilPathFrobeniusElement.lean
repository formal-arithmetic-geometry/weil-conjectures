/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath

/-!
# Local Frobenius elements from paths on the geometric curve

Let `x` be a closed point of the curve `C₀`, of degree `m = [κ(x) : K]`, and `x̄` the geometric
point of `C = C₀ ×_K K̄` over it (`AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`),
which satisfies `x̄ ≫ Frᵐ = σᵐ ≫ x̄` for the geometric Frobenius `σ` of `K̄`. For a path
`π : F_x̄ ≅ F_t` the loop

`F_t ≅ F_x̄ ≅ F_{σᵐ ≫ x̄} = F_{x̄ ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}`

(reparametrisation, then the path induced by `π` along `Frᵐ`) pushes down to a Frobenius element
at `x` of `π₁(C₀, s)` (`AlgebraicGeometry.WeilGroup.BasePointData.isFrobeniusElement_downAut`).
On the stalk of a Weil sheaf this loop is the transport of the local Frobenius `Fₓ` along `π`.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} (B : BasePointData W)

/-- The loop `F_t ≅ F_x̄ ≅ F_{σᵐ ≫ x̄} = F_{x̄ ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}` at a closed point `x` of
degree `m`, for a path `π : F_x̄ ≅ F_t`. -/
noncomputable def frobeniusLoop (x : C.finitePoints)
    (π : fiber (p.geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    fiber B.t ≅ fiber (B.t ≫ (p.geometricGaloisFrobenius ^ p.degreeOver x.1).hom) :=
  π.symm ≪≫ (fiberReparamIso (specGeometricFrobenius K ^ p.degreeOver x.1) _).symm ≪≫
    eqToIso (congrArg fiber
      (p.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x).symm) ≪≫
    pullbackPathIso (p.geometricGaloisFrobenius ^ p.degreeOver x.1).hom π

lemma frobeniusLoop_comp_geometricFiberProj (x : C.finitePoints) :
    (B.t ≫ (p.geometricGaloisFrobenius ^ p.degreeOver x.1).hom) ≫ p.geometricFiberProj =
      B.t ≫ p.geometricFiberProj := by
  sorry

/-- **The local Frobenius loop is a Frobenius element**: the push-down to `π₁(C₀, s)` of the loop
`AlgebraicGeometry.WeilGroup.BasePointData.frobeniusLoop` at a closed point `x` is a Frobenius
element at `x`. -/
theorem isFrobeniusElement_downAut (x : C.finitePoints)
    (π : fiber (p.geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    haveI := W.connectedSpace
    haveI : Finite (C.residueField x.1) := x.2
    IsFrobeniusElement W.basePoint W.fundamentalGroup x.1
      (B.downAut (B.frobeniusLoop x π) (B.frobeniusLoop_comp_geometricFiberProj x)) := by
  sorry

end AlgebraicGeometry.WeilGroup.BasePointData
