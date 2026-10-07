/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Tsen's theorem and the Brauer group of a curve

The function field of an integral curve over an algebraically closed field is `C₁`, so its
Brauer group vanishes; the Brauer group of a smooth curve over an algebraically closed field
vanishes, since it injects into that of its function field on each connected component; and the
Brauer group of every curve over an algebraically closed field vanishes.

Curves are given by a structure morphism `f : C ⟶ Spec k` satisfying
`AlgebraicGeometry.IsCurve`.

## Main statements

- `AlgebraicGeometry.IsCurve.isQuasiAlgClosed_functionField`: Tsen's theorem, the function
  field of an integral curve over an algebraically closed field is `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_functionField`: the Brauer
  group of that function field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace`: the
  Brauer group of a smooth connected curve over an algebraically closed field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth`: the Brauer group
  of a smooth curve over an algebraically closed field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a
  curve over an algebraically closed field vanishes.

## Implementation notes

The field-theoretic statements, Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one` and the
vanishing `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`, are the reusable ones; the
function-field statements here are their specialisations to curves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Tsen's theorem for curves.** For an integral curve `C` over an algebraically closed
field `k`, the function field `k(C)` is quasi-algebraically closed: every homogeneous form of
degree `d` in `N > d` variables over `k(C)` has a nontrivial zero. Neither smoothness nor
properness of `C` is assumed.
(blueprint: `sk-prop-tsen`) -/
theorem isQuasiAlgClosed_functionField (f : C ⟶ Spec (.of k)) [IsCurve f] [IsIntegral C] :
    IsQuasiAlgClosed C.functionField :=
  -- Proof sketch: `k(C)` has transcendence degree at most one over `k`, since `C` has
  -- dimension at most one, so this is `IsQuasiAlgClosed.of_trdeg_le_one`.
  sorry

/-- The Brauer group of the function field of an integral curve over an algebraically closed
field vanishes, `Br(k(C)) = H²(k(C), 𝔾ₘ) = 0`.
(blueprint: `sk-prop-tsen`) -/
theorem subsingleton_cohomologicalBrauerGroup_functionField (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsIntegral C] : Subsingleton (Spec C.functionField).CohomologicalBrauerGroup :=
  have := isQuasiAlgClosed_functionField f
  IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup C.functionField

/-- **The Brauer group of a smooth connected curve vanishes.** For a smooth connected curve
`C` over an algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. The curve `C` is
integral, noetherian and regular, so `Br(C)` injects into `Br(k(C))`
(`AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`), and `Br(k(C)) = 0` by Tsen's
theorem. Properness is not needed, so no compactification is used.
(blueprint: `lem-sc-brauer-zero`) -/
theorem subsingleton_cohomologicalBrauerGroup_of_connectedSpace (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] : Subsingleton C.CohomologicalBrauerGroup := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  -- `Br(k(C)) = 0`, and the pullback of `𝔾ₘ` to the generic point is `𝔾ₘ`
  have := subsingleton_cohomologicalBrauerGroup_functionField f
  have := C.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
      C.fromSpecFunctionField).obj C.gmSheaf) 2) :=
    let e := asIso (Scheme.upperStarGmSheafToGmSheaf C.fromSpecFunctionField)
    (Function.LeftInverse.injective (f := Sheaf.H.map e.hom 2) (g := Sheaf.H.map e.inv 2)
      fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton
  exact C.injective_cohomologyMap_gmSheaf_two.subsingleton

/-- **The Brauer group of a smooth curve vanishes.** For a smooth curve `C` over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. The blueprint states this for
smooth proper curves; properness is not needed.

The finitely many connected components of `C` are clopen, so `Br(C)` vanishes as soon as the
Brauer group of every component does
(`AlgebraicGeometry.Etale.subsingleton_H_of_isClopen`), and each component is a smooth
connected curve, to which `subsingleton_cohomologicalBrauerGroup_of_connectedSpace` applies.
(blueprint: `sk-thm-br`) -/
theorem subsingleton_cohomologicalBrauerGroup_of_smooth (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] : Subsingleton C.CohomologicalBrauerGroup := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  -- the connected components of `C`, indexed by `ConnectedComponents C`
  choose x hx using ConnectedComponents.surjective_coe (α := C)
  let U (c : ConnectedComponents C) : C.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hU (y : C) : y ∈ U y := by
    change y ∈ connectedComponent (x y)
    rw [ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  refine Etale.subsingleton_H_of_isClopen U (fun c ↦ isClosed_connectedComponent)
    (fun c d hcd ↦ ?_) (fun y ↦ ⟨y, hU y⟩) _ 2 fun c ↦ ?_
  · refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
      (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
    rw [← hx c, ← hx d, ConnectedComponents.coe_eq_coe,
      connectedComponent_eq hyc, connectedComponent_eq hyd]
  -- each connected component is a smooth connected curve
  have : ConnectedSpace (U c) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsCurve ((U c).ι ≫ f) :=
    { krullDim_le_one := (topologicalKrullDim_subspace_le C (U c)).trans (IsCurve.krullDim_le_one f) }
  have := subsingleton_cohomologicalBrauerGroup_of_connectedSpace ((U c).ι ≫ f)
  let e := Scheme.upperStarGmSheafIso (U c).ι
  exact (Function.LeftInverse.injective (f := Sheaf.H.map e.hom 2) (g := Sheaf.H.map e.inv 2)
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton

/-- **The Brauer group of a curve vanishes.** For a curve `C` over an algebraically closed
field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Neither smoothness nor properness is assumed.
(blueprint: `lem-sc-brauer-zero-all-curves`) -/
theorem subsingleton_cohomologicalBrauerGroup (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton C.CohomologicalBrauerGroup :=
  -- Proof sketch.
  -- * Smooth case: this is `subsingleton_cohomologicalBrauerGroup_of_smooth`.
  -- * Reduced case: for the normalisation `ν : C̃ ⟶ C` the cokernel `Q` of `𝔾ₘ ⟶ ν_* 𝔾ₘ` is
  --   supported on the finitely many singular points, so `H¹(C, Q) = 0`, and
  --   `H²(C, ν_* 𝔾ₘ) = H²(C̃, 𝔾ₘ) = 0` since `ν` is finite and `C̃` is smooth.
  -- * General case: with `𝒩` the nilradical, `1 + 𝒩` has a finite filtration whose graded
  --   pieces are coherent, and these have no `H²` on a scheme of dimension at most one.
  sorry

end AlgebraicGeometry.IsCurve
