/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv
import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections

/-! # Affine conormal exterior coordinates preserving ideal wedges

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- On one affine chart the exterior conormal coordinate sends the wedge of the
pullback-unit images of ideal sections to the associated algebraic conormal wedge.
This statement involves no derived category or Tor module. -/
theorem exists_selfTor_conormal_wedge_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1))
              (fun j ↦ ((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                  i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b) := by
  obtain ⟨e, he⟩ := exists_selfTor_conormal_wedge_chart_section_equiv i n U
  obtain ⟨s, hs⟩ := exists_selfTor_conormal_wedge_chart_from_sections i n U e
  refine ⟨s, ?_⟩
  intro b
  rw [hs]
  exact he b

end AlgebraicGeometry
