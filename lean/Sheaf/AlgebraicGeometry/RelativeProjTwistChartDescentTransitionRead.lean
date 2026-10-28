/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentCompatibility

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.GradedAlgebraData
variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The normalized transition induced by a compatible chart square intertwines reading maps.

Source: Stacks Project, Constructions, Tag 01NR, compatibility portion of
`lemma-glue-relative-proj-twists`.
The proof expands the section-normalized pullback adjunction, uses naturality of its unit,
and evaluates the displayed chart square on a section.  The first map in the square is
transported across the equality of the two chart preimages, and the remaining composition
is exactly the normalized transition map.
(blueprint: lem-trf-relative-proj-twist-chart-descent-transition-read).
-/
theorem twist_chart_transition_read
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1)
    (U V : S.affineOpens) (h : U ≤ V)
    (θ : ∀ j : ℤ,
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
          (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j)
    (hθ : Proj.IsScalarExtensionTwistComparison (A.res h)
      (A.relProjFunctor.map (homOfLE h)) θ)
    (hsq :
      eqToIso (congrArg (fun f ↦
          (Scheme.Modules.tensorPullback f).obj L)
        (A.relProjFunctor_map_relProjι (homOfLE h)).symm) ≪≫
        (Scheme.Modules.tensorPullbackSectionComp
          (A.relProjFunctor.map (homOfLE h)) (A.relProjι V)).app L ≪≫
        (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso
          (chart V) ≪≫ θ 1 = chart U)
    (hopen : A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V =
      A.twistChartOpen U) :
    ∀ s : Γ(L, A.relProjHom ⁻¹ᵁ V.1),
      let t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
        ConcreteCategory.hom
          (((Scheme.Modules.tensorPullbackSectionAdjunction
              (A.relProjFunctor.map (homOfLE h))).unit.app
              (Proj.twist (A.grading V) 1)).app (A.twistChartOpen V) ≫
            (θ 1).hom.app
              (A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V) ≫
            eqToHom (congrArg
              (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen))
      t (A.twistChartRead L chart V s) =
        A.twistChartRead L chart U
          (L.presheaf.map ((TopologicalSpace.Opens.map A.relProjHom.base).map
            (homOfLE (X := S.Opens) h)).op s) := by
  sorry

end AlgebraicGeometry.Scheme.GradedAlgebraData
