/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist

/-! # Descent of degree-one twists, before constructing a map from a base module

Source: Stacks Project, Constructions, Tag 01NR.
(blueprint: lem-trf-relative-proj-twist-chart-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The open on which a chart reads the sections above its base open. -/
noncomputable def twistChartOpen (U : S.affineOpens) : (Proj (A.grading U)).Opens :=
  A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1)

/-- A homogeneous element, viewed as a section of the affine degree-one twist. -/
noncomputable def twistChartFraction (U : S.affineOpens) (a : A.grading U 1) :
    Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
  (Proj.unitToTwist a.property).app (A.twistChartOpen U)
    (1 : Γ(Proj (A.grading U), A.twistChartOpen U))

/-- Reading a global module section in an affine twist chart, using the actual tensor unit.
The codomain is written as iterated pushforward so this is a linear map over the base. -/
noncomputable def twistChartRead (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1)
    (U : S.affineOpens) :
    ((Scheme.Modules.pushforward A.relProjHom).obj L).val.obj (op U.1) ⟶
      ((Scheme.Modules.pushforward A.relProjHom).obj
        ((Scheme.Modules.pushforward (A.relProjι U)).obj
          (Proj.twist (A.grading U) 1))).val.obj (op U.1) :=
  (((Scheme.Modules.pushforward A.relProjHom).map
    ((Scheme.Modules.tensorPullbackSectionAdjunction (A.relProjι U)).unit.app L ≫
      (Scheme.Modules.pushforward (A.relProjι U)).map (chart U).hom)).val.app (op U.1))

/-- The affine twists descend with their restriction maps. This is object descent only:
there is no morphism from a module on the base in the conclusion.

Source: Stacks, Tag 01NR, proof of lemma-glue-relative-proj-twists, using the
restriction and transitivity formulas in Tags 01N2 and 01MY.
(blueprint: lem-trf-relative-proj-twist-chart-descent).

Proof: use O(1) on Proj(A(U)) for every affine base open U. For U contained in V,
coefficientwise base change identifies the pulled-back twist with O(1) on Proj(A(U));
on homogeneous fractions the map sends a/f^k to res(a)/res(f)^k. The comparison
isomorphisms compose because those formulas compose, including identity restrictions.
Refine an intersection of two affine opens by affine opens inside the intersection.
The comparison maps agree on further refinements, so define overlap isomorphisms;
their triple cocycle follows by checking on the same refinements. Apply module-sheaf
object descent to the relative Proj chart cover. This gives L and the displayed chart
isomorphisms. Restrict sections through the comparison maps to obtain t. The descent
compatibility gives the first equation. The fraction formula applied to a/1 gives the
second equation. The tensor unit is the usual restriction unit under the uniquely
unit-compatible comparison for an open immersion, so the first equation uses exactly
twistChartRead. Zero rings, empty charts, and the empty base cause no exceptions. -/
theorem exists_twist_chart_descent :
    ∃ (L : A.relProj.Modules)
      (chart : ∀ U : S.affineOpens,
        (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
          Proj.twist (A.grading U) 1),
    ∀ (U V : S.affineOpens) (h : U ≤ V),
      ∃ t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U),
        (∀ s : Γ(L, A.relProjHom ⁻¹ᵁ V.1),
          t (A.twistChartRead L chart V s) =
            A.twistChartRead L chart U
              (L.presheaf.map ((TopologicalSpace.Opens.map A.relProjHom.base).map
                (homOfLE (X := S.Opens) h)).op s)) ∧
        (∀ a : A.grading V 1,
          t (A.twistChartFraction V a) =
            A.twistChartFraction U ⟨A.res h a, (A.res h).map_mem a.property⟩) := by
  classical
  sorry

end AlgebraicGeometry.Scheme.GradedAlgebraData
