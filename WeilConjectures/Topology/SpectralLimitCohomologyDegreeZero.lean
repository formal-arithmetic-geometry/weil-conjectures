/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.SpectralLimitCohomologyMap

/-! # Degree-zero evaluation of the canonical cohomology map

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-degree-zero)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

private theorem eval₀_restrict {X : TopCat.{u}}
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {U V : Opens X} (e : U = V) (x : CategoryTheory.Sheaf.H' F 0 U) :
    HEq (CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology X) V F
        (((CategoryTheory.Sheaf.cohomologyPresheaf F 0).map
          (eqToHom (congrArg op e))).hom x))
      (CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology X) U F x) := by
  subst V
  simp only [eqToHom_refl]
  rw [CategoryTheory.Functor.map_id]
  rfl

attribute [local irreducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

/-- The canonical cohomology map is the given f-map on degree-zero sections.
The heterogeneous equality transports along the equality between the inverse image
of the terminal open and the terminal open. Only normalization in degree zero at
the terminal open is needed.

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 01F8, the degree-zero
normalization of the induced cohomology map, applied to the maps in Tag 0A37.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-degree-zero)

Proof: first transport evaluation along the equality of terminal opens. Naturality
of evaluation in the coefficient sheaf moves the adjoint of α outside evaluation.
The normalization hypothesis then replaces the pullback class by the inverse-image
unit applied to its section. Finally the adjunction hom-equivalence, applied to
its inverse at α, says that the unit followed by the pushed-forward adjoint is α.
Evaluating this equality on the section gives the claimed heterogeneous equality. -/
theorem spectralLimitCohomologyMap_eval₀ {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    (hc : ∀
      (A : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (x : CategoryTheory.Sheaf.H' A 0 ⊤),
      CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology X)
        ((Opens.map f).obj ⊤) _ ((c 0 ⊤ A).hom x) =
      (((sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app A).hom.app
          (op ⊤)).hom
        (CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology Y) ⊤ A x))
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (α : F ⟶ (pushforward AddCommGrpCat.{u} f).obj G)
    (x : CategoryTheory.Sheaf.H' F 0 ⊤) :
    HEq (CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology X) ⊤ G
        ((spectralLimitCohomologyMap f c α 0).hom x))
      ((α.hom.app (op ⊤)).hom
        (CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology Y) ⊤ F x)) := by
  let adj := sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let β := (adj.homEquiv F G).symm α
  have hn := CategoryTheory.Sheaf.objectCohomologyEval₀_naturality
    (Opens.grothendieckTopology X) ((Opens.map f).obj ⊤) β ((c 0 ⊤ F).hom x)
  have hz := congrArg (fun t ↦ (β.hom.app (op ((Opens.map f).obj ⊤))).hom t) (hc F x)
  have hadj : adj.unit.app F ≫ (pushforward AddCommGrpCat.{u} f).map β = α :=
    (adj.homEquiv_unit (f := β)).symm.trans ((adj.homEquiv F G).apply_symm_apply α)
  have ha := congrArg (fun τ ↦ (τ.hom.app (op ⊤)).hom
    (CategoryTheory.Sheaf.objectCohomologyEval₀
      (Opens.grothendieckTopology Y) ⊤ F x)) hadj
  exact (eval₀_restrict G (Opens.map_top f) _).trans
    ((heq_of_eq hn).trans ((heq_of_eq hz).trans (heq_of_eq ha)))

end TopCat.Sheaf
