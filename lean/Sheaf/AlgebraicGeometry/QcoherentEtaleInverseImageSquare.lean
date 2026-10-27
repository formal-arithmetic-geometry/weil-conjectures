/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentEtaleExactComparison
public import Sheaf.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections

/-! # The sheaf-level inverse-image square for coherent coefficients

Source: Stacks Project, Tags 03P2, 03DR, 03AX and 03FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The inverse-image square and its two unit/coefficient triangles, before deriving.
There are no positive-degree cohomology groups and no arbitrary normalized
cohomology equivalences in this statement.

Source: Stacks Project, Etale Cohomology, Tags 03P2 and 03DR; Cohomology on Sites,
Tags 03AX and 03FD.
(blueprint: lem-pbc-coherent-etale-inverse-image-square).

Proof: For each scheme use the inclusion of open subschemes into its small etale
site. Compose its exact abelian inverse image with coefficient ULift to construct
P. Restricting tensor sections to opens gives the coefficient map by adjunction.
The image of the constant integer generator under the adjunction unit supplies
the integer map. Naturality of tensor restriction units gives coefficient
naturality and the section normalization in ExactComparison.

Base change of an open subscheme is the inverse-image open subscheme. This gives
the canonical commuting square of direct-image functors. Taking left adjoints
gives the isomorphism tau between the two composite inverse-image functors
(including the canonical commuting isomorphism with coefficient ULift). The
triangle for the integer maps is the composition law for the adjunction units,
evaluated on the constant integer generator. For the coefficient triangle, take
adjoints, restrict to an open, and use the tensor-pullback composition unit law.
The map along the resulting cartesian square is exactly
qcoherentPullbackSection; the hypothesis on theta therefore identifies the two
mates, component by component. Faithfulness of the adjunction Hom equivalences
proves the triangle. Inverse image of abelian sheaves is exact independently of
flatness of g. The constructions and unit laws also apply to empty schemes and
zero modules. -/
theorem exists_coherentEtale_inverseImage_square
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G))
    (hθ : ∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
      θ.hom.app (op U) (ULift.up s) = ULift.up
        (qcoherentPullbackSection g F G ψ U
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
          (pullback.fst U.hom g) pullback.condition s)) :
    let J := Opens.grothendieckTopology X
    let K := Opens.grothendieckTopology Y
    let Z := (Opens.map g.base).sheafPullback AddCommGrpCat.{u} J K
    let z := ((Opens.map g.base).constantSheafsheafPullbackIso AddCommGrpCat.{u} J K
      isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))
    let φ := (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ
    let f := (((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} J K).homEquiv
      _ _).symm (moduleAbelianHMap g φ)
    let E := Etale.upperStar AddCommGrpCat.{u + 1} g
    let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
      (AddCommGrpCat.of (ULift ℤ))
    let t := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
      (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G)).symm θ
    ∃ (D₁ : CoherentEtale.ExactComparison X) (D₂ : CoherentEtale.ExactComparison Y)
      (τ : D₁.P ⋙ E ≅ Z ⋙ D₂.P),
      e.hom ≫ E.map D₁.integer ≫ τ.hom.app (CoherentEtale.zariskiInteger X) =
        D₂.integer ≫ D₂.P.map z.hom ∧
      τ.hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≫
          D₂.P.map f ≫ D₂.coefficient G = E.map (D₁.coefficient F) ≫ t := by sorry

end
end AlgebraicGeometry.Scheme.Modules
