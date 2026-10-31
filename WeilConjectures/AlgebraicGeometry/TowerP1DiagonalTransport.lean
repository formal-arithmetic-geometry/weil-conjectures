/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1TriangleWords

/-! # Internal reordering for projective-line tower triangles

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities (blueprint: lem-sp-tower-p1-triangle-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Transport of the initial supported diagonal word through direct-image composition
and through the pullback square on GK. These equations concern only the insertion;
there is no trace, epsilon, triangle composite, or scalar in their conclusions.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction, source comparisons, steps 5 and 9 of the parent node
(blueprint: lem-sp-tower-p1-diagonal-transport).

Proof: the sourceUnit and sourceUnitAt maps are the composite adjunction units for
p_i Delta=identity, formed using the specified diagonalPull comparison. For the
first equation, paste the q/p_i pullback squares with the section square of Delta.
The two pasted pullback comparisons agree by the termwise composition normalization
in Operations.comp_termwise and the ordinary inverse-image composition law. Their
right conjugates agree by mate pasting, giving the source comparison after pushSwap.
Naturality of this conjugate for the inverse diagonal projection, delta tensor
identity, and the symmetry moves pushSwap to the end of the insertion, yielding
the first equation. For the second, restrict rightPullComparison along Delta.
Both p_i Delta are the specified identity. Its q*K factor is identity by the same
pasting law, and its line factor is identity because line1Iso was defined from the
same square and line2Iso. Therefore inverse supported projection for p1 and for p2
is intertwined by tensoring with rightPullComparison. Projection naturality and
symmetry naturality move that tensor map across delta tensor identity, leaving
exactly sourceUnitAt true and diagonalProjectionInverse true. This proves the
second equation. All identities are in the tower derived category; the argument
uses ordinary sheaf normalization before localization, never faithfulness of
evaluation on arbitrary derived morphisms. -/
theorem towerP1DiagonalTransport (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) :
    (∀ M : C l E p.classes.base (ProjectiveLine S),
      (p.F l E).map (unitInsertion l E d M) ≫
        (p.pushSwap l E).hom.app
          ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).obj
            ((SpTowerShriek.pull l E p.classes.base
              (p.operations.geometry (pullback.fst _ _))).obj M.obj,
              (line l E p.classes.chernW)⟦(2 : ℤ)⟧)) =
      (p.F l E).map (diagonalInsertion l E h false M)) ∧
    (∀ K : C l E p.classes.base S,
      unitInsertion l E d ((rightRestricted l E d).obj K) ≫
        (SpTowerShriek.push l E p.classes.base
          (p.operations.geometry (pullback.snd _ _))).map
            ((SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
              (Prod.mkHom (rightPullComparison l E p K.obj).hom (𝟙 _))) =
      diagonalInsertion l E h true ((rightRestricted l E d).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1
