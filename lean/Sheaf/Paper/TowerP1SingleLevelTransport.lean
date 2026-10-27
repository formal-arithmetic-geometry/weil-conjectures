/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.TowerP1SingleLevelData

/-! # Evaluated projective-line triangle words

Source: the Levels argument of det-sp-tower-p1-adjunction, steps 1--3 of
lem-sp-tower-p1-single-level-triangles.
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
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]


/-- Unconditional commuting squares for the two composite triangle words.
This compares specified composites; neither tower composite is assumed to be an
identity. In particular this statement does not assert a triangle identity.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels;
lem-sp-tower-p1-single-level-triangles, steps 3--4.
(blueprint: lem-sp-tower-p1-single-level-transport).

Proof: For the first square use formulas.eta on projective.J L with its retained
origin. Apply the canonical direct-image word comparison, whose naturality in
the input arrow identifies evaluation of F eta with the finite F_n eta_n.
Use formulas.epsilon on F(projective.J L), retaining the etale origin F_n L
specified by the direct-image comparison. Naturality in the origin isomorphism
identifies this formula with epsilon_n at F_n L. Compose these squares.
The intermediate comparison and its inverse cancel. The outer comparison is
push.hom.app L by push_eq. For the second square use formulas.epsilon on base.J H
and then its pullback-line-tensor word. Naturality of exact pullback, tensor and
shift identifies evaluation of G epsilon with G_n epsilon_n. Apply formulas.eta
on G(base.J H), using its retained origin G_n H, and compose. The intermediate
comparisons cancel and pull_eq fixes the outer comparison. All inverses here
are the inverses of the recorded comparison isomorphisms, not new choices.
Associativity and functoriality of evaluation give the displayed equations.
The same comparison theorem supplies boundedness of all iterated inputs, so
its canonical direct-image mate is used only on its stated domain. -/
theorem singleLevelTransport (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : Presentation l E S hS) (d : Maps l E p) (h : EtaleOriginComparisons l E p d)
    (c : SingleLevelComparisons l E n d h) :
    (∀ L : DerivedCategory.Plus
        (Sheaf (ProjectiveLine S).smallEtaleTopology
          (ModuleCat.{u + 1} (levelRing l E n))),
      (nu l E n S).map
          ((singleLevelF l E n S).map
              (singleLevelEta l E n c.coordinates h.cartier_diagonal L.obj) ≫
            singleLevelEpsilon l E n c.coordinates ((singleLevelF l E n S).obj L.obj)) ≫
        c.push.hom.app L =
      c.push.hom.app L ≫ (SpTowerShriek.Ev l E S n).map
        ((p.F l E).map (eta l E d ((c.projective.J l E n).obj L)) ≫
          epsilon l E d ((left l E d).obj ((c.projective.J l E n).obj L)))) ∧
    (∀ H : DerivedCategory.Plus
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))),
      (nu l E n (ProjectiveLine S)).map
          (singleLevelEta l E n c.coordinates h.cartier_diagonal
              ((singleLevelG l E n S).obj H.obj) ≫
            (singleLevelG l E n S).map (singleLevelEpsilon l E n c.coordinates H.obj)) ≫
        c.pull.hom.app H =
      c.pull.hom.app H ≫ (SpTowerShriek.Ev l E (ProjectiveLine S) n).map
        (eta l E d ((rightRestricted l E d).obj ((c.base.J l E n).obj H)) ≫
          (p.G l E).map (epsilon l E d ((c.base.J l E n).obj H)))) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
