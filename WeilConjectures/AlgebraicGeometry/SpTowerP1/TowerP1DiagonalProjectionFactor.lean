/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TriangleWords

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

/-- Section specialization and projection naturality for either projective-line
projection, retaining the composition source alpha_i. This holds for every M in the
comparison domain, independently of the trace or the unit/counit triangle words.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction, first arrow and its source, steps 5 and 9 of the parent node
(blueprint: lem-sp-tower-p1-diagonal-projection-factor).

Proof: apply ringedProjectionTensorComposition in the actual inverse-system ringed
topoi, with i=Delta, p=p_i and V=A_P in its section specialization. Normalize the
pullback of p_i along Delta by diagonalPull and the identity pullback in Presentation;
Operations.comp_termwise fixes this normalization before localization. The conjugate
right comparison is the inverse of sourceUnitAt. The section identity, with these
normalizations and the left and right coefficient unitors, identifies the inverse
supported projection followed by push p_i with rightUnit_M inverse and identity_M
tensor sourceUnitAt(A_P), followed by the outside-first projection at Delta_*A_P.
Projection naturality in the arrow delta:Delta_*A_P -> T_W moves delta across that
outside projection. Naturality of the recorded signed symmetry gives the same
outside-first order as diagonalInsertion and outsideProjection. The result is
rightUnit_M inverse followed by identity_M tensor (sourceUnitAt(A_P) then Rp_i(delta)),
then outsideProjection(M,T_W), exactly diagonalTensorFactor then outsideProjection.
In particular the source alpha_i is not discarded and the argument is valid for
both Bool values and for the zero object, without a Tor hypothesis. -/
theorem towerP1DiagonalProjectionFactor (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    diagonalInsertion l E h a M =
      diagonalTensorFactor l E p a M.obj ≫
        outsideProjection l E p a M.obj ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1
