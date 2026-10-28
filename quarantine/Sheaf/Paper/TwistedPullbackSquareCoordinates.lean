/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackPbcPullback
public import Sheaf.Paper.TwistedPullbackPbcTwist
public import Sheaf.Paper.TwistedPullbackShiftCoherence

/-! # Simultaneous normalized coordinates for the scalar pullback square

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
common-presentation calculation of (Z), (C), (M)
(blueprint: def-pur-twisted-pullback-square-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The normalized presentation and scalar comparisons at one scheme, simultaneously
for all finite subfields, including equal fields and the ground field.
Source: purity transport, common integral presentations
(blueprint: def-pur-twisted-pullback-square-coordinates). -/
structure CoefficientCoordinates (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))] where
  stage : ∀ R : Fields l Ω, Presentation l R.val W
  scalar : ∀ (R S : Fields l Ω) (h : R ≤ S),
    ScalarCoordinates l R.val S.val (IntermediateField.inclusion h) W (stage R) (stage S)

/-- The arbitrary-morphism pullback bridge and its scalar equation, using the same
presentation and scalar comparisons at both endpoints.
Source: purity transport, conjugation of the actual specified p
(blueprint: def-pur-twisted-pullback-square-coordinates). -/
structure ArrowCoordinates {A B : Scheme.{u}} [IsNoetherian A] [IsNoetherian B]
    [Fact (∃ n : ℕ, topologicalKrullDim A ≤ n)]
    [Fact (∀ x : A, IsUnit (l : A.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim B ≤ n)]
    [Fact (∀ y : B, IsUnit (l : B.presheaf.stalk y))]
    [∀ x : A, Invertible (l : A.residueField x)]
    [∀ y : B, Invertible (l : B.residueField y)]
    (CA : CoefficientCoordinates l Ω A) (CB : CoefficientCoordinates l Ω B)
    (h : A ⟶ B) where
  pull : ∀ R : Fields l Ω, PullCoordinates l R.val (CA.stage R) (CB.stage R) h
  scalar : ∀ (R S : Fields l Ω) (i : R ≤ S),
    PullScalarCompatible l R.val S.val (IntermediateField.inclusion i) h
      (pull R) (pull S) (CA.scalar R S i) (CB.scalar R S i)

/-- The raw PBC coordinates used in the square, including the actual PBC twists.
All comparisons are normalized inside their records, rather than arbitrary
natural isomorphisms that could rescale the equations.
Source: purity transport, common-presentation calculation of (Z), (C), (M)
(blueprint: def-pur-twisted-pullback-square-coordinates). -/
structure SquareCoordinates {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n)]
    [Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n)]
    [Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y) (d : ℕ)
    (s : ShiftCoherence l Ω u f f' v d) where
  atX : CoefficientCoordinates l Ω X
  atX' : CoefficientCoordinates l Ω X'
  atY : CoefficientCoordinates l Ω Y
  atY' : CoefficientCoordinates l Ω Y'
  alongU : ArrowCoordinates l Ω atX' atX u
  alongF : ArrowCoordinates l Ω atX atY f
  alongF' : ArrowCoordinates l Ω atX' atY' f'
  alongV : ArrowCoordinates l Ω atY' atY v
  twistX : ∀ R : Fields l Ω, TwistCoordinates l R.val X d (atX.stage R) (s.atX R)
  twistX' : ∀ R : Fields l Ω, TwistCoordinates l R.val X' d (atX'.stage R) (s.atX' R)

end WeilConjectures.TwistedPullbackScalars
