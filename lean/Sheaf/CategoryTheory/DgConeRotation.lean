module

public import Sheaf.CategoryTheory.DgModuleConeCalculus

/-!
# Both rotations of a DG cone triangle

Source: Stacks Project, dga.tex, Tags 09KB, 09KC, 09KF and 09KH
(blueprint: lem-sfb-dg-cone-rotation).

Mathlib orders cone coordinates as (x,y), while the source orders them as (y,x).
Its third triangle map is already the negative projection. The forward maps below
are the fixed ordinary chain maps q(y,x,y')=-x and s(x)=(0,-x,f(x)), lifted to
right DG module maps. Three-arrow isomorphisms in the actual DG homotopy quotient
express triangle isomorphisms with identity also on the common shifted vertex.
This avoids assuming a triangulation in the very lemma used to construct it.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.DgAlgebra

/-- The two signed cone rotations, retaining the right DG action and its homotopies.
Every action is on the specified ordinary complex and is pinned by the unchanged
shift action or the two cone projections. Every lifted forward map is a fixed
chain map, so q and s have the stated coordinates, rather than being arbitrary
homotopy equivalences. The inverse rotation uses the canonical cancellation of
opposite shifts to interpret p[-1] and the last inclusion.
Source: Stacks, dga.tex, Tags 09KB, 09KC, 09KF and 09KH
(blueprint: lem-sfb-dg-cone-rotation). -/
structure ConeRotation (A : Algebra.{u}) {X Y : RightModule A} (f : X ⟶ Y) where
  coneF : ConeAction A X Y ((underlying A).map f)
  shiftX : ShiftAction A X 1
  shiftY : ShiftAction A Y 1
  inclusion : LinearLift A Y coneF.module
    (CochainComplex.mappingCone.inr ((underlying A).map f))
  connecting : LinearLift A coneF.module shiftX.module
    (CochainComplex.mappingCone.triangle ((underlying A).map f)).mor₃
  negativeShiftF : LinearLift A shiftX.module shiftY.module
    (-((underlying A).map f)⟦(1 : ℤ)⟧')
  coneInclusion : ConeAction A Y coneF.module
    (CochainComplex.mappingCone.inr ((underlying A).map f))
  iteratedInclusion : LinearLift A coneF.module coneInclusion.module
    (CochainComplex.mappingCone.inr
      (CochainComplex.mappingCone.inr ((underlying A).map f)))
  iteratedConnecting : LinearLift A coneInclusion.module shiftY.module
    (CochainComplex.mappingCone.triangle
      (CochainComplex.mappingCone.inr ((underlying A).map f))).mor₃
  retract : LinearLift A coneInclusion.module shiftX.module
    (CochainComplex.mappingCone.rotateHomotopyEquiv ((underlying A).map f)).inv
  sectionMap : LinearLift A shiftX.module coneInclusion.module
    (CochainComplex.mappingCone.rotateHomotopyEquiv ((underlying A).map f)).hom
  retract_section : linearLiftMap sectionMap ≫ linearLiftMap retract = 𝟙 _
  section_retract : homotopyRel A
    (linearLiftMap retract ≫ linearLiftMap sectionMap) (𝟙 _)
  inclusion_retract :
    linearLiftMap iteratedInclusion ≫ linearLiftMap retract = linearLiftMap connecting
  section_connecting :
    linearLiftMap sectionMap ≫ linearLiftMap iteratedConnecting = linearLiftMap negativeShiftF
  forwardIso :
    mk₃ ((homotopyQuotient A).map (linearLiftMap inclusion))
        ((homotopyQuotient A).map (linearLiftMap iteratedInclusion))
        ((homotopyQuotient A).map (linearLiftMap iteratedConnecting)) ≅
      mk₃ ((homotopyQuotient A).map (linearLiftMap inclusion))
        ((homotopyQuotient A).map (linearLiftMap connecting))
        ((homotopyQuotient A).map (linearLiftMap negativeShiftF))
  forward_first : app' forwardIso.hom 0 = 𝟙 _
  forward_second : app' forwardIso.hom 1 = 𝟙 _
  forward_third : app' forwardIso.hom 2 = (homotopyQuotient A).map (linearLiftMap retract)
  forward_shift : app' forwardIso.hom 3 = 𝟙 _
  shiftCone : ShiftAction A coneF.module (-1)
  inverseFirst : shiftCone.module ⟶ X
  inverseFirst_formula : (underlying A).map inverseFirst =
    (-(CochainComplex.mappingCone.triangle ((underlying A).map f)).mor₃)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId Complex.{u} (1 : ℤ) (-1) (by decide)).hom.app
        ((underlying A).obj X)
  coneInverseFirst : ConeAction A shiftCone.module X ((underlying A).map inverseFirst)
  shiftShiftCone : ShiftAction A shiftCone.module 1
  inverseInclusion : LinearLift A X coneInverseFirst.module
    (CochainComplex.mappingCone.inr ((underlying A).map inverseFirst))
  inverseConnecting : LinearLift A coneInverseFirst.module shiftShiftCone.module
    (CochainComplex.mappingCone.triangle ((underlying A).map inverseFirst)).mor₃
  inverseLast : Y ⟶ shiftShiftCone.module
  inverseLast_formula : (underlying A).map inverseLast =
    CochainComplex.mappingCone.inr ((underlying A).map f) ≫
      (shiftFunctorCompIsoId Complex.{u} (-1 : ℤ) 1 (by decide)).inv.app
        ((underlying A).obj coneF.module)
  inverseIso :
    mk₃ ((homotopyQuotient A).map inverseFirst)
        ((homotopyQuotient A).map (linearLiftMap inverseInclusion))
        ((homotopyQuotient A).map (linearLiftMap inverseConnecting)) ≅
      mk₃ ((homotopyQuotient A).map inverseFirst)
        ((homotopyQuotient A).map f)
        ((homotopyQuotient A).map inverseLast)
  inverse_first : app' inverseIso.hom 0 = 𝟙 _
  inverse_second : app' inverseIso.hom 1 = 𝟙 _
  inverse_shift : app' inverseIso.hom 3 = 𝟙 _

/-- Both rotations of every right DG module cone triangle are cone triangles up to
A-linear homotopy, with identity components on their first two objects. The forward
contraction is the specified q and s, with qs=1 and the two strict triangle identities.

Proof: the unchanged shift action satisfies the DG Leibniz rule since the two shift
signs cancel; the componentwise cone action satisfies it in each coordinate, and
the square of its differential is zero by the chain-map equation for f.
Writing E=C(i_f) in source coordinates (y,x,y'), its differential is
D(y,x,y')=(d_Y y+f(x)+y',-d_X x,-d_Y y'). The prescribed q=-x and
s(x)=(0,-x,f(x)) are additive, A-linear and commute with the differentials.
They satisfy qs=1 and sq(y,x,y')=(0,x,-f(x)). The A-linear degree-minus-one
map H(y,x,y')=(0,0,y) has DH+HD=1-sq; use -H for sq-1. Direct substitution
gives q i_{i_f}=-p_f and (-p_{i_f})s=-f[1]. For the remaining square,
J(y,x,y')=-y into Y[1] has dJ+JD=-f(x)-y'=(-p_{i_f})-(-f[1])q.
Consequently (1,1,[q],1) is the forward three-arrow isomorphism, with inverse
(1,1,[s],1); its last square also follows by cancelling the inverse maps.
For inverse rotation put U=C(f)[-1], g=p_f[-1] and F=C(g), with coordinates
(u,y,x) and differential D'(u,y,x)=(d_X u+x,d_Y y+f(x),-d_X x).
The A-linear chain maps r(u,y,x)=f(u)-y and t(y)=(0,-y,0) satisfy rt=1.
For H'(u,y,x)=(0,0,u), D'H'+H'D'=1-tr. Also r i_g=f and
(-p_g)t=i_f after the canonical identification U[1]=C(f).
The A-linear homotopy J'(u,y,x)=(0,-u) into C(f) has
 dJ'+J'D'=(-f(u),-x)=(-p_g)-i_f r. Thus (1,1,[r],1) and
(1,1,[t],1) give the inverse-rotation three-arrow isomorphism. All homotopies
are right A-linear with no sign in their linearity condition. No A-linearity
of the differential is assumed. These are precisely the six coordinate steps
of the DAG proof; all are elementary and require no other theorem node.
Source: Stacks, dga.tex, Tags 09KB, 09KC, 09KF and 09KH
(blueprint: lem-sfb-dg-cone-rotation). -/
theorem nonempty_coneRotation (A : Algebra.{u}) {X Y : RightModule A} (f : X ⟶ Y) :
    Nonempty (ConeRotation A f) := by
  sorry

end CategoryTheory.DgAlgebra
