module

public import Sheaf.CategoryTheory.DgModuleConeCalculus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Contraction of the composite DG cone

Source: Stacks Project, dga.tex, Tags 09KF, 09KI, 09KJ
(blueprint: lem-sfb-dg-composite-cone-contraction).

Mathlib orders cone coordinates as (x,y), rather than (y,x). Its composite-cone
maps have exactly the node's coordinates after exchanging those summands. In particular
`MappingConeCompHomotopyEquiv.inv` is r(z,x,y,t)=(z,f(x)+y) and `hom` is s(z,y)=(z,0,y,0).
The module-linear lifts and homotopy quotient below retain the DG action.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.DgAlgebra

/-- The contraction data with fixed underlying chain maps. Cone and shift action fields
are the componentwise and unchanged actions, rather than arbitrary replacement objects.
The isomorphism is of the three arrows of the triangles with identity on the first two
objects and on the common shift; thus it is an isomorphism of triangles in K_A without
assuming a triangulation or passing to the derived category.
Source: Stacks, Tags 09KF, 09KI, 09KJ
(blueprint: lem-sfb-dg-composite-cone-contraction). -/
structure CompositeConeContraction (A : Algebra.{u}) {X Y Z : RightModule A}
    (f : X ⟶ Y) (g : Y ⟶ Z) where
  coneF : ConeAction A X Y ((underlying A).map f)
  coneGF : ConeAction A X Z ((underlying A).map f ≫ (underlying A).map g)
  coneG : ConeAction A Y Z ((underlying A).map g)
  shiftF : ShiftAction A coneF.module 1
  alpha : LinearLift A coneF.module coneGF.module
    (CochainComplex.mappingConeCompTriangle ((underlying A).map f) ((underlying A).map g)).mor₁
  beta : LinearLift A coneGF.module coneG.module
    (CochainComplex.mappingConeCompTriangle ((underlying A).map f) ((underlying A).map g)).mor₂
  gamma : LinearLift A coneG.module shiftF.module
    (CochainComplex.mappingConeCompTriangle ((underlying A).map f) ((underlying A).map g)).mor₃
  coneAlpha : ConeAction A coneF.module coneGF.module
    (CochainComplex.mappingConeCompTriangle ((underlying A).map f) ((underlying A).map g)).mor₁
  inclusion : LinearLift A coneGF.module coneAlpha.module
    (CochainComplex.mappingCone.inr
      (CochainComplex.mappingConeCompTriangle ((underlying A).map f) ((underlying A).map g)).mor₁)
  connecting : LinearLift A coneAlpha.module shiftF.module
    (CochainComplex.mappingCone.triangle
      (CochainComplex.mappingConeCompTriangle
        ((underlying A).map f) ((underlying A).map g)).mor₁).mor₃
  retract : LinearLift A coneAlpha.module coneG.module
    (CochainComplex.MappingConeCompHomotopyEquiv.inv ((underlying A).map f) ((underlying A).map g))
  sectionMap : LinearLift A coneG.module coneAlpha.module
    (CochainComplex.MappingConeCompHomotopyEquiv.hom ((underlying A).map f) ((underlying A).map g))
  retract_section : linearLiftMap sectionMap ≫ linearLiftMap retract = 𝟙 _
  section_retract : homotopyRel A
    (linearLiftMap retract ≫ linearLiftMap sectionMap) (𝟙 _)
  inclusion_retract : linearLiftMap inclusion ≫ linearLiftMap retract = linearLiftMap beta
  connecting_retract :
    (homotopyQuotient A).map (linearLiftMap retract) ≫
      (homotopyQuotient A).map (linearLiftMap gamma) =
        (homotopyQuotient A).map (linearLiftMap connecting)
  triangleIso :
    mk₃ ((homotopyQuotient A).map (linearLiftMap alpha))
        ((homotopyQuotient A).map (linearLiftMap inclusion))
        ((homotopyQuotient A).map (linearLiftMap connecting)) ≅
      mk₃ ((homotopyQuotient A).map (linearLiftMap alpha))
        ((homotopyQuotient A).map (linearLiftMap beta))
        ((homotopyQuotient A).map (linearLiftMap gamma))
  identity_first : app' triangleIso.hom 0 = 𝟙 _
  identity_second : app' triangleIso.hom 1 = 𝟙 _
  third_retract : app' triangleIso.hom 2 = (homotopyQuotient A).map (linearLiftMap retract)
  identity_shift : app' triangleIso.hom 3 = 𝟙 _

/-- The iterated DG cone contracts onto C(g) with the specified r and s, inducing
an isomorphism of triangles in K_A with the first two components identities.

Proof: shifts and cones have the indicated actions because the Leibniz signs on the
shifted summands cancel. The cone differential squares to zero by the chain-map equation.
The formulas alpha(y,x)=(g(y),x), beta(z,x)=(z,f(x)) and gamma(z,y)=(-y,0) are
A-linear chain maps by the chain-map equations for f and g. On the iterated cone,
D(z,x,y,t)=(dz+gf(x)+g(y),-dx+t,-dy-f(t),dt). Substitution shows that
r(z,x,y,t)=(z,f(x)+y) and s(z,y)=(z,0,y,0) commute with D, are A-linear and satisfy
rs=1. The degree-minus-one A-linear map H(z,x,y,t)=(0,0,0,x) satisfies
DH+HD=1-sr, so its negative supplies the homotopy sr-1 used here. The second triangle
square is the strict identity r i_alpha=beta. The A-linear degree-minus-one map
J(z,x,y,t)=(0,x) into C(f)[1] satisfies dJ+JD=(-f(x),t)=gamma r-(-p_alpha).
Thus the last square commutes in K_A. The triple (1,1,[r]) is invertible with inverse
(1,1,[s]), by rs=1 and the displayed homotopy. Adding identity on the common shifted
object gives precisely the stated three-arrow isomorphism.
Source: Stacks, Tags 09KF, 09KI, 09KJ
(blueprint: lem-sfb-dg-composite-cone-contraction). -/
theorem nonempty_compositeConeContraction (A : Algebra.{u}) {X Y Z : RightModule A}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Nonempty (CompositeConeContraction A f g) := by
  sorry

end CategoryTheory.DgAlgebra
