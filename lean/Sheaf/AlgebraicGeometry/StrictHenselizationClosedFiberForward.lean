module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.RingTheory.StrictHenselizationTriples
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
/-- The strict henselization structural fibre over the distinguished point contains no
point other than the closed point. This is the forward half of the singleton-fibre theorem.
Source: Stacks Project, Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber-forward)
Proof: choose an affine chart Spec R around p = s(closedPoint Ω) and factor s
through it. The initial chart restriction and the pointed etale residue-triple equivalence
identify the coordinate-ring colimit C defining the strict henselization with the triple
colimit, preserving the structural R-map on every coprojection. The residue embeddings
land in the relative separable closure of κ(p) inside Ω since etale residue extensions
are finite separable (Tag 04HX). Tags 04GW and 04GP give a local colimit whose maximal
ideal is pC. The prime corresponding to e(x) contracts to p, so it contains pC and equals
that maximal ideal. Therefore e(x) is the closed point of Spec C. An isomorphism preserves
closed singletons; its inverse sends this point to the unique closed point of Spec A.
Thus x = closedPoint A. The argument includes the field case. A zero ring A cannot have
the assumed isomorphism, since C has a nonzero field quotient. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictHenselizationStructuralMap s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A := by sorry
end AlgebraicGeometry.Scheme
