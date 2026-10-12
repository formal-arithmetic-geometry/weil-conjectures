module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A nonempty smooth geometrically connected family over a normal integral base
has normal integral total space and generic fibre.

Source: Stacks Project, Tags 034F, 056T and 01UA.
(blueprint: lem-sbc-smooth-connected-generic-geometry-core)

Proof: Since S is integral its local rings are domains, and hS makes them normal.
Normality ascends through smooth morphisms (034F), so all local rings of C are
integrally closed domains. Smoothness is open (01UA), and the nonempty image of
C therefore contains the generic point of S. Thus the cartesian generic fibre
Cη is nonempty. Base change preserves smoothness and geometric connectedness,
so Cη is smooth and connected over K(S). Smooth schemes over a field are
locally noetherian and regular, hence normal and reduced (056T). In a locally
noetherian normal scheme, the irreducible components are disjoint and open:
on an affine normal noetherian chart the finitely many minimal primes give
disjoint components, because each local ring is a domain. Connectedness
therefore leaves just one component, so Cη is irreducible and integral.
For every nonempty open U of C, c(U) is a nonempty open of S containing its
generic point. The pullback has a point above a compatible pair of points,
so U meets j(Cη). Hence j has dense image. Its source is irreducible, so C
is irreducible. Its normal local rings imply reducedness; together with
nonemptiness this proves integrality of C. The normality already proved for
C and Cη supplies the two remaining conclusions. No noetherian hypothesis
on S or C is used: only Cη, being smooth over a field, is locally noetherian. -/
theorem smooth_connected_generic_geometry_core {S C : Scheme.{u}} [IsIntegral S]
    [Nonempty C] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ hC : IsIntegral C, letI := hC;
      ∃ hη : IsIntegral Cη, letI := hη;
        (∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) ∧
        (∀ x : Cη, IsIntegrallyClosed (Cη.presheaf.stalk x)) := by sorry

end AlgebraicGeometry.Scheme
