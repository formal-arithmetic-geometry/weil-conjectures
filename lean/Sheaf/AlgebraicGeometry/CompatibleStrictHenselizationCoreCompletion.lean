module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
/-- Functoriality between affine presentations of compatible strict henselizations.
Source: Stacks Project, Tag 04GU. (blueprint: compatible-strict-henselization-core-completion)

Proof: the equality of geometric points gives the functor from pointed etale neighbourhoods
of S to those of T by base change. Its maps to the two colimits induce the morphism from
strictHenselizationScheme t to strictHenselizationScheme s over g. Transport through eA and
eB, then use the fully faithful contravariant Spec functor to obtain the ring homomorphism.
On closed points this sends the selected geometric point to the selected geometric point;
the corresponding map of local rings is local. The colimit cone compatibility gives the
structural equality. -/
theorem Etale.exists_compatibleStrictHenselizationCoreCompletion
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω A B : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [CommRing B] [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g)
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    (eB : Spec (.of B) ≅ strictHenselizationScheme t) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictHenselizationStructuralMap s =
        eB.hom ≫ strictHenselizationStructuralMap t ≫ g := by sorry
end AlgebraicGeometry
