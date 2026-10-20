module

public import WeilConjectures.RingTheory.IsStrictHenselization
import Sheaf.RingTheory.PointedEtaleQuotientFinal

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Base-change of the pointed etale colimit along a surjective local quotient.
Source: Stacks Project, Tag 05WS.
(blueprint: lem-sbc-strict-henselization-surjective-quotient-core)

The quotient action is constructed, rather than quantified arbitrarily. Apply extension
of scalars to the universal cocone for C. It preserves colimits because pushout is a
left adjoint. Transport the cocone along the natural diagram isomorphism supplied by
pointedEtaleQuotient_final and extend it along the final functor. The resulting universal
cocone has the same vertex. The proved quotientBaseChange_obj_iso identifies that vertex
with C/IC, equipped with the action induced by the surjection. -/
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (_hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C)) := by
  obtain ⟨c, ⟨hc⟩, ⟨e⟩⟩ := hC
  obtain ⟨F, hF, ⟨α⟩⟩ := pointedEtaleQuotient_final A K B L π hπ
  have : F.Final := hF
  let t := (Cocone.precompose α.inv).obj ((quotientBaseChange π).mapCocone c)
  have ht : IsColimit t :=
    (IsColimit.precomposeInvEquiv α _).symm
      (isColimitOfPreserves (quotientBaseChange π) hc)
  let d := (Functor.Final.extendCocone (F := F)).obj t
  have hd : IsColimit d := (Functor.Final.isColimitExtendCoconeEquiv F t).symm ht
  obtain ⟨qB, ⟨eq⟩⟩ := quotientBaseChange_obj_iso A B C π hπ I hker
  let : Algebra B (C ⧸ I.map (algebraMap A C)) := qB
  refine ⟨qB, d, ⟨hd⟩, ⟨?_⟩⟩
  exact (quotientBaseChange π).mapIso e ≪≫ eq

end Algebra
