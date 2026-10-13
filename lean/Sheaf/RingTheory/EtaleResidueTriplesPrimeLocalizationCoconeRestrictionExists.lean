module

public import Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Existence of a compatible global cocone across prime localization.
Source: Stacks Project, Tag 04GW (pointed triples), Section 10.9 (localization
universal property), and Tag 00U2 (3) (etale base change).
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-restriction-exists)

Proof: Put A = R_p and write f_s : B_s to K for the pointing of a global triple s.
Its kernel is s.q because its residue-field map is injective. By compatibility
and hK, f_s sends the image of every element of R outside p to a nonzero element
of K. Construct C_s by localizing B_s at these images, with canonical map i_s.
It is the base change A tensor_R B_s, hence etale over A. Extend f_s by sending
b/d to f_s(b)/f_s(d). Its kernel defines a prime r_s of C_s; the induced embedding
of the fraction field of C_s/r_s into K gives its residue-field pointing.
The composite A to C_s to K is the specified algebra map: the two maps agree on
R by hK, hence on A by localization uniqueness. By hψ and injectivity of ψ its
kernel on A is q. Thus this construction gives a local triple t_s, and i_s
satisfies both equations in the compatible-leg relation.

Define the leg at s to be i_s followed by θ.app t_s. Each global-triple morphism
extends uniquely to an A-map of these localized rings; its commutation with K
follows by uniqueness of the extension to K, so it is a local-triple morphism.
Naturality of θ then proves naturality of the proposed global legs. Finally,
for any β : B_s to B_t occurring in the relation, all denominators become units
in B_t because they already are units in A. Extend β to C_s to B_t. This map is
A-linear by agreement on R and localization uniqueness, and commutes with the
pointings by agreement on B_s. It is therefore a local-triple morphism.
Naturality of θ for it gives β followed by θ.app t = i_s followed by θ.app t_s,
which is exactly the required relation. -/
theorem etaleResidueTriples_primeLocalization_cocone_restriction_exists
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V) :
    ∃ η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ := by sorry

end AlgebraicGeometry.Scheme
