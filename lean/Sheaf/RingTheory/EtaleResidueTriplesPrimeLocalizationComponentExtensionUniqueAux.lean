module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A fixed local pointed étale triple admits a global pointed model whose map is epic.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux)

This is the descent-and-localization part of the uniqueness proof: the global model
maps to the prescribed local triple, and its underlying ring map is an epimorphism.
-/
theorem etaleResidueTriples_primeLocalization_component_extension_unique_aux
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
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ ∧
      Epi β := by sorry

end AlgebraicGeometry.Scheme
