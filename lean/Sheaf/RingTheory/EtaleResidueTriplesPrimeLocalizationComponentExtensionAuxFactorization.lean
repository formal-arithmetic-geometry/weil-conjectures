module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/--
Cocone-leg extension and morphism-factorization part.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization)
-/
theorem etaleResidueTriples_primeLocalization_component_extension_factorization
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
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (hiα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (hiφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ) :
    ∃ b : t.B ⟶ V,
      i ≫ b = η.app c ∧
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        ∃ a : c ⟶ s,
          (etaleResidueTriplesRingDiagram R p K χ).map a ≫ β = i ∧
          ∀ (f g : s.B ⟶ V),
            (etaleResidueTriplesRingDiagram R p K χ).map a ≫ f =
              (etaleResidueTriplesRingDiagram R p K χ).map a ≫ g → f = g := by
  sorry

end AlgebraicGeometry.Scheme
