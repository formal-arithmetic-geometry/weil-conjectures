module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The descended compatible map is an epimorphism.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi)

The localization model produced by finite-presentation descent identifies the target
with a localization of the descended affine algebra.  Hence its canonical map is
an epimorphism; this is the standard localization epimorphism argument.
-/
theorem etaleResidueTriples_primeLocalization_component_extension_epi
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
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (hα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (hφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ) : Epi i := by
  sorry

end AlgebraicGeometry.Scheme
