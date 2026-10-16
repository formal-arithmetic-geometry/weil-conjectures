module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Category.Ring.Instances

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A compatible map that exhibits a localization is an epimorphism.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi)

The added localization hypothesis is relative to the algebra structure induced
by i, so it identifies i itself with the canonical localization map. Two ring
homomorphisms out of t.B agreeing after i agree on all fractions, by
IsLocalization.ringHom_ext. Mathlib packages this argument as IsLocalization.epi.
Compatibility alone does not imply the localization hypothesis: the pointed
diagonal from a field F to F × F is compatible but not epic.
-/
theorem etaleResidueTriples_primeLocalization_component_extension_epi
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (_hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (_hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B)
    (_hα : c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α)
    (_hφ : i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ)
    (M : Submonoid c.B)
    (hlocal : letI := i.hom.toAlgebra; IsLocalization M t.B) : Epi i := by
  let := i.hom.toAlgebra
  let : IsLocalization M t.B := hlocal
  exact IsLocalization.epi M t.B

end AlgebraicGeometry.Scheme
