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

Proof: Write A = R_p and S = R minus p. Descend the finitely presented etale
A-algebra t.B to an etale algebra over R_s for some s in S (01ZM, 07RP).
The affine-limit theorem (01Z6) supplies an affine descended model C after
enlarging s. Since R_s is etale over R, C is etale over R. The base-change
identification makes t.B the localization of C at the image of S, with map i.
Restrict the pointing t.B → K along i. Its prime kernel defines the point of
Spec C; the induced injection from C modulo that kernel into K extends to the
fraction field, giving its residue-field pointing. The equations hψ and hK
ensure this point lies over p and its pointing is compatible with χ. Thus C
and its pointing form the required triple. Its map i satisfies both displayed
equations and is epic by localization extensionality. It is essential to retain
this localization property during descent; an arbitrary compatible model is
insufficient.
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
      Epi β := by
  sorry

end AlgebraicGeometry.Scheme
