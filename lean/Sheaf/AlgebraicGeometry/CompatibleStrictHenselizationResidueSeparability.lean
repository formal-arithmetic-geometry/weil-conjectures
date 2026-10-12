module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/- STATEMENT-DISPUTED: the arbitrary Algebra (IsLocalRing.ResidueField B) k' is not
required to have algebraMap equal to (Spec.preimage ρB).hom. The conclusion can therefore
use a different embedding from all the geometric hypotheses. For an algebraically closed
field F of positive transcendence degree and an algebraically closed extension L, choose
embeddings b, a : F →+* L such that a(x) is transcendental over b(F). Take S = T = Spec F,
A = B = F, k = k' = Ω = L, g = ι = ν = identity, and σ = τ = Spec.map a. The strict
henselizations are F, and ρA = ρB are induced by a after the canonical residue-field
identification. All geometric hypotheses hold. Use b for the displayed Algebra instance;
the conclusion falsely asserts that a(x) is separable over b(F). See report.md for the
construction and a compiled algebraic counterexample. No signature has been changed. -/

/-- The residue-field element induced by a compatible strict-henselization
point is separable over the second residue field.  This is the residue-field
comparison step from Stacks Tags 04HX and 095T; it is isolated here so that
the polynomial conclusion can be obtained independently by a minimal-polynomial
argument.

(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-separability)

Proof: identify the residue fields of the strict henselizations with the separable closures
arising from pointed etale-neighbourhood colimits, transport these identifications
through eA and eB,
and use hι, hρA, and hρB to identify the displayed residue-field image with
the corresponding
element in the separable extension. -/
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k'] :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x) := by
  sorry

end AlgebraicGeometry
