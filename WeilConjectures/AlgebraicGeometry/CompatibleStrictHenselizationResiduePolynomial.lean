/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomialCore
import WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Separable polynomials for compatible strict-henselization residues

Source: Stacks Project, Tags 04HX and 095T.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/-- Each image element of the first strict-henselization residue field satisfies a
nonzero separable polynomial with coefficients in the second residue field.
Source: Stacks Project, Tag 04HX and the residue-field inclusion argument of Tag 095T. -/
theorem Etale.compatibleStrictHenselization_residue_separable_polynomial
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ) :
    ∀ x : IsLocalRing.ResidueField A,
      ∃ p : Polynomial (IsLocalRing.ResidueField B),
        p ≠ 0 ∧ p.Separable ∧
          p.eval₂ (Spec.preimage ρB).hom ((Spec.preimage (ι ≫ ρA)).hom x) = 0 := by
  let algebra : Algebra (IsLocalRing.ResidueField B) k' :=
    (Spec.preimage ρB).hom.toAlgebra
  have hs := Etale.compatibleStrictHenselization_residue_isSeparable
    σ τ ι hι ν eA eB ρA ρB hρA hρB rfl
  intro x
  exact @exists_separable_polynomial_of_isSeparable _ _ _ _ algebra
    (Spec.preimage ρB).hom rfl _ (hs x)

end AlgebraicGeometry
