/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.MapIntoHenselianColimit

/-! # Lifting compatible residue embeddings through strict henselizations

Source: Stacks Project, Tags 04GU and 04HX.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry
open Scheme Etale

/-- Lift compatible geometric residue embeddings to a ring map of strict henselizations.
Source: Stacks Project, Tags 04GU and 04HX.
(blueprint: lem-weil-pbc-compatible-strict-henselization-residue-lift).

Proof: choose an affine open U = Spec R containing the image of σ. The closed
point of Spec B maps into U, so the entire local spectrum Spec B maps into U:
every point generalizes its closed point. This gives the base ring map R → B.
Use Scheme.etale_local_ring_triples to identify the pointed neighbourhood
colimit over U with the etale residue-triples diagram. Scheme.strictHenselization_triples
identifies its residue field with the chosen separable closure and its maximal ideal
with the pointed prime. Transport this colimit presentation along eA using full
faithfulness of Spec. Thus A is an ind-etale R-algebra with its maximal ideal over
the inverse image of the maximal ideal of B. The supplied hres, followed by the two
factorization equalities and hι, says that r respects the base residue field.
Apply Algebra.map_into_henselian_colimit (Tag 08HR, the lifting property used in
Tag 04GU) with this maximal ideal and r. Identify the prime residue fields there
with the local residue fields here. Its prescribed reduction gives the ring residue
diagram; its R-algebra compatibility gives the equality of maps to U and hence the
structural square after composing with U → S. Only φ is obtained: r and its spectral
compatibility are inputs, constructed independently by the caller. -/
theorem Etale.exists_compatibleStrictHenselizationResidueLift
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
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
    (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    (hres : ρB ≫ Spec.map (CommRingCat.ofHom r) = ι ≫ ρA) :
    ∃ (φ : A →+* B),
      (IsLocalRing.residue B).comp φ = r.comp (IsLocalRing.residue A) ∧
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g := by sorry

end AlgebraicGeometry
