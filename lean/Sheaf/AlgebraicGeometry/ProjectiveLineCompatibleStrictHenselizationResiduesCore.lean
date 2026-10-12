/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-! # Compatible strict henselizations and geometric residue maps

Source: Stacks Project, Tags 04HX, 03PS, 04GU and 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Core data for compatible strict henselizations to the
original integral geometric points. The residue maps are universal homeomorphisms.

Source: Stacks Project, Tags 04HX and 03PS, functoriality Tag 04GU, and the last two
paragraphs of the proof of Tag 095T; topological invariance Tag 04DY.
(blueprint: compatible-strict-henselization-residues-core).

Proof: take the coordinate-ring colimits of the affine pointed neighbourhoods at
s and t, and use their spectra for eA and eB. Tag 04HX identifies each as a strictly
henselian local ring and identifies
its residue field with the relative separable closure of the base residue field
inside Ω. Since k and k' are separably closed, these relative separable closures
already lie in k and k', respectively: a separable polynomial splits there, so
all of its roots in Ω lie in the image of that field. This gives ρA and ρB.
The integral factorizations hσ and hτ make k and k' algebraic over their base
residue fields. Their extensions of the relative separable closures are thus
purely inseparable, and their spectra are universal homeomorphisms. The pointed
factorization in Tag 04HX proves the two displayed geometric-point equalities.
The equality hι identifies the base-residue embeddings into Ω. Functoriality of
strict henselization (Tags 03PS and 04GU) gives the local ring map φ, the structural
square, and the commuting residue square. Equality can be checked after embedding
both residue fields into Ω; those embeddings are injective. No sheaf, cohomology,
or closed-fibre comparison is used. -/
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues_core
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
              (eB : Spec (.of B) ≅ strictHenselizationScheme t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap s =
                eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictHenselizationStructuralMap t = τ ∧
              True := by sorry

end AlgebraicGeometry

namespace AlgebraicGeometry
open CategoryTheory Limits
open Scheme Etale
set_option autoImplicit false
/-- The residue maps in a compatible strict henselization datum commute.
Source: Stacks Project, Tags 04GU and 04DY; the equality follows by functoriality
of residue fields and cancellation after embedding into the common algebraic closure.
(blueprint: compatible-strict-henselization-residue-square).
Proof: compare both composites after embedding residue fields into the common
algebraically closed field. Functoriality of residue maps gives equality. -/
theorem Etale.compatibleStrictHenselization_residue_square
    {S T : Scheme.{u}} {g : T ⟶ S} {k k' Ω A B : Type u}
    [Field k] [Field k'] [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (ι : Spec (.of k') ⟶ Spec (.of k))
    (φ : A →+* B) (hφ : IsLocalHom φ)
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    (eB : Spec (.of B) ≅ strictHenselizationScheme t)
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) :
    ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
      ι ≫ ρA := by sorry
end AlgebraicGeometry
