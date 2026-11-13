/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore

/-! # Compatible strict henselizations and geometric residue maps

## References

* Stacks Project, Tags 04HX, 03PS, 04GU and 095T.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Compatible strict henselizations have compatible residue-field maps to the
original integral geometric points. The residue maps are universal homeomorphisms
(Stacks, Tags 04HX, 03PS, 04GU, 095T). -/
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues
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
            ∃ (eA : Spec (.of A) ≅ strictLocalization s)
              (eB : Spec (.of B) ≅ strictLocalization t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
                ι ≫ ρA := by
  dsimp
  obtain ⟨A, B, cA, cB, hA, hB, sA, sB, φ, hφ, eA, eB, ρA, ρB,
      hUA, hUB, hbase, hρA, hρB, _⟩ :=
    Etale.projectiveLine_compatibleStrictHenselizationResidues_core σ τ ι hι hσ hτ ν
  letI := cA
  letI := cB
  letI := hA
  letI := hB
  letI := sA
  letI := sB
  obtain ⟨ψ, hψ, hbase', hres⟩ :=
    Etale.compatibleStrictHenselization_residue_square
      σ τ ι hι ν eA eB ρA ρB hρA hρB
  exact ⟨A, B, cA, cB, hA, hB, sA, sB, ψ, hψ, eA, eB, ρA, ρB,
    hUA, hUB, hbase', hρA, hρB, hres⟩

end AlgebraicGeometry
