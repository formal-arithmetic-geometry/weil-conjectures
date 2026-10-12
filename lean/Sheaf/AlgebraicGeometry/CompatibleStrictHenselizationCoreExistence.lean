module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.StrictHenselization
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale
/-- The strict henselization rings and residue maps exist for the two geometric points.
Source: Stacks Project, Tags 04HX, 03PS and 04DY.
(blueprint: compatible-strict-henselization-core-existence)
Proof: take A and B to be the actual coordinate-ring colimits strictHenselizationRing
of the indicated geometric points, with eA and eB the identity spectrum isomorphisms.
By affine neighbourhood cofinality and Tag 04HX, these colimits are the strict
henselizations of the local rings at the images of σ and τ. Their residue fields are
the separable algebraic closures of the respective point residue fields inside Ω;
they are henselian local rings with separably closed residue fields. The integral
factorizations hσ and hτ identify k and k' as algebraic extensions of those point
residue fields. Since k and k' are separably closed, their embeddings into Ω contain
these separable closures. The remaining extensions are algebraic purely inseparable:
an algebraic extension of a separably closed field has no nontrivial separable part.
Take ρA and ρB to be the spectra of these residue inclusions. Purely inseparable
algebraic field extensions give integral, radicial, surjective spectrum maps, hence
universal homeomorphisms. The inclusions extend the given point residue maps, so
composition with the ring residue maps and the colimit structural maps gives σ and τ.
No ring data are chosen from a mere unproved existence assertion. -/
theorem Etale.exists_compatibleStrictHenselizationCoreExistence
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
          ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
            (eB : Spec (.of B) ≅ strictHenselizationScheme t)
            (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
            (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
            IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
            ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
              eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
            ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
              eB.hom ≫ strictHenselizationStructuralMap t = τ := by sorry
end AlgebraicGeometry
