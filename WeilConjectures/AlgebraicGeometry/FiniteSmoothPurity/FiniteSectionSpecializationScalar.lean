/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionSpecializationScalarCanonical
import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.FiniteSectionFamilyConstancy

/-! # Scalar compatibility of normalized zero-fibre specialization

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and general-ring proof (2), Steps 4--7.
(blueprint: lem-sp-finite-section-specialization-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Zero-fibre specialization commutes with derived change of finite coefficients.
The annihilator is shared; this statement has no Tate exponent or integration factor.
Source: sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation, and
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2), Steps 4--7.
(blueprint: lem-sp-finite-section-specialization-scalar).

Proof: the scalar/base-change square for the Rees projection gives the coefficient
squares at one and zero. Both coefficient rings are killed by N, since the image of
N in B is the image of its zero value in A. Finite-family constancy makes each family
the pullback of its section invariant through its supplied normalized isomorphism.
Etale locally the invariants are shifted free rank-one modules. Derived scalar
extension of these flat models is the corresponding free B-model, without a flatness
hypothesis on B over A. Thus the two family maps, one obtained by extending kappa_A
and the other by kappa_B after the exceptional coefficient map, are maps between
pullbacks of shifted locally constant B-sheaves. After trivializing both sheaves,
their difference is a locally constant matrix along each geometric affine-line
fibre. Each such fibre is connected and meets the section one. The one-fibre
coefficient square and both normalization equations make this difference zero at
one, hence on every fibre and globally. Apply zero restriction to this family
identity, use the zero-fibre coefficient square, and cancel the zero restrictions
of both kappas and the scalar/pullback section compositors. This yields the displayed
square for the specified specialization maps. For an empty base or zero ring all
maps are unique; rank zero is included in the same shifted-sheaf calculation. -/
theorem finiteSectionSpecialization_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family B g s ≅
      (ordinaryFinitePullback B (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant B g s))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized B g s hs κ') :
    (scalarExtension φ S).map (NoetherianSectionSpecialization.specialization A g s κ) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ
          (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection =
      WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
        NoetherianSectionSpecialization.specialization B g s κ' := by
  obtain ⟨κB, hκB, htransport⟩ :=
    finiteSectionSpecialization_scalar_canonical φ N hN hA d g s hs hS κ hκ
  have huniq :=
    (NoetherianSectionSpecialization.finite_family_constancy B N hN
      (by rw [← map_natCast φ, hA, map_zero]) hS d g s hs).2.2
  have heq : κB = κ' := huniq.unique hκB hκ'
  simpa [heq] using htransport.symm

end AlgebraicGeometry.Etale.FiniteSmoothPurity
