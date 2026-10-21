/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-! Derived universal properties of normalized supported scalar maps.
Source: Stacks Project, Tags 03QP, 03Q1 and 06YY
(blueprint: lem-asd-supported-kummer-scalar-derived-units). -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The normalized coefficient maps give the three derived scalar-extension units.
Source: Stacks Project, etale-cohomology Tag 03QP (finite direct image) and Tag 03Q1
(stalks of inverse image), and sites-cohomology Tag 06YY (derived change of rings).
(blueprint: lem-asd-supported-kummer-scalar-derived-units).

Proof: Write Λ = R. A closed immersion is finite. Its geometric fibre
is empty or a singleton, so the finite-stalk formula identifies (i_*Λ_D)_t with Λ
on D and zero off D, compatibly with the coefficient map fixed by hD. The same
formula holds for A. Finite direct image is exact, including for module sheaves,
so the degree-zero objects compute the derived direct images.

The single complexes Λ_D, Λ_T and i_*Λ_D are K-flat: for an acyclic complex C,
its tensor with each of them has stalk C_t, or zero off D. Tensor-stalk compatibility
identifies the differentials too. The tensor over the constant ring sheaf has the
same stalks as the tensor over Λ, since the stalk of the constant ring sheaf is Λ
and filtered colimits commute with tensor. Exact and conservative geometric stalks
therefore detect the required acyclicity.

Construct (i_*Λ_D) tensor A_T → i_*A_D by s tensor a ↦ ηD(s) times the restriction
of a. It is balanced and compatible with restrictions. On D its stalk is the
canonical isomorphism Λ tensor A → A; off D both sides vanish. Conservativity
makes it an isomorphism. The same construction applies to constants on D and T.
Compute derived change of rings by the identity K-flat resolutions above. Its
adjunction supplies the three universal properties against every unbounded test
complex. The generator equations hD and hT identify the ordinary units with the
specified coefficient maps, so these are the required normalized universal arrows.
No coefficient-flatness assumption is used; empty support and zero rings are included. -/
theorem supported_kummer_scalar_derived_units
    (T : Scheme.{u}) (R A : Type (u + 1)) [CommRing R] [CommRing A] (φ : R →+* A)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (ηD : ordinaryFiniteConstant (R) D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant A D))
    (ηT : ordinaryFiniteConstant (R) T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant A T))
    (hD : ∀ (U : D.Etaleᵒᵖ) (r : R),
      ηD.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of (R) (R)))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app U (φ r))
    (hT : ∀ (U : T.Etaleᵒᵖ) (r : R),
      ηT.hom.app U
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of (R) (R)))).app U r) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app U (φ r)) :
    SupportedDerivedScalarUnit φ D
        (ordinaryFiniteConstant (R) D)
        (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit φ T
        ((lowerStar (ModuleCat.{u + 1} (R)) i).obj
          (ordinaryFiniteConstant (R) D))
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        ((lowerStar (ModuleCat.{u + 1} (R)) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit φ T
        (ordinaryFiniteConstant (R) T)
        (ordinaryFiniteConstant A T) ηT := by
  sorry
end AlgebraicGeometry.Etale
