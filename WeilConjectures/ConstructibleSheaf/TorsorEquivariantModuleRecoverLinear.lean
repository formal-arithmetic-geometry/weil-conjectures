/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleRecoverLinearDiagonal
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModulePointwiseFromDiagonal

/-!
# Linear recovery for equivariant section transformations

## Implementation details

The linear map is first recovered from diagonal values over the torsor object `c.P`, where
connectedness makes equivariant sections constant on the diagonal; the pointwise formula is
then propagated to every étale object by naturality.

## References

* [Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- A natural transformation of equivariant section presheaves acts pointwise
by a unique linear map when the total space of the torsor is connected. -/
theorem equivariantModulePresheaf_recoverLinear
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N') :
    ∃! f : N.V →ₗ[ZMod ℓ] N'.V,
      ∀ (W : V.Etale) (s : c.equivariantSections ℓ N W) (x : c.sectionSpace W),
        (η.app (op W) s).val x = f (s.val x) := by
  let := c.etale
  obtain ⟨f, hf, huniq⟩ := c.equivariantModulePresheaf_recoverLinear_diagonal ℓ N N' η
  refine ⟨f, c.equivariantModulePresheaf_pointwise_of_diagonal ℓ N N' η f hf, ?_⟩
  intro g hg
  apply huniq g
  intro s x
  exact hg (Etale.mk c.π) s
    ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)

end AlgebraicGeometry.Scheme.GaloisCover
