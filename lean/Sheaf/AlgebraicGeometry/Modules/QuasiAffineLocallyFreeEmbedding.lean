/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasiAffineFiniteFreeQuotient
import Sheaf.AlgebraicGeometry.Modules.DualFiniteFreeQuotientEmbedding

/-! # Universal finite free embeddings on Noetherian affine opens

Source: Stacks Project, Tag 0EKP, the dual-surjection construction in (2) to (3).
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an open of a Noetherian affine scheme embeds into
finite free with finite locally free cokernel, and this embedding remains mono after
arbitrary scheme pullback.

Source: Stacks Project, Tag 0EKP, first dual-surjection construction in (2) to (3),
with the ample invertible module equal to the structure sheaf.
(blueprint: new-sbc-quasi-affine-locally-free-embedding)

Proof: The open is quasi-compact and quasi-affine, so its structure sheaf is ample.
The dual of M is finite locally free, hence finite type. Choose a finite cover by
principal affine opens in Spec R, contained in V, on which the dual is free. Clear
denominators for each basis section, using the structure sheaf as the invertible
module. The multiplying function is invertible on its principal open, so these
extended sections still generate there. All these finitely many global sections
give a surjection from a finite free sheaf onto the dual.
On a neighbourhood where the dual is free this surjection splits, since the finite
free target is projective. Dualizing, and using finite locally free biduality, gives
an embedding M into finite free. Its cokernel is locally the dual of the kernel of
the split surjection. That kernel is a finitely generated projective summand on
each affine trivializing neighbourhood, and is locally free after shrinking. Locally
this embedding is the inclusion of a direct summand. Every pullback preserves that splitting
and therefore
its injectivity. Rank zero, empty opens and varying ranks require no positive-rank
hypothesis. -/
theorem exists_universally_mono_free
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (M : V.toScheme.Modules) [M.IsFiniteLocallyFree] :
    ∃ (r : ℕ) (α : M ⟶ free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))),
      Mono α ∧ (cokernel α).IsFiniteLocallyFree ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ V.toScheme), Mono ((Modules.pullback g).map α) := by
  have := IsFiniteLocallyFree.dual M
  obtain ⟨r, β, hβ⟩ := exists_epi_free_of_isFiniteLocallyFree V (dual M)
  have : Epi β := hβ
  refine ⟨r, SheafOfModules.bidual (R := V.toScheme.sheaf) M ≫ dualMap β ≫
    (SheafOfModules.homObjFreeUnitIso (R := V.toScheme.sheaf) (ULift.{u} (Fin r))).hom, ?_⟩
  exact dual_free_quotient_embedding M β

end AlgebraicGeometry.Scheme.Modules
