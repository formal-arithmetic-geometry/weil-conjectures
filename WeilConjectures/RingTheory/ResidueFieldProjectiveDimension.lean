/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Projective dimension of the residue field

For a Noetherian local ring whose residue field has finite projective dimension, that
projective dimension is at most the Krull dimension of the ring.

## References

* [Stacks, Tag 00OB]
-/

@[expose] public section

universe u

namespace Ring

/-- Let `(R, m)` be a Noetherian local ring. If its residue field has finite
projective dimension as an `R`-module, then that projective dimension is at most
its Krull dimension. If the Krull dimension is finite, the residue field has a
projective resolution of length at most that dimension. -/
lemma residueField_projectiveDimension_le_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R))) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤
        ringKrullDim R ∧
      ∀ D : ℕ, ringKrullDim R = (D : WithBot ℕ∞) →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of R (IsLocalRing.ResidueField R)) D := by
  have hdim : CategoryTheory.projectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) ≤ ringKrullDim R := by
    calc
      _ ≤ (IsLocalRing.depth (R := R) R : WithBot ℕ∞) :=
        residueField_projectiveDimension_le_depth R h
      _ ≤ Module.supportDim R R := IsLocalRing.depth_le_supportDim R
      _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  refine ⟨hdim, ?_⟩
  intro D hD
  have hle := (CategoryTheory.projectiveDimension_le_iff _ D).1 (hdim.trans_eq hD)
  exact (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE.{u, u} _ D).2 hle

end Ring
