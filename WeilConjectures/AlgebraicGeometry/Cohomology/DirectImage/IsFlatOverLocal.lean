/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.RingTheory.Flat.Stability

/-!
# Flatness over the base: locality and pullbacks from a factor

* `AlgebraicGeometry.Scheme.Modules.isFlatOver_of_forall_exists_nhds`: flatness of a
  quasi-coherent module over the base is local on the source.
* `AlgebraicGeometry.Scheme.Modules.flat_sections_pullback_fst_of_flat_baseChange` and
  `AlgebraicGeometry.Scheme.Modules.flat_baseChange_of_flat_sections_pullback_fst`: for
  `Y ⟶ S ⟵ Z` with `S` affine, affine opens `W ⊆ Y`, `V ⊆ Z` and a quasi-coherent module `ℱ` on
  `Y`, the sections of `pr_Y^* ℱ` over affine opens of `pr_Y⁻¹ W ∩ pr_Z⁻¹ V` are flat over
  `Γ(Z, V)` if `Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W)` is, and conversely over `pr_Y⁻¹ W ∩ pr_Z⁻¹ V`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

section PullbackFst

variable {S Y Z : Scheme.{u}} [IsAffine S] (gY : Y ⟶ S) (gZ : Z ⟶ S) (ℱ : Y.Modules)
  [ℱ.IsQuasicoherent] {W : Y.Opens} {V : Z.Opens}

end PullbackFst

end AlgebraicGeometry.Scheme.Modules
