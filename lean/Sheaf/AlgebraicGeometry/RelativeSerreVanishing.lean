/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import Sheaf.AlgebraicGeometry.CoherentSerreVanishing
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective

/-!
# Relative Serre vanishing

Source: Stacks Project, Cohomology of Schemes, Tag 02O1, lemma-kill-by-twisting
(blueprint: lem-pc-relative-kill-by-twisting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Higher direct images of a coherent quasi-coherent module vanish after sufficiently
large twists by an invertible module ample over every affine open of the Noetherian base.
The witness in `hL` supplies the invertibility instance required by `IsAmple` for the
restriction; it adds no geometric condition beyond invertibility of that restriction.
The degree-zero tensor power is the structure module, and a nonnegative threshold suffices.
Source: Stacks Project, Cohomology of Schemes, Tag 02O1, lemma-kill-by-twisting
(blueprint: lem-pc-relative-kill-by-twisting).

Proof:
1. Restrict to an affine open V of S. Properness survives this base change
   (lem-pc-proper-base-change); the restricted morphism is separated and finite type
   (def-weil-proper-morphism). Its base is affine Noetherian, its module coherent, and
   its invertible module ample, so lem-weil-pbc-coherent-serre-vanishing applies.
2. This gives a bound n_V for all positive cohomological degrees. The affine-base
   comparison (lem-pc-cohomology-sections-affine-base) identifies these cohomology groups
   with sections of the higher direct images. Those images are quasi-coherent
   (lem-pc-finite-support-hi), hence zero when their affine global sections vanish
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
3. The open restriction comparison (lem-pc-restrict-derived-direct-image-open) identifies
   the restriction of each higher direct image with the higher direct image on X_V.
   Thus each restriction vanishes above its bound n_V, in every positive degree.
4. Take a finite affine cover of the Noetherian base and the maximum of its bounds
   (zero for an empty cover). Vanishing on this cover gives vanishing of the sheaf. -/
theorem exists_isZero_higherDirectImage_tensorPow_of_relatively_ample
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ V : S.Opens, IsAffineOpen V →
      ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h) :
    letI : EnoughInjectives X.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero ((higherDirectImage f p).obj (F ⊗ L.tensorPow n)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
