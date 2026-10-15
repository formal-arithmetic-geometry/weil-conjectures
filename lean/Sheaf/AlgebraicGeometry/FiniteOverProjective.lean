/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Finite covers of projective schemes over affine opens

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc, node
`lem-fin-finite-over-projective`, order 1601 (blueprint: lem-fin-finite-over-projective).
The conclusion uses the node's corrected affine-local H-projective convention.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over each affine open of a Noetherian base, a finite cover of a projective scheme
admits a closed immersion into a finite-dimensional projective space over that open.
Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc, order 1601
(blueprint: lem-fin-finite-over-projective).

Proof plan:
1. Fix an affine open U. Restrict the closed projective embedding of T and the finite
   morphism h to U. Standard projective charts show that T_U is quasi-compact over U
   (def-pc-projective-morphism, def-weil-closed-immersion,
   def-nagata-projective-space-base-change, def-nagata-relative-projective-space,
   def-weil-finite-integral-morphism, def-weil-finite-type-morphism).
2. Projective and finite morphisms are proper, as is their composite. Consequently
   Y_U is quasi-compact and locally of finite type over U (lem-pc-projective-proper,
   lem-weil-pbc-finite-proper, lem-weil-pbc-proper-composition,
   def-weil-proper-morphism, def-weil-finite-type-morphism).
3. Pull back O(1) and its coordinate sections along Y_U to projective space. The module
   is invertible (def-pc-projective-space-twist, lem-weil-pbc-invertible-pullback-tensor).
4. The coordinate nonvanishing loci are the affine inverse images of the standard
   charts under the finite map. They cover Y_U, so the pulled-back module is ample
   (def-nagata-relative-projective-space, def-weil-closed-immersion,
   def-weil-finite-integral-morphism, lem-weil-pbc-invertible-pullback-tensor,
   def-weil-pbc-ample-invertible-module).
5. The affine-base ample immersion theorem gives an immersion into some P^N_U over U
   (lem-weil-pbc-ample-very-ample-immersion-affine-base).
6. Projective space is separated over U, so the immersion is proper and hence closed
   (lem-weil-pbc-projective-space-proj-separated, lem-weil-pbc-proper-to-separated,
   lem-weil-pbc-proper-immersion-closed). With quasi-compactness this is projectivity
   (def-pc-projective-morphism). For an affine base take U to be the whole base. -/
theorem finite_over_projective_affineLocally {S T Y : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (p : T ⟶ S) [IsProjective p]
    (h : Y ⟶ T) [IsFinite h] :
    (∀ (U : S.Opens), IsAffineOpen U →
      (∃ (N : ℕ) (i : ((h ≫ p) ⁻¹ᵁ U).toScheme ⟶
          ℙ(ULift.{u} (Fin (N + 1)); U.toScheme)),
        IsClosedImmersion i ∧
          i ≫ ℙ(ULift.{u} (Fin (N + 1)); U.toScheme) ↘ U.toScheme = (h ≫ p) ∣_ U) ∧
      IsProjective ((h ≫ p) ∣_ U)) ∧
    (IsAffine S → IsProjective (h ≫ p)) := by
  sorry

end AlgebraicGeometry
