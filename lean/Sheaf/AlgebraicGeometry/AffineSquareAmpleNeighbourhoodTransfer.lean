/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.AmpleIso
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import WeilConjectures.AlgebraicGeometry.AmplePullback

/-! # Transfer of an ample neighbourhood through an affine commutative square

Source: Stacks Project, More on Morphisms, Tag 0D2S, lemma-ample-in-neighbourhood,
final paragraph and hints; Morphisms, Tags 0892(2), 01SH and 01SD.
(blueprint: lem-trf-affine-square-ample-neighbourhood-transfer).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Transfer absolute ampleness over an affine open through an affine commutative square.
Restrictions are expressed by tensor pullback along the open inclusions. Their invertibility
witnesses come from invertible_pullback_tensor and impose no additional hypotheses.

Source: Stacks Project, More on Morphisms, Tag 0D2S, lemma-ample-in-neighbourhood,
final paragraph and hints; Morphisms, Tags 0892(2), 01SH and 01SD; Sheaves, Tags 0097, 00A0.
(blueprint: lem-trf-affine-square-ample-neighbourhood-transfer).

Proof, following the node's four steps:
1. Set T = g⁻¹(V), U = b⁻¹(V), and Y₀ = f⁻¹(U). By pqf-def-affine-morphism,
   U is affine. Commutativity gives Y₀ = a⁻¹(T). The restricted map a₀ : Y₀ → T is
   affine: every affine open H in T is affine in Z, and a₀⁻¹(H) = a⁻¹(H) is affine.
2. By lem-weil-pbc-open-immersion-module-pullback-restriction, open restriction is
   tensor pullback. The invertibility and composition comparisons of
   lem-weil-pbc-invertible-pullback-tensor identify a₀* (N|T) with M|Y₀, using the
   given a* N ≅ M. Apply lem-weil-pbc-pullback-ample-invertible to a₀ and the ample
   module N|T, then lem-sc-ample-iso. The quasi-compactness clause of
   def-weil-pbc-ample-invertible-module gives quasi-compactness of Y₀.
3. For an affine W ⊆ U, the inclusion W → U is affine by
   lem-weil-pbc-morphism-affine-schemes-affine. The square of inverse-image opens
   Y_W → Y₀ over W → U is Cartesian: a map to Y₀ factors through Y_W precisely
   when its composite to U factors through W, and the factorization is unique.
   Thus Y_W → Y₀ is affine by lem-weil-pbc-affine-morphism-permanence.
4. Apply lem-weil-pbc-pullback-ample-invertible once more to Y_W → Y₀ and M|Y₀.
   Open restriction and the composition comparison identify its pullback with
   M|Y_W (lem-weil-pbc-open-immersion-module-pullback-restriction and
   lem-weil-pbc-invertible-pullback-tensor). Use lem-sc-ample-iso to conclude.
-/
theorem affine_square_ample_neighbourhood_transfer
    {X Y Z S : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ S) (a : Y ⟶ Z) (b : X ⟶ S)
    (hsquare : a ≫ g = f ≫ b) [IsAffineHom a] [IsAffineHom b]
    (N : Z.Modules) (M : Y.Modules) [N.IsInvertible] [M.IsInvertible]
    (e : (tensorPullback a).obj N ≅ M) (V : S.Opens) (hV : IsAffineOpen V)
    (hN : @IsAmple (g ⁻¹ᵁ V).toScheme
      ((tensorPullback (g ⁻¹ᵁ V).ι).obj N)
      ((invertible_pullback_tensor (g ⁻¹ᵁ V).ι).1 N).2) :
    IsAffineOpen (b ⁻¹ᵁ V) ∧
      CompactSpace (f ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme ∧
      @IsAmple (f ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme
        ((tensorPullback (f ⁻¹ᵁ (b ⁻¹ᵁ V)).ι).obj M)
        ((invertible_pullback_tensor (f ⁻¹ᵁ (b ⁻¹ᵁ V)).ι).1 M).2 ∧
      ∀ (W : X.Opens), W ≤ b ⁻¹ᵁ V → IsAffineOpen W →
        @IsAmple (f ⁻¹ᵁ W).toScheme ((tensorPullback (f ⁻¹ᵁ W).ι).obj M)
          ((invertible_pullback_tensor (f ⁻¹ᵁ W).ι).1 M).2 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
