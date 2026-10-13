/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Fixed-degree affine Serre vanishing

Source: Stacks Project, Tag 0B5T (4).
(blueprint: lem-pc-e4-affine-restricted-twist-fixed-degree)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Fixed-degree Serre vanishing on the inverse image of one affine open.

Source: Stacks Project, Tag 0B5T (4), used in the affine-local proof of Tag 02O1.
(blueprint: lem-pc-e4-affine-restricted-twist-fixed-degree)

Proof: Base change f to V. Properness gives a Noetherian source over the
Noetherian affine base. Restriction preserves coherence, and the hypothesis
provides an ample invertible module on this source. Apply Tag 0B5T (4) in the
specified positive degree as follows. A positive power L^d comes from O(1)
along an immersion into projective space; properness makes that immersion
closed. For each residue r<d, the projection formula and affine closed-immersion
cohomology comparison identify the dt+r twist with projective cohomology of
i_*(F tensor L^r) tensor O(t). This pushforward is coherent. Projective Serre
vanishing supplies a threshold t_r. The finite maximum T of these thresholds
gives the bound d*T, since n=dt+r and n>=d*T imply t>=T. Open restriction commutes
with tensor products and powers, identifying the coefficient module with
F restricted tensor the nth power of L restricted. Transport cohomology
vanishing through this isomorphism. For empty V or empty inverse image the
module category is zero, so threshold zero works. No threshold uniform in
cohomological degree is asserted here. -/
theorem exists_isZero_restricted_twist_moduleCohomology_degree
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible] (V : S.Opens) (hV : IsAffineOpen V)
    (hL : ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
      @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h)
    (q : ℕ) (hq : 0 < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace q).obj
        ((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι)) := by sorry

end AlgebraicGeometry.Scheme.Modules
