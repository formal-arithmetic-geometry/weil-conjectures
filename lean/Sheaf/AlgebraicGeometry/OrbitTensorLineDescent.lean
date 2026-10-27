/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.OrbitTensorLineSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.OrbitTensorLocalFrames
import Sheaf.AlgebraicGeometry.OrbitTensorPermutationLinearizations
import Sheaf.AlgebraicGeometry.InvariantFrameLineDescent

/-! # Descent of the orbit tensor line

Source: Rydh, arXiv:0708.3333v2, Proposition 4.7, norm argument; Stacks Project,
Tags 0BUT, 0BCY, 01CA, 01CD, 0096 and 03CV.
(blueprint: lem-per-orbit-tensor-line-descent)

The orbit tensor uses the existing `pencilOrbitBundle` iterated sheaf tensor product.
Its permutation linearization
is specified by its action on orbit frames. Such frames locally generate, by Tag 0BUT;
thus these formulas determine the maps uniquely, including all their coherence laws.
Invariant subsheaves are specified by sectionwise injectivity and their exact image.
No object or map is selected from a theorem of mere existence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Descent of the orbit tensor through a finite invariant-ring quotient, with canonical
linearization, evaluation, and all tensor powers (including zero).

Source: Rydh Proposition 4.7, norm argument; Stacks Tags 0BUT, 0BCY, 01CA, 01CD,
0096 and 03CV (blueprint: lem-per-orbit-tensor-line-descent).

Proof:
1. By lem-sfb-finite-trivialize-invertible-upstairs choose a cover of Y on whose inverse
   images L has a frame s. These inverse images are invariant because a_h q = q.
2. By lem-weil-pbc-invertible-pullback-tensor and the symmetric monoidal structure of
   lem-weil-pbc-module-tensor-symmetric-monoidal, the tensor n of all a_h^*s is a frame.
   Pullback by g reindexes h to hg; the canonical permutation fixes n. This determines
   the linearization uniquely on this cover and proves its identity and cocycle laws.
   The same construction on tensor powers fixes the pure power of n, also in degree 0.
3. Fixed sections glue uniquely, so they form a module subsheaf M of q_*N; multiplication
   by O_Y preserves them because q a_h = q. This is def-weil-sheaf-of-modules-category.
4. A section f n is fixed exactly when f is fixed. The invariant-ring hypothesis gives
   a unique b in O_Y with f = q^sharp(b). Thus b maps to q^sharp(b)n and trivializes M.
   These restriction-compatible local presentations show that M is invertible.
5. The adjoint of the inclusion is the canonical evaluation q^*M to N. It sends the
   pulled-back frame m to n and hence is an isomorphism. Both linearizations fix these
   frames, so the equivariance square commutes locally, therefore globally.
6. Tensoring invariant sections gives the displayed c_d. It sends the pure tensor of
   m's to that of n's. The same coefficient calculation gives exactly all invariant
   sections, with no kernel. Thus its factorization through the invariant subsheaf is
   an isomorphism. At d=0 it is precisely q^sharp, the assumed invariant-ring map.

The frame normalization clauses uniquely specify the permutation linearizations: the
finite-trivialization lemma supplies generating orbit frames locally over Y. The maps j
and c_d identify their sources with the actual invariant subsheaves by their sectionwise
image, rather than positing an arbitrary isomorphic descended object. -/
theorem orbit_tensor_line_descent {H : Type v} [Group H] [Finite H]
    {X Y : Scheme.{u}} (a : H → (X ≅ X))
    (a_one : (a 1).hom = 𝟙 X)
    (a_mul : ∀ g h : H, (a (g * h)).hom = (a h).hom ≫ (a g).hom)
    (q : X ⟶ Y) [IsFinite q] [Surjective q]
    (aq : ∀ h : H, (a h).hom ≫ q = q)
    (ring_injective : ∀ T : Y.Opens, Function.Injective (q.app T))
    (ring_image : ∀ (T : Y.Opens) (f : Γ(X, q ⁻¹ᵁ T)),
      (∃ b : Γ(Y, T), q.app T b = f) ↔
        ∀ g : H,
          X.presheaf.map (eqToHom
            (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)).symm).op
              ((a g).hom.app (q ⁻¹ᵁ T) f) = f)
    (L : X.Modules) [L.IsInvertible] :
    ∃ (lin : ∀ g : H,
        (tensorPullback (a g).hom).obj (pencilOrbitBundle a L) ≅ pencilOrbitBundle a L)
      (linPow : ∀ (d : ℕ) (g : H),
        (tensorPullback (a g).hom).obj ((pencilOrbitBundle a L).tensorPow d) ≅
          (pencilOrbitBundle a L).tensorPow d),
      (lin 1).hom = (orbitLinearizationUnit a a_one (pencilOrbitBundle a L)).hom ∧
      (∀ g h : H, (lin (g * h)).hom =
        (orbitLinearizationComp a a_mul (pencilOrbitBundle a L) g h).hom ≫
          (tensorPullback (a h).hom).map (lin g).hom ≫ (lin h).hom) ∧
      (∀ d : ℕ, (linPow d 1).hom =
        (orbitLinearizationUnit a a_one ((pencilOrbitBundle a L).tensorPow d)).hom) ∧
      (∀ (d : ℕ) (g h : H), (linPow d (g * h)).hom =
        (orbitLinearizationComp a a_mul ((pencilOrbitBundle a L).tensorPow d) g h).hom ≫
          (tensorPullback (a h).hom).map (linPow d g).hom ≫ (linPow d h).hom) ∧
      (∀ (T : Y.Opens) (s : Γ(L, q ⁻¹ᵁ T)) (g : H),
        (lin g).hom.app (q ⁻¹ᵁ T)
          (orbitInvariantPullback (a g).hom (pencilOrbitBundle a L) (q ⁻¹ᵁ T)
            (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g))
            (orbitTensorFrame a L (q ⁻¹ᵁ T)
              (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s)) =
          orbitTensorFrame a L (q ⁻¹ᵁ T)
            (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s) ∧
      (∀ (d : ℕ) (T : Y.Opens) (s : Γ(L, q ⁻¹ᵁ T)) (g : H),
        (linPow d g).hom.app (q ⁻¹ᵁ T)
          (orbitInvariantPullback (a g).hom ((pencilOrbitBundle a L).tensorPow d)
            (q ⁻¹ᵁ T) (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g))
            (orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d
              (fun _ ↦ orbitTensorFrame a L (q ⁻¹ᵁ T)
                (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s))) =
          orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d
            (fun _ ↦ orbitTensorFrame a L (q ⁻¹ᵁ T)
              (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s)) ∧
      ∃ (M : Y.Modules) (j : M ⟶ (pushforward q).obj (pencilOrbitBundle a L))
        (e : (tensorPullback q).obj M ≅ pencilOrbitBundle a L)
        (c : ∀ d : ℕ, M.tensorPow d ⟶
          (pushforward q).obj ((pencilOrbitBundle a L).tensorPow d)),
        M.IsInvertible ∧
        (∀ T : Y.Opens, Function.Injective (j.app T)) ∧
        (∀ (T : Y.Opens) (s : Γ(pencilOrbitBundle a L, q ⁻¹ᵁ T)),
          (∃ m : Γ(M, T), j.app T m = s) ↔
            ∀ g : H, (lin g).hom.app (q ⁻¹ᵁ T)
              (orbitInvariantPullback (a g).hom (pencilOrbitBundle a L) (q ⁻¹ᵁ T)
                (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)) s) = s) ∧
        e.hom = ((tensorPullbackSectionAdjunction q).homEquiv M (pencilOrbitBundle a L)).symm j ∧
        (∀ g : H, (tensorPullback (a g).hom).map e.hom ≫ (lin g).hom =
          (orbitQuotientPullbackIso q (a g).hom (aq g) M).hom ≫ e.hom) ∧
        (∀ (d : ℕ) (T : Y.Opens) (s : Fin d → Γ(M, T)),
          (c d).app T (orbitPowerSection M T d s) =
            orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d (fun i ↦ j.app T (s i))) ∧
        (∀ (T : Y.Opens) (b : Γ(Y, T)),
          (c 0).app T (unitSectionsEquiv T b) = unitSectionsEquiv (q ⁻¹ᵁ T) (q.app T b)) ∧
        (∀ (d : ℕ) (T : Y.Opens), Function.Injective ((c d).app T)) ∧
        (∀ (d : ℕ) (T : Y.Opens) (s : Γ((pencilOrbitBundle a L).tensorPow d, q ⁻¹ᵁ T)),
          (∃ m : Γ(M.tensorPow d, T), (c d).app T m = s) ↔
            ∀ g : H, (linPow d g).hom.app (q ⁻¹ᵁ T)
              (orbitInvariantPullback (a g).hom ((pencilOrbitBundle a L).tensorPow d)
                (q ⁻¹ᵁ T) (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)) s) = s) := by
  obtain ⟨lin, linPow, hunit, hcomp, hunitPow, hcompPow, hframe, hframePow⟩ :=
    exists_orbit_tensor_linearizations a a_one a_mul q aq L
  refine ⟨lin, linPow, hunit, hcomp, hunitPow, hcompPow, hframe, hframePow, ?_⟩
  apply invariant_frame_line_descent a q aq ring_injective ring_image
    (pencilOrbitBundle a L) lin linPow
  intro y
  obtain ⟨T, s, hy, hn, hnPow⟩ := exists_orbit_tensor_local_frames a q aq L y
  exact ⟨T, orbitTensorFrame a L (q ⁻¹ᵁ T)
    (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s,
    hy, hn, hnPow, hframe T s, fun d g ↦ hframePow d T s g⟩

end AlgebraicGeometry.Scheme.Modules
