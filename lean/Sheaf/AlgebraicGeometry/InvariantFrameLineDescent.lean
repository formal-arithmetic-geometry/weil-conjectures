/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.OrbitTensorLineSections

/-! # Descent from invariant local frames

Source: Stacks Project, Tags 03CV, 0096, 01CA and 0BCY; the invariant-coefficient
argument of Steps 3--6 of `lem-per-orbit-tensor-line-descent`.
(blueprint: lem-per-invariant-frame-line-descent)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A module with invariant local frames over the base descends by fixed sections.
The evaluation map is equivariant and the same construction commutes with every
tensor power. This lemma assumes the frames and the isomorphisms fixing them; it
does not construct an orbit tensor or a permutation linearization.

Source: Stacks Project, Tag 03CV for module sheaves, Tag 0096 for evaluation, and
Tags 0BCY and 01CA for the local-frame and tensor arguments; the invariant-coefficient
calculation is Steps 3--6 of the parent node, written independently by Q10.
(blueprint: lem-per-invariant-frame-line-descent)

Proof: for each open T take the submodule of sections of F over q inverse T fixed
by every specified isomorphism lin g after section pullback. Restriction preserves
this submodule by naturality and aq. The fixed-ring hypothesis implies that base
scalars preserve it. Compatible fixed sections glue in F, and applying lin g to
the gluing gives the same gluing, proving the sheaf condition. This constructs M
and its inclusion j. On a neighbourhood with invariant free generator n, every
section over q inverse W for W contained in T is uniquely f times the restricted n.
Semilinearity and invariance of n say it is fixed if and only if f is fixed. The
ring-image hypothesis supplies a base coefficient, unique by ring-injectivity.
These coefficient maps commute with restriction. They trivialize M on T, so M is
locally free of rank one and is invertible. The adjoint of j sends the pulled-back
local generator to n. It is an isomorphism on this cover, hence globally; the two
maps in its equivariance square agree on the local generators and therefore agree.
For each d, tensor j on sections and apply the tensor universal property to obtain
c d. The local generator m to the power d maps to n to the power d. The assumed
invariance and free-generation of these powers repeat the coefficient argument,
proving injectivity and the exact invariant image of c d on every open. The local
inverses agree on overlaps by uniqueness. At d = 0 use the ring map q.app itself,
through unitSectionsEquiv; this proves its formula for every scalar, including on
empty opens. No exactness of invariants or division by a group order is used. -/
theorem invariant_frame_line_descent {H : Type v} {X Y : Scheme.{u}}
    (a : H → (X ≅ X)) (q : X ⟶ Y) (aq : ∀ h : H, (a h).hom ≫ q = q)
    (ring_injective : ∀ T : Y.Opens, Function.Injective (q.app T))
    (ring_image : ∀ (T : Y.Opens) (f : Γ(X, q ⁻¹ᵁ T)),
      (∃ b : Γ(Y, T), q.app T b = f) ↔
        ∀ g : H,
          X.presheaf.map (eqToHom
            (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)).symm).op
              ((a g).hom.app (q ⁻¹ᵁ T) f) = f)
    (F : X.Modules)
    (lin : ∀ g : H, (tensorPullback (a g).hom).obj F ≅ F)
    (linPow : ∀ (d : ℕ) (g : H),
      (tensorPullback (a g).hom).obj (F.tensorPow d) ≅ F.tensorPow d)
    (local_frames : ∀ y : Y, ∃ (T : Y.Opens) (n : Γ(F, q ⁻¹ᵁ T)), y ∈ T ∧
      IsFreeGenerator n ∧
      (∀ d : ℕ, IsFreeGenerator (orbitPowerSection F (q ⁻¹ᵁ T) d (fun _ ↦ n))) ∧
      (∀ g : H, (lin g).hom.app (q ⁻¹ᵁ T)
        (orbitInvariantPullback (a g).hom F (q ⁻¹ᵁ T)
          (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)) n) = n) ∧
      (∀ (d : ℕ) (g : H), (linPow d g).hom.app (q ⁻¹ᵁ T)
        (orbitInvariantPullback (a g).hom (F.tensorPow d) (q ⁻¹ᵁ T)
          (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g))
          (orbitPowerSection F (q ⁻¹ᵁ T) d (fun _ ↦ n))) =
        orbitPowerSection F (q ⁻¹ᵁ T) d (fun _ ↦ n))) :
    ∃ (M : Y.Modules) (j : M ⟶ (pushforward q).obj F)
        (e : (tensorPullback q).obj M ≅ F)
        (c : ∀ d : ℕ, M.tensorPow d ⟶
          (pushforward q).obj (F.tensorPow d)),
        M.IsInvertible ∧
        (∀ T : Y.Opens, Function.Injective (j.app T)) ∧
        (∀ (T : Y.Opens) (s : Γ(F, q ⁻¹ᵁ T)),
          (∃ m : Γ(M, T), j.app T m = s) ↔
            ∀ g : H, (lin g).hom.app (q ⁻¹ᵁ T)
              (orbitInvariantPullback (a g).hom F (q ⁻¹ᵁ T)
                (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)) s) = s) ∧
        e.hom = ((tensorPullbackSectionAdjunction q).homEquiv M F).symm j ∧
        (∀ g : H, (tensorPullback (a g).hom).map e.hom ≫ (lin g).hom =
          (orbitQuotientPullbackIso q (a g).hom (aq g) M).hom ≫ e.hom) ∧
        (∀ (d : ℕ) (T : Y.Opens) (s : Fin d → Γ(M, T)),
          (c d).app T (orbitPowerSection M T d s) =
            orbitPowerSection F (q ⁻¹ᵁ T) d (fun i ↦ j.app T (s i))) ∧
        (∀ (T : Y.Opens) (b : Γ(Y, T)),
          (c 0).app T (unitSectionsEquiv T b) = unitSectionsEquiv (q ⁻¹ᵁ T) (q.app T b)) ∧
        (∀ (d : ℕ) (T : Y.Opens), Function.Injective ((c d).app T)) ∧
        (∀ (d : ℕ) (T : Y.Opens) (s : Γ(F.tensorPow d, q ⁻¹ᵁ T)),
          (∃ m : Γ(M.tensorPow d, T), (c d).app T m = s) ↔
            ∀ g : H, (linPow d g).hom.app (q ⁻¹ᵁ T)
              (orbitInvariantPullback (a g).hom (F.tensorPow d)
                (q ⁻¹ᵁ T) (congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq g)) s) = s) := by sorry

end AlgebraicGeometry.Scheme.Modules
