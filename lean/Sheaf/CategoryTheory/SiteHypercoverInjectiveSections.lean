/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Injective abelian sections on a hypercover of an arbitrary site

Source: Stacks Project, Hypercoverings, Tag 01GW (lemma-injective-trivial-cech),
using Tag 01GE (lemma-acyclic-hypercover-sheaves), representable case
(blueprint: lem-trf-site-hypercover-injective-sections).

The matching-cover hypothesis is expressed by local lifting of compatible lower
simplices. Finite limits identify these matching families with maps into the matching
object in the slice over `W`. No subcanonicality or splitness is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

/-- The augmented alternating restriction sequence of an injective abelian sheaf on a
representable hypercover of a small site is exact.

Source: Stacks Project, Hypercoverings, Tags 01GW and 01GE, representable case
(blueprint: lem-trf-site-hypercover-injective-sections).

The hypothesis `hcover` says that every compatible lower-simplex family over `T → W`
lifts on a covering sieve of `T`. Finite completeness identifies it with the covering
sieve condition for `Uₙ → Nₙ`, where matching is taken in `C/W`. For `n = 0`, the family
is empty and it says that `U₀ → W` covers. For `n = 1`, the two vertices must have the
same augmentation. Higher matching families include the lower degenerate operators,
which are determined by the proper faces. This description uses representable
presheaves and their sectionwise limits, so it does not require subcanonicality.

Proof for stage 3:
1. By lem-trf-site-hypercover-free-resolution (Tag 01GE), the sheafified free abelian
   sheaves on `Uₙ` form an exact augmented alternating-face complex ending in the
   free sheaf on `W`. By lem-trf-site-free-sheaf-sections, evaluation at the identity
   identifies Hom from each free sheaf to `I` with the corresponding sections of `I`.
2. By def-sp-injective-resolutions, a positive-degree dual cocycle factors through
   the image of the preceding boundary, since it vanishes on that boundary's kernel.
   Extend the resulting map from this image along its monomorphism into the preceding
   free sheaf. The extension is the required cochain whose differential is the cocycle.
   In degree zero, a cocycle factors uniquely through the epimorphic augmentation to
   the free sheaf on `W`. Precomposition with that epimorphism is injective.
3. Naturality of the free-sheaf Hom-to-sections equivalence identifies every dual face
   with restriction along `U.δ i`, hence the dual boundary with the displayed alternating
   sum. The dual augmentation is restriction along `e₀`. Thus the degree-zero kernel
   identification is specifically induced by restriction from `W`. Neither the free
   resolution nor this argument assumes that the topology is subcanonical or that
   the hypercover splits. -/
theorem siteHypercover_injective_sections_exact
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (J : Precoverage C) (hsite : J.IsSiteForCoverings)
    (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ J.toGrothendieck T ∧
        ∀ (V : C) (f : V ⟶ T), S f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}) [Injective I] :
    Function.Injective (I.obj.map (e.app (op (SimplexCategory.mk 0))).op) ∧
    Function.Exact
      (I.obj.map (e.app (op (SimplexCategory.mk 0))).op)
      (fun s : I.obj.obj (op (U _⦋0⦌)) ↦
        ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.obj.map (U.δ j).op s) ∧
    ∀ n : ℕ, Function.Exact
      (fun s : I.obj.obj (op (U _⦋n⦌)) ↦
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.obj.map (U.δ j).op s)
      (fun s : I.obj.obj (op (U _⦋n + 1⦌)) ↦
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.obj.map (U.δ j).op s) := by
  sorry

end CategoryTheory
