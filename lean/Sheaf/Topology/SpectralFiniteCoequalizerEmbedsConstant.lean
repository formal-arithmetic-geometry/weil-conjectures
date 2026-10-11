/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.Topology.SetsExtensionByEmpty
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Embedding finitely presented sheaves on spectral spaces

Source: Stacks Project, Modules, Lemma Tag 0CAL, with the presentation of Equation 0CAJ
and the reduction of Lemma Tag 0CAK.
(blueprint: lem-weil-pbc-spectral-finite-coequalizer-embeds-constant)
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- A sheaf with the finite coequalizer presentation of Equation 0CAJ embeds into a finite
product of finite constant sheaves pushed forward from constructible closed subsets.
Source: Stacks Project, Modules, Lemma Tag 0CAL.
(blueprint: lem-weil-pbc-spectral-finite-coequalizer-embeds-constant)

The target over `W` is the sectionwise product of locally constant maps on `W ∩ Z l`.
The last equality asserts compatibility with restrictions, so `e` is exactly a sheaf
morphism to that product, and the preceding clause asserts injectivity on every open.

Proof (the eight steps of the node):
1. Apply lem-weil-pbc-spectral-finite-coequalizer-from-finite-space (Tag 0CAK) to the
   given presentation. Obtain a finite sober space Y, a spectral continuous map f,
   a sheaf G with finite stalks, and an isomorphism f⁻¹G ≅ F, using the inverse image
   of def-weil-pbc-topological-inverse-image.
2. Map G into the sectionwise product of its skyscraper sheaves by taking germs.
   Restrictions preserve germs, and lem-weil-pbc-sheaf-sections-determined-by-germs
   makes this map injective on sections. The product is a sheaf by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
3. By lem-weil-pbc-skyscraper-constant-on-point-closure, the skyscraper at y with
   value G_y is the pushforward of the constant sheaf G_y on the closure of {y}.
   Composing these isomorphisms with Step 2 gives an embedding of G into their product.
4. Inverse image preserves sectionwise injections: an injection on sections is an
   injection on stalks, and lem-weil-pbc-sets-inverse-image-stalk and naturality of
   the adjunction unit identify the inverse-image stalk map with the original one.
   Equality of germs then gives equality of sections by
   lem-weil-pbc-sheaf-sections-determined-by-germs.
5. By lem-weil-pbc-sets-inverse-image-colimits-finite-products, inverse image commutes
   with this finite product, with comparison induced by its projections.
6. By lem-weil-pbc-inverse-image-closed-pushforward-constant, the pulled-back factor
   is the constant sheaf G_y pushed forward from Z_y = f⁻¹(closure {y}).
7. Each Z_y is closed. Its complement is quasi-compact open since f is spectral and
   Y is finite. By lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact, X and
   this complement are retrocompact open, so Z_y is constructible by
   def-weil-constructible-subset.
8. Enumerate Y by Fin k and compose the isomorphism F ≅ f⁻¹G, the injection of Step 4,
   and the isomorphisms of Steps 5 and 6. Every factor is injective on sections,
   and the coefficient sets are finite by Step 1, giving the asserted e. -/
theorem spectral_finite_coequalizer_embeds_constant
    (X : TopCat.{u}) [SpectralSpace X] (F : X.Sheaf (Type u))
    (m n : ℕ) (U : Fin n → Opens X) (V : Fin m → Opens X)
    (S : Fin n → Type u) (T : Fin m → Type u)
    (hU : ∀ a : Fin n, IsCompact (U a : Set X))
    (hV : ∀ b : Fin m, IsCompact (V b : Set X))
    (hS : ∀ a : Fin n, Finite (S a)) (hT : ∀ b : Fin m, Finite (T b))
    (A : Cofan (fun a : Fin n => extensionByEmptyConstant (U a) (S a)))
    (B : Cofan (fun b : Fin m => extensionByEmptyConstant (V b) (T b)))
    (hA : Nonempty (IsColimit A)) (hB : Nonempty (IsColimit B))
    (β γ : B.pt ⟶ A.pt) (q : A.pt ⟶ F)
    (hq : β ≫ q = γ ≫ q)
    (hcoeq : Nonempty (IsColimit (Cofork.ofπ q hq))) :
    ∃ (k : ℕ) (Z : Fin k → Set X) (R : Fin k → Type u),
      (∀ l : Fin k, IsClosed (Z l) ∧ Topology.IsConstructible (Z l) ∧ Finite (R l)) ∧
      ∃ e : ∀ W : Opens X, F.obj.obj (op W) →
          ((l : Fin k) → LocallyConstant {x : X // x ∈ W ∧ x ∈ Z l} (R l)),
        (∀ W : Opens X, Function.Injective (e W)) ∧
        ∀ (W W' : Opens X) (i : W' ⟶ W) (s : F.obj.obj (op W)) (l : Fin k),
          e W' (F.obj.map i.op s) l =
            LocallyConstant.comap
              ⟨fun x : {x : X // x ∈ W' ∧ x ∈ Z l} ↦
                  ⟨x.1, i.le x.2.1, x.2.2⟩,
                continuous_subtype_val.subtype_mk _⟩ (e W s l) := by
  sorry

end TopCat
