/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Sections of a pulled-back module sheaf over a descended affine etale object

Source: Stacks Project, Etale Cohomology, Lemma 09YU, proof, paragraph 'Fully faithful',
a special case of Theorem 09YQ in degree 0
(blueprint: lem-weil-pbc-limit-pullback-sections-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Let `D` be a directed inverse system of quasi-compact quasi-separated schemes with affine
transition morphisms, `c` a limit cone, `i₀` a stage, `G` an etale sheaf of `Λ`-modules on
`X₀ = D.obj (op i₀)` and `V₀ → X₀` an etale morphism with `V₀` affine. For `i ≥ i₀` the
sections of `G_i = f_{i i₀}^{-1} G` over `V_i = V₀ ×_{X₀} X_i` are the sections at `V₀` of
`(f_{i i₀})_* (f_{i i₀})^{-1} G`. The maps `ρ_{i' i}` (unit of `f_{i' i}^{-1} ⊣ f_{i' i,*}` at
`G_i`, then the composition isomorphisms of direct and inverse images) and `ρ_i` (the same with
the limit projection `f_i`) form a directed system with a compatible family; the induced map
`colim_{i ≥ i₀} G_i(V_i) → G_∞(V)` is bijective, stated by the elementwise criterion for
filtered colimits: every section on the limit comes from a stage, and two sections at a stage
with the same image on the limit agree at a later stage.

Source: Stacks Project, Tag 09YU ('Fully faithful'), Tag 09YQ in degree 0
(blueprint: lem-weil-pbc-limit-pullback-sections-colimit).

Proof:
1. The `V_i` are affine, etale over `X_i`, form an inverse system with affine transitions and
   limit `V = V₀ ×_{X₀} X` (`lem-weil-pbc-scheme-over-limit`,
   `lem-weil-pbc-affine-morphism-permanence`).
2. Module inverse images and their units are those of the underlying abelian sheaves
   (`prop-weil-pbc-inverse-image-modules-exact`); the composition isomorphisms are
   `Λ`-linear by uniqueness of adjoints (`lem-weil-pbc-conjugate-iso-unit-equation`).
3. The sheaves `F_i = w_i^{-1} G` on `V_i` with the composition isomorphisms form a system
   with colimit `w^{-1} G` on `V` (constant connected diagram).
4. Theorem 09YQ in degree 0 (`lem-weil-pbc-etale-cohomology-limit-of-schemes`), translated to
   sections, gives a bijection `colim_i F_i(V_i) → (w^{-1} G)(V)`.
5. Etale restriction isomorphisms and `lem-weil-pbc-etale-restriction-pullback-unit` identify
   that system with the maps `ρ`.
6. Hence the identities of a directed system and the cocone identities hold.
7. The elementwise criterion for filtered colimits of modules
   (`lem-weil-pbc-filtered-colimit-modules-elementwise`) gives bijectivity. -/
theorem limit_pullback_sections_colimit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) [IsAffine V₀.left] :
    (∀ (i : I) (h : i₀ ≤ i)
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (le_refl i)).op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (le_refl i)).op)
          (D.map (homOfLE h).op) (D.map (homOfLE h).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (le_refl i)).op)
            (D.map (homOfLE h).op) (D.map (homOfLE h).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s = s) ∧
    (∀ (i i' i'' : I) (h : i₀ ≤ i) (h' : i ≤ i') (h'' : i' ≤ i'')
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h'').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h'').op)
          (D.map (homOfLE (h.trans h')).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE ((h.trans h').trans h'')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h'').op)
            (D.map (homOfLE (h.trans h')).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
          (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (h'.trans h'')).op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h'.trans h'')).op)
          (D.map (homOfLE h).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE ((h.trans h').trans h'')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h'.trans h'')).op)
            (D.map (homOfLE h).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) ∧
    (∀ (i i' : I) (h : i₀ ≤ i) (h' : i ≤ i')
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i'))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i'))
          (D.map (homOfLE (h.trans h')).op) (c.π.app (op i₀))
          (c.w (homOfLE (h.trans h')).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i'))
            (D.map (homOfLE (h.trans h')).op) (c.π.app (op i₀))
            (c.w (homOfLE (h.trans h')).op).symm).inv.app G)).hom.app (op V₀)
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
          (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s) ∧
    (∀ t : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀),
      ∃ (i : I) (h : i₀ ≤ i)
        (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj
            (op V₀)),
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
              (D.map (homOfLE h).op) (c.π.app (op i₀))
              (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s = t) ∧
    (∀ (i : I) (h : i₀ ≤ i)
      (s s' : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s' →
      ∃ (i' : I) (h' : i ≤ i'),
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (D.map (homOfLE h').op)).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
              (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
              (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s =
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (D.map (homOfLE h').op)).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
              (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
              (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s') := by
  sorry

end AlgebraicGeometry.Etale
