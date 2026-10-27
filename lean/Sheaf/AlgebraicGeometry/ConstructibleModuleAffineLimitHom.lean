/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.InverseImageFreeEtaleModule
import WeilConjectures.AlgebraicGeometry.LimitPullbackSectionsColimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Morphisms of constructible module sheaves along affine inverse limits

Source: Stacks Project, Etale Cohomology, Tag 09YU, `lemma-category-is-colimit`,
part (3), Faithful and Fully faithful paragraphs, for finite commutative coefficients
(blueprint: lem-sfb-constructible-module-affine-limit-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Morphisms between pullbacks of constructible module sheaves descend to a later
stage, and equality of two stage morphisms on the limit is detected at a later stage.
The pullback of a descended morphism is conjugated by the canonical composition
isomorphisms. All arrows are module-linear; no scheme is assumed Noetherian.

Source: Stacks Project, Etale Cohomology, Tag 09YU, `lemma-category-is-colimit`,
part (3), Faithful and Fully faithful paragraphs, with Tags 095N and 09YQ
(blueprint: lem-sfb-constructible-module-affine-limit-hom).

Proof:
1. By `lem-weil-pbc-constructible-module-finite-presentation`, choose a cokernel
   presentation B_i → A_i → P_i, where A_i and B_i are finite sums of free etale
   module sheaves on affine etale objects U_r and V_s. Exact additive inverse image
   preserves this presentation and the sums
   (`prop-weil-pbc-inverse-image-modules-exact`). Identify iterated pullbacks using
   `lem-weil-pbc-inverse-image-composition`; all resulting quotient maps remain epi.
2. By `lem-weil-pbc-inverse-image-free-etale-module`, maps from each pulled-back
   free summand to the pullback of Q_i correspond to sections on its base-changed
   etale object, naturally in the target. The generating-section identity says that
   further inverse image acts by the adjunction unit followed by the composition
   comparison. These are exactly the section maps rho in
   `lem-weil-pbc-limit-pullback-sections-colimit`.
3. For two maps from a pulled-back A_i or B_i agreeing on X, the finitely many
   generating sections have equal limit images. Injectivity of the section-colimit
   comparison and `lem-weil-pbc-filtered-colimit-modules-elementwise` make each
   difference vanish at a later stage. Directedness supplies one common stage.
   Naturality of rho and the finite coproduct property give equality of the maps
   there. For an empty family, there is a unique map and the stage need not change.
4. To prove clause (2), precompose a and b with A_i → P_i. Apply step 3 and cancel
   the pulled-back epimorphism A_j → P_j. This gives equality of the inverse images
   of a and b at j, using exactness of module inverse image.
5. For clause (1), precompose the given limit map with A_X → P_X. By step 2 it is
   specified by finitely many sections. Surjectivity in
   `lem-weil-pbc-limit-pullback-sections-colimit` descends each section; take a common
   stage j and assemble them to b_j : A_j → Q_j. Its pullback is the precomposed map.
   If there are no generators, use j = i and the unique map from the empty sum.
6. The map b_j d_j : B_j → Q_j vanishes after pullback. Apply step 3 to it and zero
   to find k ≥ j where b_k d_k = 0. The cokernel property gives a_k : P_k → Q_k
   with a_k q_k = b_k. Pull back this equation, use naturality of the canonical
   composition comparisons, and cancel q_X. This identifies the conjugated pullback
   of a_k with the original limit map. All operations took place in module-sheaf
   categories, so every morphism remains linear.
-/
theorem constructible_module_affineLimit_hom
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (i : I)
    (P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hP : IsConstructibleEtaleModuleSheaf P)
    (hQ : IsConstructibleEtaleModuleSheaf Q) :
    (∀ a : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj P ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Q,
      ∃ (j : I) (h : i ≤ j)
        (aⱼ : (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj P ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj Q),
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
            (D.map (homOfLE h).op) (c.π.app (op i))
            (c.w (homOfLE h).op).symm).hom.app P ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op j))).map aⱼ ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
            (D.map (homOfLE h).op) (c.π.app (op i))
            (c.w (homOfLE h).op).symm).inv.app Q = a) ∧
    (∀ a b : P ⟶ Q,
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map a =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map b →
      ∃ (j : I) (h : i ≤ j),
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map a =
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map b) := by
  sorry

end AlgebraicGeometry.Scheme
