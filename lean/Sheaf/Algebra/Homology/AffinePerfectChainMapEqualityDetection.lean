/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.FinitePresentation

import Sheaf.Algebra.FinitePresentationColimit

/-! # AffinePerfectChainMapEqualityDetection

Source: Stacks Project, Tags 09RE and 05N7.
(blueprint: lem-pc-affine-perfect-chain-map-equality-detection)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Equality of chain maps from different stages is detected at a common later stage.
This statement does not construct a homotopy or a graded family.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 (3).
Proof: Choose a common stage above i and j by directedness, and extend both maps
there using the canonical associativity isomorphisms. Their scalar extensions
to the colimit agree by the hypothesis and associativity. Each source and target term is
finitely presented, since scalar extension preserves finite presentation. Apply finite-presentation
map equality detection separately in the finitely many source degrees. Choose a
common upper stage for this finite list, and extend all equalities to it. Outside
the source support both component maps are zero, since scalar extension preserves
zero objects. Extensionality gives equality of the chain maps. Associativity
identifies these maps with the displayed scalarExtensionHom expressions.
For a preorder pass to its quotient by mutual comparability, choose representatives,
apply the partial-order finite-presentation theorem to the equivalent diagram,
and transport the equalities back. The chosen stage can be enlarged above the
original indices. Empty support needs only directedness to choose a common stage.
(blueprint: lem-pc-affine-perfect-chain-map-equality-detection) -/
theorem affine_perfect_chainMap_equality_detection
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n))
    (hEfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (E₀.X n))
    (hKfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (j : Set.Ici i₀)
    (f : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (g :
      ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
          ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (h : scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
        E₀ K₀ f =
      scalarExtensionHom (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
        E₀ K₀ g) :
    ∃ (k : Set.Ici i₀) (hik : i ≤ k) (hjk : j ≤ k),
      scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hik)).hom
        (F.map (homOfLE k.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hik))) E₀ K₀ f =
      scalarExtensionHom (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
        (F.map (homOfLE k.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE j.property) (homOfLE hjk))) E₀ K₀ g := by sorry

end CochainComplex
