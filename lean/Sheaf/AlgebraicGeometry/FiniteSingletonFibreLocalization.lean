/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Neighbourhoods and module stalks at a singleton finite fibre

Source: Stacks Project, More on Morphisms, Tag 05B8,
`lemma-finite-morphism-single-point-in-fibre`, assertions (1) and (4).
(blueprint: lem-trf-finite-singleton-fibre-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A singleton finite fibre has cofinal inverse-image neighbourhoods, and the canonical
pushforward germ map is an isomorphism linear over the target local ring via `π.stalkMap z`.
The underlying map is Mathlib's `stalkPushforward`, not an unspecified isomorphism.
Source: Stacks Project, More on Morphisms, Tag 05B8,
`lemma-finite-morphism-single-point-in-fibre`, assertions (1) and (4).
(blueprint: lem-trf-finite-singleton-fibre-localization).

Proof:
1. By lem-weil-pbc-finite-iff-integral-lft and pqf-lem-integral-univclosed, π is
   integral and closed. For an open U containing z, remove the closed image of Z \ U.
   Its complement V contains π z because the fibre is {z}, and π⁻¹V is contained in U.
2. Choose an affine neighbourhood V₀ of π z. Finiteness makes π⁻¹V₀ affine, with
   a finite ring map A → B. By lem-weil-pbc-affine-open-spec-points, the two points
   correspond to primes p and q, and locality of the stalk maps identifies contraction
   with the map on points. Thus q is the unique prime over p.
3. Write M = G(π⁻¹V₀). The affine pushforward is quasi-coherent by
   lem-weil-pbc-affine-pushforward-base-change. Apply
   lem-sbc-affine-module-germ-localization to both affine opens: the actual germ maps
   identify the stalks with M ⊗[A] Aₚ and M_q, using
   def-weil-pbc-module-localization and def-weil-pbc-module-tensor-product.
4. The comparison of lem-trf-unique-prime-localization is an isomorphism. Its fraction
   formula sends m_y/s_y to m_z/(π♯s)_z, exactly as the canonical pushforward germ map
   does. Finally lem-weil-pbc-affine-open-stalk-localization identifies Aₚ with the
   target local ring by its germ map; the same formula identifies its scalar action
   with restriction along π.stalkMap z. This proves invertibility and the displayed
   scalar compatibility for the canonical map. -/
theorem finite_singleton_fibre_neighbourhoods_and_module_stalk
    {Z Y : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π] (z : Z)
    (_hfibre : π ⁻¹' ({π z} : Set Y) = ({z} : Set Z)) :
    (∀ U : Z.Opens, z ∈ U → ∃ V : Y.Opens, π z ∈ V ∧ π ⁻¹ᵁ V ≤ U) ∧
    (∀ G : Z.Modules, G.IsQuasicoherent →
      IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z) ∧
      ∀ (r : Y.presheaf.stalk (π z))
        (m : (RingedSpace.moduleStalkFunctor Y.toRingedSpace (π z)).obj
          ((pushforward π).obj G)),
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z (r • m) =
          (π.stalkMap z).hom r •
            (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z m :
              (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
