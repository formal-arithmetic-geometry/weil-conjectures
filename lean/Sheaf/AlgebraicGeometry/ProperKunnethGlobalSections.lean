/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KunnethGlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.KunnethMapAgrees

/-!
# Künneth with one proper factor in module-valued cohomology

Source: Stacks Project, Tag 0F14 (2); blueprint sec-smooth-purity,
unit sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f14b).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- (blueprint: lem-kun-0f14b) The canonical Künneth map is invertible when the first
factor is proper and the second factor is of finite type over a separably closed field.
Source: Stacks Project, Tag 0F14 (2).

Proof:
1. Apply clause (b) of `kunnethMap_agrees_with_leray_projection_formula_modN` to
   the given pullback square. Its final clause makes the canonical sheaf-valued
   Künneth map invertible. The given invertibility of n supplies its IsUnit hypothesis.
2. Unfold `kunnethGlobalSectionsMap`. The tensor of the inverse Leray maps and the
   point-global-sections tensor comparison are isomorphisms. Global sections preserves
   the isomorphism from step 1, and the final Leray comparison is an isomorphism.
   Their composite is therefore invertible, with no boundedness condition on E or K.
-/
theorem isIso_kunnethGlobalSectionsMap_of_isProper
    {k : Type u} [Field k] [IsSepClosed k]
    (n : ℕ) (hn : 0 < n) [Invertible (n : k)]
    {X Y Z : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsProper aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (p : Z ⟶ X) (q : Z ⟶ Y) (sq : IsPullback p q aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))) :
    IsIso (kunnethGlobalSectionsMap (ULift.{u + 1} (ZMod n))
      p q aX aY sq.w.symm E K) := by
  obtain ⟨_, _, _, _, _, hκ⟩ :=
    kunnethMap_agrees_with_leray_projection_formula_modN
      aX aY n hn (isUnit_of_invertible (n : k)) p q sq E K
  have := hκ
  unfold kunnethGlobalSectionsMap
  infer_instance

end AlgebraicGeometry.Etale
