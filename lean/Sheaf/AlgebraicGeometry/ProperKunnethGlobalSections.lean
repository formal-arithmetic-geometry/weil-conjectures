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
1. Properness is stable under base change (lem-kun-proper-stability), so the second
   projection is proper. Apply the unbounded torsion-coefficient projection formula
   (lem-kun-0f0g), as in lem-kun-0f14a, to move the second factor outside its pushforward.
2. Unbounded proper base change (lem-kun-0f0c) identifies the pushforward of the first
   pullback with the constant complex on the first factor's cohomology. Pullback of
   constants and the tensor-unit constraints are lem-kun-pullback-constant and
   lem-kun-tensor-unit. The cohomological dimension of the base point is zero
   (lem-kun-cd-sep-closed-point); lem-kun-0f10 gives finite cohomological dimension of
   the finite-type second factor and the proper projection. Apply unbounded Leray
   (lem-kun-leray-unbdd) to identify cohomology on the product with cohomology of this
   tensor product on the second factor.
3. Tensoring with a constant complex (lem-kun-0f12), followed by tensor symmetry
   (lem-kun-tensor-sym), gives an inverse. The comparison calculation
   lem-kun-kunneth-map-agrees (b) says that this inverse composed with the canonical
   adjunction mate of def-kun-kunneth-map is the identity. Every comparison used is
   invertible, so the canonical map, transported to module-valued global sections,
   is an isomorphism. The argument imposes no boundedness condition on either input.
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
  let := hκ
  -- The defining transport consists of tensor/Leray isomorphisms and RΓ of κ.
  dsimp only [kunnethGlobalSectionsMap]
  infer_instance

end AlgebraicGeometry.Etale
