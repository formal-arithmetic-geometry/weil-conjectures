/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.CategoryTheory.CyclicDerivedFreeHomCoordinates
public import Sheaf.CategoryTheory.CyclicDerivedOffDiagonalPresentation

/-! # Comparison of the free and off-diagonal boundaries

Source: Stacks Tags 0149, 0152, and the normalized cyclic free resolution.
(blueprint: lem-sf-cyclic-free-boundary-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The normalized SES boundary of the free resolution computes the uniquely
presented off-diagonal boundary. This only identifies two concrete morphisms; it
does not assert additivity, naturality, or any exactness statement.

Proof: take a strict presentation S of u. Let e be the free adjunct of the chosen
underlying splitting s, and let f₀ be the adjunct of its off-diagonal entry.
On summand zero, e d = j f₀ follows by inserting the inverse triangular action:
the difference between s and its translate is exactly the inclusion composed
with the off-diagonal entry. Also p e = epsilon because p s = 1. The free
adjunction shows these identities hold on all summands, so f₀,e,1 define a
morphism of short exact sequences. Naturality of triangleOfSESδ gives the
presented boundary as delta_free followed by f₀[1]. The standard localization
comparisons, differential_fac, delta_fac, and the two adjunctions defining
cyclicDerivedFreeShiftedHomEquiv turn this expression into the displayed one.
Use naturality of delta to transport the presentation's endpoint isomorphisms.
Finally cyclicDerivedOffDiagonalBoundary_eq identifies the presented morphism
with the specified boundary. The computation uses the normalized SES sign,
and works for unbounded complexes and independent localizations.
Source: parent calculus step 2, Stacks 0152 and parent presentation step 8
(blueprint: lem-sf-cyclic-free-boundary-comparison). -/
theorem cyclicDerivedFreeBoundary_comparison (R : CyclicDerivedFreeResolution F)
    {M N : DerivedCategory (IsoAlgebra F)} (u : CyclicDerivedHom F M N (-1)) :
    cyclicDerivedOffDiagonalBoundary F u =
      R.delta.app M ≫ (cyclicDerivedFreeShiftedHomEquiv F M N).symm u := by sorry

end CategoryTheory.Endofunctor.IsoAlgebra
