/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.SliceSupport

/-!

# Nearby duality: the finite-support step

For a trait model `M` over the base, the cone of the duality map `δ_{M,K}` is supported on
finitely many closed points of the special fibre
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap`), provided that `δ` becomes an
isomorphism on the special fibre of the generic slice of every coordinate of the restrictions of
the total space to opens (the generic-slice step of blueprint `det-tf-nearby-duality-slice`, taken
as a hypothesis): around every point of the special fibre, the coordinates of a local chart of the
total space detect closed points, and the cone vanishes over the generic point of each coordinate
line (`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Restrict

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

section OpenRestriction

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

end OpenRestriction

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
