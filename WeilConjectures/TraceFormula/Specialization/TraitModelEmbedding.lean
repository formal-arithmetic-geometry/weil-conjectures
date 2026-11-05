/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict

/-!

# The standard model of a scheme over the trait, and closed embeddings of models

For a morphism `q : T ⟶ S` to the trait `S = Spec k'⟦t⟧`, the *standard model*
`NearbyCyclesModel.traitStdModel q` of `T` has total space `T`, geometric generic fibre
`T ×_S η̄` and special fibre `T ×_S s` (`NearbyCyclesModel.traitStdSpecialFibre q`), with the
first projections as inclusions and `ε = j`; it is a model of finite type over the trait when `q`
is (`NearbyCyclesModel.isTraitModel_traitStdModel`).

A morphism `c : 𝒳 ⟶ T` over `S` from the total space of a model `M` of finite type over the trait
induces a morphism of models `M.geometric ⟶ (traitStdModel q).geometric`
(`NearbyCyclesModel.traitStdHom`), whose squares of geometric generic fibres and of special fibres
are cartesian (`NearbyCyclesModel.isPullback_traitStdHom_generic`,
`NearbyCyclesModel.isPullback_traitStdHom_special`). This is used with a closed immersion of an
affine total space into an affine space `𝔸ⁿ_S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {T : Scheme.{u}} (q : T ⟶ trait k')

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {qM : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hj : IsPullback M.j g qM (traitGenericPoint k'))
  (hi : IsPullback M.i X'.hom qM (traitClosedPoint k')) (c : M.total ⟶ T) (hc : c ≫ q = qM)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
