/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShortcutInstances
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport

/-!

# The finite-support criterion on the special fibre of a model (statement)

This file states, without proof, the finite-support criterion of Deligne's proof of the
invariance of nearby cycles under change of trait (SGA 4½, [Th. finitude], proof of 3.7), item 4
of the 3.7 list of PR #1790: on the special fibre of a model locally of finite type over a trait
with separably closed residue field, a morphism of complexes which is an isomorphism away from a
finite set of closed points and on `Rp_*` is an isomorphism
(`NearbyCyclesModel.isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map`).

It is proved on the branch `trace2/nearby-finite-support` (PR #1835), in
`SixFunctors/NearbyCycles/FiniteSupportVanishing.lean`; the statement here is copied verbatim from
that branch, and the proof is `sorry`ed here until it lands. PR #1790 does not use it: its proper
case uses the stronger closed-point criterion
`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`, since without
constructibility the slices only give the isomorphism at the non-closed points.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace ProEtale.CondensedRing.NearbyCyclesModel

attribute [local instance] hasTensor₄ObjExt_mod hasGoodTensor₁₂Tensor_mod hasGoodTensorTensor₂₃_mod
  hasColimitsOfShape_int_mod preservesColimitsOfShape_int_curriedTensor_obj_mod
  preservesColimitsOfShape_int_curriedTensor_flip_obj_mod

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {R : Type u} [CommRing R] {κ : Type u} [Field κ] [IsSepClosed κ] {b : R →+* κ}
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'} {q : M.total ⟶ Spec (.of R)}
  [LocallyOfFiniteType q] {p : X' ⟶ Spec (.of κ)}

/-- **The finite-support criterion on the special fibre of a model, for morphisms**: in the
situation of `isZero_of_isZero_leftDerivedUpperStar_finsetComplOpens_of_isZero` on PR #1835,
a morphism `a` of complexes on the special fibre `X'` which is an isomorphism away from a finite
set of closed points and such that `Rp_* a` is an isomorphism is an isomorphism. This is the form
in which Deligne's induction applies it, to the base change morphism of a change of trait
restricted to the special fibre. -/
theorem isIso_of_isIso_leftDerivedUpperStar_finsetComplOpens_map
    (hMi : IsPullback M.i p q (Spec.map (CommRingCat.ofHom b))) (S : Finset X')
    (hS : ∀ x ∈ S, IsClosed {x})
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1})
      (condensedRingObj Λ X'))} (a : K ⟶ L)
    (hU : IsIso ((L(((finsetComplOpens S hS).ι)^*⟦Λ⟧)).map a))
    (hΓ : IsIso ((R((p)_*⟦Λ⟧)).map a)) : IsIso a :=
  sorry

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
