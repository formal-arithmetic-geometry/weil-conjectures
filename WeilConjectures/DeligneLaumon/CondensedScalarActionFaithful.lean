/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations

/-! # Trivial monodromy survives normalized scalar extension -/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.LisseQlbar

set_option maxHeartbeats 0 in
-- The comparison contains module-object functors with large coefficient types.
/-- The normalized scalar comparison carries a trivial action to a trivial action.
Source: `thm-lisse-qlbar-representations`, scalar compatibility in clauses (2)--(3).
(blueprint: lem-dl-a1-condensed-scalar-action-faithful).

Proof: the comparison identifies the target module with a tensor product. Equivariance
fixes pure tensors whenever the original action is the identity. Every tensor is a sum
of pure tensors, so linearity fixes the entire target module, including the zero module. -/
theorem ScalarCompatibility.action_eq_one
    {Λ B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj B] [IsCommMonObj B]
    {a : Λ ⟶ B} [IsMonHom a]
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {sR : R → condensedScalarRing Λ} {sS : S → condensedScalarRing B}
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] {x : Spec (.of Ω) ⟶ X}
    {G : Type v} [Group G]
    {P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    {Q : ObjectProperty (Rep.{u + 1} R G)}
    {P' : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))}
    {Q' : ObjectProperty (Rep.{u + 1} S G)}
    {e : FibreEquivalence Λ R sR x G P Q}
    {e' : FibreEquivalence B S sS x G P' Q'}
    (c : ScalarCompatibility Λ B a R S sR sS x G P Q P' Q' e e')
    (L : P.FullSubcategory) (M : P'.FullSubcategory)
    (i : L.obj ⟶ (Mod.comap (coefficientMap a X)).obj M.obj)
    (hi : IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv
      L.obj M.obj).symm i))
    (g : G) (hg : (e.functor.obj L).ρ g = 1) :
    (e'.functor.obj M).ρ g = 1 := by
  obtain ⟨t, _, ht⟩ := c.comparison L M i hi
  ext w
  obtain ⟨z, rfl⟩ := t.surjective w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b v =>
    rw [← ht g b v, hg]
    rfl
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'

end AlgebraicGeometry.ProEtale.LisseQlbar
