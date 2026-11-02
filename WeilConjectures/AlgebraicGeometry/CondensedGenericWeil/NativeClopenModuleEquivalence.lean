/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.NativeClopenModuleFullFaithful
import WeilConjectures.CategoryTheory.JointEssentialSurjectivity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-! # Native condensed module gluing on a finite clopen partition

Source: Weil II (1.1.12), the underlying module reconstruction on components.
(blueprint: lem-dl-a1-native-clopen-module-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

attribute [local irreducible] CondensedRing.upperStar

/-- The actual native component restriction is an equivalence on module objects.
Source: Weil II (1.1.12), finite disjoint component gluing.
(blueprint: lem-dl-a1-native-clopen-module-equivalence).

Proof: the native adjunction-unit fans already prove joint full faithfulness.
Each individual pullback has a right inverse up to isomorphism: the unit of
extension by zero followed by restriction is invertible, because extension by
zero is fully faithful. To lift a prescribed tuple, take the finite biproduct
of individual lifts and split the coordinatewise projector. Module categories
are abelian, hence have finite biproducts and split all idempotents. The generic
retract construction therefore gives joint essential surjectivity. -/
theorem native_clopen_restriction_isEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : IsColimit (Cofan.mk X j)) :
    (nativeClopenRestriction Λ j).IsEquivalence := by
  have h := native_clopen_restriction_full_faithful Λ j hc
  let : (nativeClopenRestriction Λ j).Full := h.1
  let : (nativeClopenRestriction Λ j).Faithful := h.2
  let : (Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))).Full := h.1
  let : (Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))).Faithful := h.2
  let (i : I) : (CondensedRing.upperStar Λ (j i)).EssSurj := by
    let E := CondensedRing.openImmersionLowerShriek Λ (j i)
    let ff := CondensedRing.fullyFaithfulOpenImmersionLowerShriek Λ (j i)
    let : E.Full := ff.full
    let : E.Faithful := ff.faithful
    let adj := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ (j i)
    have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
    constructor
    intro M
    exact ⟨E.obj M, ⟨(asIso (adj.unit.app M)).symm⟩⟩
  let : (nativeClopenRestriction Λ j).EssSurj :=
    joint_essSurj_of_finite_biproducts (fun i ↦ CondensedRing.upperStar Λ (j i))
  exact {}

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
