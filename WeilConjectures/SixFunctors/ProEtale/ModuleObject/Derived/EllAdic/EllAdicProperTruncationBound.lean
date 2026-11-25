/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleLocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic

/-! # Uniform upper bound for the discarded lower tail
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

set_option linter.unusedSectionVars false in
/-- The direct image of a sufficiently low lower tail has no cohomology in
degree `q` or above, uniformly on the bounded constructible localizing hull. -/
theorem ellAdic_proper_lowerTail_bound :
    ∃ c : ℕ, ∀ (q : ℤ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
        (condensedRingObj Λ Z.left))),
      boundedConstructibleLocalizingClosure Λ Z.left K →
      ((R((g.left)_*⟦Λ⟧)).obj
        ((DerivedCategory.TStructure.t.truncLT (q - (c : ℤ))).obj K)).IsLE (q - 1) := by
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have hheart : ProperLowerStarHeartHypotheses Λ g.left := by
    cases hΛ with
    | continuous E =>
      exact properLowerStarHeartHypotheses_continuousMapRingObj ℓ E Y.hom g.left
    | integral E =>
      exact properLowerStarHeartHypotheses_padicIntegersRingObj ℓ E Y.hom g.left
    | algebraicClosure =>
      exact properLowerStarHeartHypotheses_padicAlgClRingObj ℓ Y.hom g.left
  obtain ⟨d, hd⟩ := hheart.1
  let P := constructibleCoproductClosure Λ Z.left
  have hclosure : boundedConstructibleLocalizingClosure Λ Z.left ≤
      DerivedCategory.homologyProperty P := by
    apply boundedConstructibleLocalizingClosure_le
    intro K hK n
    exact ObjectProperty.le_weakSerreCoproductClosure _ _ (hK.2 n)
  -- The coarse Milnor bound costs one extra degree, absorbed in the existential constant.
  refine ⟨d.toNat + 1, fun q K hK ↦ ?_⟩
  let a : ℤ := q - ((d.toNat + 1 : ℕ) : ℤ)
  let L := (DerivedCategory.TStructure.t.truncLT a).obj K
  have hL : DerivedCategory.homologyProperty P L :=
    (DerivedCategory.homologyProperty P).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (a - 1) a (by omega)).app K)
      (DerivedCategory.homologyProperty_truncLE (hclosure K hK) (a - 1))
  have : L.IsLE (a - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj K a (a - 1) (by omega)
  have hbound : ((R((g.left)_*⟦Λ⟧)).obj L).IsLE (a - 1 + d + 1) := by
    apply DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    intro n
    exact DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
      (R((g.left)_*⟦Λ⟧)) d P hd _
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨a - 1, inferInstance⟩⟩
      (DerivedCategory.homologyProperty_truncGE hL _) (a - 1)
  exact DerivedCategory.TStructure.t.isLE_of_le
    ((R((g.left)_*⟦Λ⟧)).obj L) (a - 1 + d + 1) (q - 1) (by dsimp [a]; omega)

end AlgebraicGeometry.ProEtale.CondensedRing
