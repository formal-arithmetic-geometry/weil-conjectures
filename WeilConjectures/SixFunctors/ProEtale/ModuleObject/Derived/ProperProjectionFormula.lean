/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational

/-!
# The projection formula for proper morphisms

For a proper morphism `p : X ⟶ Y` of separated `k`-schemes of finite type, the ambient
projection map `Rp_* A ⊗ᴸ B ⟶ Rp_* (A ⊗ᴸ Lp^* B)` is an isomorphism when `A` and `B` are
bounded constructible `ℚ̄_ℓ`-complexes. The projection morphism on `Dᵇc` is its restriction
along the fully faithful inclusions.

## Main statements

- `isIso_projectionMorphism_boundedConstructible_padicAlgCl`: the ambient formula.
- `isIso_projectionMorphism_boundedConstructible_padicAlgCl_restrict`: its restriction to `Dᵇc`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- For a proper morphism, the projection morphism on the ambient derived category is an
isomorphism at bounded constructible `ℚ̄_ℓ`-complexes. -/
theorem isIso_projectionMorphism_boundedConstructible_padicAlgCl (p : X ⟶ Y) [IsProper p.left]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hA : boundedConstructible _ A) (hB : boundedConstructible _ B) :
    IsIso (moduleObjectProjectionMap (Profinite.padicAlgClRingObj ℓ) p.left A B) := by
  exact isIso_properProjectionMap_boundedConstructible_rational ℓ p
    (Mon.mk (Profinite.padicAlgClRingObj ℓ)) (Or.inr rfl) A B hA hB

/-- The projection morphism of a proper map is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes. -/
instance isIso_projectionMorphism_boundedConstructible_padicAlgCl_restrict
    (p : X ⟶ Y) [IsProper p.left]
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      p).projectionMorphism A B) := by
  have h := Adjunction.ι_map_projectionMorphism_restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ p K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ p K) A B
  have : IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      p.left).projectionMorphism A.obj B.obj) := by
    change IsIso (moduleObjectProjectionMap (Profinite.padicAlgClRingObj ℓ) p.left
      A.obj B.obj)
    exact isIso_projectionMorphism_boundedConstructible_padicAlgCl ℓ p A.obj B.obj
      A.property B.property
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        p).projectionMorphism A B)) := by
    erw [h]
    infer_instance
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

end AlgebraicGeometry.ProEtale.CondensedRing
