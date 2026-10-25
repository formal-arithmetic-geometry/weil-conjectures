/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed

/-!
# The derived pullback on module objects commutes with the shifts

Since the pullback `f^*` on module objects is exact, the derived pullback `L((f)^*⟦Λ⟧)` is
isomorphic to the levelwise functor `D((f)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`), which commutes with the
shifts and is triangulated. We transport both structures to `L((f)^*⟦Λ⟧)`.

As an application, maps from a shifted extension by zero `(j_! N)[n]` to a pushforward
`Ri_* M` along a closed immersion `i` whose range misses that of `j` vanish: by the adjunction
`Li^* ⊣ Ri_*` they correspond to maps out of `(Li^* j_! N)[n] = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Shift

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback on module objects commutes with the shifts: the structure of the
levelwise functor `D((f)^*⟦Λ⟧)` transported along `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)`. -/
noncomputable instance : L((f)^*⟦Λ⟧).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The identification `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)` is compatible with the shifts. -/
instance : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ ℤ

/-- The derived pullback on module objects is triangulated. -/
instance : L((f)^*⟦Λ⟧).IsTriangulated :=
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

end Shift

section HomVanishing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ in
/-- Maps from a shifted extension by zero `(j_! N)[n]` to a pushforward `Ri_* M` vanish when the
range of the closed immersion `i` misses the range of the open immersion `j`: by the adjunction
`Li^* ⊣ Ri_*` they correspond to maps out of `(Li^* j_! N)[n] = 0`. -/
lemma eq_zero_of_shift_openImmersionLowerShriek_to_lowerStar {U Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base)) (N : Dᵇc(U.left)⟦Λ⟧)
    (n : ℤ) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj Λ Z.left)))
    (φ : (shiftFunctor _ n).obj ((boundedConstructible (condensedRingObj Λ X.left)).ι.obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj N)) ⟶
        R((i.left)_*⟦Λ⟧).obj M) : φ = 0 := by
  have h₀ : IsZero (L((i.left)^*⟦Λ⟧).obj ((boundedConstructible
      (condensedRingObj Λ X.left)).ι.obj ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ
        j).obj N))) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j.left i.left hji
      N.obj).of_iso (L((i.left)^*⟦Λ⟧).mapIso
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app N))
  have h₁ : IsZero (L((i.left)^*⟦Λ⟧).obj ((shiftFunctor _ n).obj ((boundedConstructible
      (condensedRingObj Λ X.left)).ι.obj ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ
        j).obj N)))) :=
    ((shiftFunctor _ n).map_isZero h₀).of_iso ((L((i.left)^*⟦Λ⟧).commShiftIso n).app _)
  rw [← ((derivedUpperStarLowerStarAdjunction Λ i.left).homEquiv _ _).apply_symm_apply φ,
    h₁.eq_of_src (((derivedUpperStarLowerStarAdjunction Λ i.left).homEquiv _ _).symm φ) 0,
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

end HomVanishing

end AlgebraicGeometry.ProEtale.CondensedRing
