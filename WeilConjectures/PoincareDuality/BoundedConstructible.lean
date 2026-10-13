/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SmoothPurity.Defs

/-!

# The monoidal closed structure on bounded constructible module objects

Let `Λ` be a commutative condensed ring and `X` a separated `k`-scheme of finite type. The bounded
constructible complexes `Dᵇc(X)⟦Λ⟧` contain the tensor unit `Λ_X`
(`ProEtale.CondensedRing.boundedConstructible_tensorUnit`) and are stable under the derived tensor
product and the derived hom (`boundedConstructible_derivedTensor_obj`,
`boundedConstructible_derivedHom_obj`). Hence they form a full monoidal closed subcategory of
`D(Mod_{Λ_X})` (`ObjectProperty.IsMonoidal`, `ObjectProperty.IsMonoidalClosed`), whose tensor
product, unit and internal hom are those of `D(Mod_{Λ_X})`.

The restriction `boundedConstructibleUpperStar` of the strong monoidal derived pullback
`Lf^*` (`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`) is then oplax monoidal, with the
comparison maps of `Lf^*`.

## Main results

- `ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
  `ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`.
- `ProEtale.CondensedRing.oplaxMonoidal_boundedConstructibleUpperStar`.

## Implementation notes

These are lemmas rather than instances: the base field `k` does not appear in their conclusion,
so they cannot be found by instance search. Downstream statements take the two properties as
instance arguments, which these lemmas discharge.

The monoidal unit of the subcategory is `⟨𝟙_ _, _⟩`, which is definitionally
`ProEtale.CondensedRing.boundedConstructibleUnit`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

/-! ### Oplax monoidal restrictions to full monoidal subcategories -/

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.OplaxMonoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The restriction `Q.lift (P.ι ⋙ F)` of an oplax monoidal functor `F` to full monoidal
subcategories is oplax monoidal, with the comparison maps of `F`. -/
noncomputable instance oplaxMonoidalLift : (Q.lift (P.ι ⋙ F) hF).OplaxMonoidal where
  η := ObjectProperty.homMk (η F)
  δ X Y := ObjectProperty.homMk (δ F X.obj Y.obj)
  δ_natural_left f X' := ObjectProperty.hom_ext _ (δ_natural_left F f.hom X'.obj)
  δ_natural_right X f := ObjectProperty.hom_ext _ (δ_natural_right F X.obj f.hom)
  oplax_associativity X Y Z :=
    ObjectProperty.hom_ext _ (oplax_associativity F X.obj Y.obj Z.obj)
  oplax_left_unitality X := ObjectProperty.hom_ext _ (oplax_left_unitality F X.obj)
  oplax_right_unitality X := ObjectProperty.hom_ext _ (oplax_right_unitality F X.obj)

end CategoryTheory.ObjectProperty

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section BoundedConstructible

include ℓ k

variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]

/-- The bounded constructible complexes on `X` contain the unit `Λ_X` and are stable under the
derived tensor product, so `Dᵇc(X)⟦Λ⟧` is a full monoidal subcategory of `D(Mod_{Λ_X})`. -/
lemma isMonoidal_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidal where
  prop_unit := boundedConstructible_tensorUnit Λ X
  prop_tensor _ _ hK hL := boundedConstructible_derivedTensor_obj Λ ℓ k X hK hL

/-- The bounded constructible complexes on `X` are stable under the derived hom, so `Dᵇc(X)⟦Λ⟧`
is a full monoidal closed subcategory of `D(Mod_{Λ_X})`. -/
lemma isMonoidalClosed_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X)).IsMonoidalClosed where
  prop_ihom _ _ hK hL := boundedConstructible_derivedHom_obj Λ ℓ k X hK hL

end BoundedConstructible

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [(boundedConstructible (condensedRingObj Λ X)).IsMonoidal]
  [(boundedConstructible (condensedRingObj Λ Y)).IsMonoidal]

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes is
oplax monoidal, with the comparison maps of `L((f)^*⟦Λ⟧)`. -/
noncomputable instance oplaxMonoidal_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar Λ ℓ k f).OplaxMonoidal := by
  unfold boundedConstructibleUpperStar
  exact ObjectProperty.oplaxMonoidalLift _ _

end UpperStar

end AlgebraicGeometry.ProEtale.CondensedRing
