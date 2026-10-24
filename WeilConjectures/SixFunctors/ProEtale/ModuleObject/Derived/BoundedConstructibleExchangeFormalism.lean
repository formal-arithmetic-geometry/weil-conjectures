/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!

# The exchange formalism of bounded constructible complexes

The derived pullbacks `Lf^*`, the derived pushforwards `Rf_*` and the extensions by zero `j_!`
on the bounded constructible derived categories `Dᵇc(X)⟦Λ⟧` of separated `k`-schemes of finite
type (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`) form a
`CategoryTheory.ExchangeFormalism`, indexed by the full subcategory
`ProEtale.CondensedRing.SepFinType k` of `Over (Spec k)` with the open immersions as class of
morphisms (`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`). The pseudofunctor
laws are `boundedConstructibleUpperStarComp_assoc_app` and the unit laws of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback`.

The formal coherence results of `CategoryTheory.ExchangeFormalism` (pasting, identity and cube
laws of the base change and exchange maps) then apply to the bounded constructible functors.

## Main definitions

- `ProEtale.CondensedRing.SepFinType`: the separated `k`-schemes of finite type, as a full
  subcategory of `Over (Spec k)`, and `ProEtale.CondensedRing.SepFinType.mk`, `homMk`.
- `ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`: the exchange formalism of
  bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section SepFinType

variable (k : Type u) [Field k]

/-- The property of a `k`-scheme of being separated and of finite type over `k`. -/
def sepFinType : ObjectProperty (Over (Spec (.of k))) :=
  fun X ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsSeparated X.hom

/-- The separated `k`-schemes of finite type, as a full subcategory of `Over (Spec k)`: the
schemes on which the bounded constructible six functors are defined. -/
abbrev SepFinType := (sepFinType k).FullSubcategory

variable {k}

instance (X : SepFinType k) : LocallyOfFiniteType X.obj.hom := X.property.1
instance (X : SepFinType k) : QuasiCompact X.obj.hom := X.property.2.1
instance (X : SepFinType k) : IsSeparated X.obj.hom := X.property.2.2

/-- A separated `k`-scheme of finite type as an object of `SepFinType k`. -/
noncomputable abbrev SepFinType.mk (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] : SepFinType k :=
  ⟨X, ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- A morphism of separated `k`-schemes of finite type as a morphism of `SepFinType k`. -/
noncomputable abbrev SepFinType.homMk {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : SepFinType.mk X ⟶ SepFinType.mk Y :=
  ObjectProperty.homMk f

/-- The open immersions of separated `k`-schemes of finite type. -/
def SepFinType.openImmersion : MorphismProperty (SepFinType k) :=
  fun _ _ f ↦ IsOpenImmersion f.hom.left

instance : (SepFinType.openImmersion (k := k)).ContainsIdentities where
  id_mem X := inferInstanceAs (IsOpenImmersion (𝟙 X.obj.left))

instance {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    Fact (SepFinType.openImmersion (SepFinType.homMk j)) :=
  ⟨inferInstanceAs (IsOpenImmersion j.left)⟩

instance {X Y : SepFinType k} (j : X ⟶ Y) [h : Fact (SepFinType.openImmersion j)] :
    IsOpenImmersion j.hom.left :=
  h.out

end SepFinType

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

/-- **The exchange formalism of bounded constructible complexes**: the bounded constructible
derived categories `Dᵇc(X)⟦Λ⟧` of the separated `k`-schemes of finite type, with the derived
pullbacks `Lf^*` (`boundedConstructibleUpperStar`), their composition and identity isomorphisms,
the derived pushforwards `Rf_*` and the extensions by zero `j_!` along open immersions. -/
noncomputable def boundedConstructibleExchangeFormalism :
    ExchangeFormalism (SepFinType k) SepFinType.openImmersion where
  obj X := Dᵇc(X.obj.left)⟦Λ⟧
  pb f := boundedConstructibleUpperStar Λ ℓ f.hom
  pbId X := boundedConstructibleUpperStarId Λ ℓ X.obj
  pbComp f g := boundedConstructibleUpperStarComp Λ ℓ f.hom g.hom
  pbComp_assoc f g h M := boundedConstructibleUpperStarComp_assoc_app Λ ℓ f.hom g.hom h.hom M
  pbId_comp f M := boundedConstructibleUpperStarComp_id_left_app Λ ℓ f.hom M
  pbComp_id f M := boundedConstructibleUpperStarComp_id_right_app Λ ℓ f.hom M
  pf f := boundedConstructibleLowerStar Λ ℓ f.hom
  adj f := boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f.hom
  sh j _ := boundedConstructibleOpenImmersionLowerShriek Λ ℓ j.hom
  shAdj j _ := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j.hom

section Fields

variable {k} {X Y Z : SepFinType k}

@[simp]
lemma boundedConstructibleExchangeFormalism_obj :
    (boundedConstructibleExchangeFormalism Λ ℓ k).obj X = Dᵇc(X.obj.left)⟦Λ⟧ :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pb (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism Λ ℓ k).pb f = boundedConstructibleUpperStar Λ ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pbId :
    (boundedConstructibleExchangeFormalism Λ ℓ k).pbId X =
      boundedConstructibleUpperStarId Λ ℓ X.obj :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pbComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedConstructibleExchangeFormalism Λ ℓ k).pbComp f g =
      boundedConstructibleUpperStarComp Λ ℓ f.hom g.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pf (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism Λ ℓ k).pf f = boundedConstructibleLowerStar Λ ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_adj (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism Λ ℓ k).adj f =
      boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_sh (j : X ⟶ Y) [Fact (SepFinType.openImmersion j)] :
    (boundedConstructibleExchangeFormalism Λ ℓ k).sh j =
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_shAdj (j : X ⟶ Y)
    [Fact (SepFinType.openImmersion j)] :
    (boundedConstructibleExchangeFormalism Λ ℓ k).shAdj j =
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j.hom :=
  rfl

end Fields
end AlgebraicGeometry.ProEtale.CondensedRing
