/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.VerdierExchange
public import WeilConjectures.CategoryTheory.Monoidal.ExceptionalProjection
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-!

# The derived exceptional projection morphism for module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes with a
compactification `c = (X ⟶[i] Z ⟶[g] Y)`, so that `Rf_! = Rg_* ∘ Di_!` and
`Lf^* ≅ Li^* ∘ Lg^*` on the derived categories of module objects over `Λ`. This file
constructs the *derived exceptional projection morphism*
```
PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B),
```
the canonical morphism whose invertibility is the derived projection formula for `Rf_!`. Its
direction is chosen so that the Verdier exchange morphism can be defined from it directly
(`WeilConjectures.CategoryTheory.Monoidal.Closed.VerdierExchange`). It is the composite of three
canonical maps:

1. the projection morphism `PF^*_g : Rg_* A ⊗ᴸ B ⟶ Rg_* (A ⊗ᴸ Lg^* B)` of the adjunction
   `Lg^* ⊣ Rg_*`, the transpose of `Lg^* (Rg_* A ⊗ᴸ B) ⟶ Lg^* Rg_* A ⊗ᴸ Lg^* B ⟶ A ⊗ᴸ Lg^* B`
   (`CategoryTheory.Adjunction.rightAdjointProjectionMap` for the oplax monoidal structure of
   `Lg^*` of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`), at
   `A = Di_! K`;
2. the *inverse* of the projection map `q_{i,M,N} : Di_! (M ⊗ᴸ Li^* N) ⟶ Di_! M ⊗ᴸ N` of the
   adjunction `Di_! ⊣ Li^*` along the open immersion `i`
   (`ProEtale.CondensedRing.openImmersionProjectionComparison`, an isomorphism by the derived
   projection formula for the extension by zero);
3. the identification `Li^* Lg^* B ≅ Lf^* B`.

## Main definitions

- `ProEtale.CondensedRing.properProjectionMorphism`: `PF^*_g` for any morphism `g` (the name
  records that it is only expected to be an isomorphism for `g` proper).
- `ProEtale.CondensedRing.exceptionalProjectionOfCompactification`: `PF^!_f` with respect to a
  compactification, on the unbounded derived categories, as a natural transformation of
  bifunctors (`CategoryTheory.MonoidalCategory.exceptionalProjection`).
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection`: `PF^!_f` on bounded
  constructible complexes, for a morphism `f` of separated `k`-schemes of finite type and the
  compactification `compactificationOverField f` defining `boundedConstructibleLowerShriek`, as a
  natural transformation of bifunctors `(K, B) ↦ Rf_! K ⊗ᴸ B` to `(K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B)`.
  This is the version used by Verdier duality.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjection_app_app`: the derived
  projection formula for `Rf_!` on bounded constructible `ℚ̄_ℓ`-sheaves (blueprint
  `thm-sf-pf-proetale`). It is deduced from the proper case `g` and from base change; neither is
  available in derived form.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The projection morphism of `Lg^* ⊣ Rg_*` -/

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The projection morphism `PF^*_g : Rg_* A ⊗ᴸ B ⟶ Rg_* (A ⊗ᴸ Lg^* B)` of the derived
adjunction `Lg^* ⊣ Rg_*`, as a natural transformation of bifunctors: the transpose of
```
Lg^* (Rg_* A ⊗ᴸ B) --δ--> Lg^* Rg_* A ⊗ᴸ Lg^* B --ε ▷ Lg^* B--> A ⊗ᴸ Lg^* B,
```
where `δ` is the oplax monoidal structure of `Lg^*` and `ε` the counit of `Lg^* ⊣ Rg_*`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`). It is the derived projection formula
for `Rg_*` when it is an isomorphism, which is expected for `g` proper. -/
noncomputable def properProjectionMorphism :
    R((g)_*⟦Λ⟧) ⋙ curriedTensor _ ⟶
      (Functor.postcompose₂.obj R((g)_*⟦Λ⟧)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((g)^*⟦Λ⟧)).obj (curriedTensor _)) :=
  (derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
    (Functor.OplaxMonoidal.δNatTrans L((g)^*⟦Λ⟧))

end Proper

/-! ### The exceptional projection morphism -/

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The identification `Lf^* ≅ Lg^* ⋙ Li^*` of the derived pullback along `f` with the
composite of the derived pullbacks along the two halves of a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`. -/
noncomputable def leftDerivedUpperStarCompactificationIso :
    L((f)^*⟦Λ⟧) ≅ L((c.g)^*⟦Λ⟧) ⋙ L((c.i)^*⟦Λ⟧) :=
  eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h)^*⟦Λ⟧)) c.comm) ≪≫ leftDerivedUpperStarComp Λ c.i c.g

/-- The derived exceptional projection morphism
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` with respect to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, as a natural transformation of bifunctors: the composite
```
Rg_* (Di_! K) ⊗ᴸ B --PF^*_g--> Rg_* (Di_! K ⊗ᴸ Lg^* B) --Rg_* (q_i⁻¹)-->
  Rg_* Di_! (K ⊗ᴸ Li^* Lg^* B) ≅ Rg_* Di_! (K ⊗ᴸ Lf^* B)
```
of the projection morphism `PF^*_g` at `Di_! K`, the inverse of the projection map `q_i`, and
the identification `Li^* Lg^* B ≅ Lf^* B` (`CategoryTheory.MonoidalCategory.exceptionalProjection`).
-/
noncomputable def exceptionalProjectionOfCompactification :
    curriedTensorInsertFunctor₁ (Rf_!(c)⟦Λ⟧) ⟶
      curriedTensorPost (Rf_!(c)⟦Λ⟧) ⋙ (Functor.whiskeringLeft _ _ _).obj L((f)^*⟦Λ⟧) :=
  exceptionalProjection (properProjectionMorphism Λ c.g) (openImmersionProjectionComparison Λ c.i)
    (leftDerivedUpperStarCompactificationIso Λ c)

end OfCompactification

/-! ### The exceptional projection morphism on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **derived exceptional projection morphism** on bounded constructible complexes, as a
natural transformation of bifunctors `Dᵇc(X) ⥤ Dᵇc(Y) ⥤ Dᵇc(Y)`
```
(K, B) ↦ Rf_! K ⊗ᴸ B   ⟶   (K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B):
```
the restriction (`CategoryTheory.MonoidalCategory.restrictTensor`) of
`exceptionalProjectionOfCompactification` for the compactification `compactificationOverField f`
defining `boundedConstructibleLowerShriek`, along the fully faithful monoidal inclusions
`Dᵇc ⥤ D`. This is the form in which `PF^!` enters `CategoryTheory.Verdier`. -/
noncomputable def boundedConstructibleExceptionalProjection :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriek Λ ℓ f) ⟶
      curriedTensorPost (boundedConstructibleLowerShriek Λ ℓ f) ⋙
        (Functor.whiskeringLeft _ _ _).obj (boundedConstructibleUpperStar Λ ℓ f) :=
  restrictTensor
    (boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ
      (compactificationOverField f))
    (boundedConstructibleUpperStarCompatibility Λ ℓ f)
    (exceptionalProjectionOfCompactification Λ (compactificationOverField f))

/-- **The derived projection formula for `Rf_!`** (blueprint `thm-sf-pf-proetale`): the
exceptional projection morphism `PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` is an
isomorphism for bounded constructible `ℚ̄_ℓ`-sheaves `K` and `B`, which are of finite Tor
dimension, `ℚ̄_ℓ` being a field. See the module docstring. -/
instance isIso_boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (((boundedConstructibleExceptionalProjection _ ℓ f).app K).app B) :=
  sorry

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
