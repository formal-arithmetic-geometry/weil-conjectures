/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Widesubcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ExtendScalars

/-!
# Constructible objects with coefficients in `ℚ̄_ℓ`

Let `X` be a scheme. This file constructs the category `D_cons(X, ℚ̄_ℓ)` as the 2-colimit

```
  D_cons(X, ℚ̄_ℓ)  :=  2-colim_E D_cons(X, E)
```

over the finite extensions `E` of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l` of the categories
`D_cons(X, E)` of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient`,
with transition functors the extensions of scalars `- ⊗_E F` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.ExtendScalars`.

## Realization inside `D(X, ℚ̄_ℓ)`

Rather than as an abstract 2-colimit, `D_cons(X, ℚ̄_ℓ)` is realized as a subcategory of the
derived category `D(X, ℚ̄_ℓ)` of pro-étale sheaves of modules over `ℚ̄_ℓ` with its discrete
topology, through the extensions of scalars `T_E = - ⊗_E ℚ̄_ℓ : D_cons(X, E) ⥤ D(X, ℚ̄_ℓ)`,
which are compatible with the transition functors
(`DerivedCategoryConstructibleRational.extendScalarsQlbarComp`):

- its objects are the objects of `D(X, ℚ̄_ℓ)` in the essential image of some `T_E`;
- its morphisms are the composites of morphisms of the form `T_E(g)` for some `E` and some
  morphism `g` of `D_cons(X, E)`, up to isomorphism of arrows of `D(X, ℚ̄_ℓ)`.

The morphisms from `T_E(A)` to `T_E(B)` coming from a single step are thus the image of
`colim_F Hom_{D_cons(X, F)}(A ⊗_E F, B ⊗_E F)`, as in the 2-colimit. Since the identifications
`K ≅ T_E(A)` are arbitrary isomorphisms of `D(X, ℚ̄_ℓ)`, every isomorphism of `D(X, ℚ̄_ℓ)`
between two objects is a morphism of `D_cons(X, ℚ̄_ℓ)`
(`DerivedCategory.constructibleQlbarHom_of_isIso`). In general this is **not** a full
subcategory of `D(X, ℚ̄_ℓ)`.

## Main definitions

- `PadicAlgCl.FiniteExtension` : the finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, the index of
  the 2-colimit.
- `DerivedCategory.constructibleQlbar` : the objects of `D(X, ℚ̄_ℓ)` in the essential image of
  some `T_E`.
- `DerivedCategory.constructibleQlbarHom` : the multiplicative closure of the morphisms
  isomorphic to some `T_E(g)`.
- `DerivedCategoryConstructibleQlbar` : the category `D_cons(X, ℚ̄_ℓ)`.
- `DerivedCategoryConstructibleQlbar.ι` : its faithful inclusion into `D(X, ℚ̄_ℓ)`.
- `DerivedCategoryConstructibleQlbar.isoMk` : an isomorphism of `D(X, ℚ̄_ℓ)` between objects of
  `D_cons(X, ℚ̄_ℓ)` is an isomorphism of `D_cons(X, ℚ̄_ℓ)`.
- `DerivedCategoryConstructibleRational.toQlbar` : the functor `D_cons(X, E) ⥤ D_cons(X, ℚ̄_ℓ)`
  to the 2-colimit, lifting `T_E`.
- `DerivedCategoryConstructibleRational.extendScalarsCompToQlbarIso` : for `E ⊆ F`, the
  compatibility `(- ⊗_E F) ⋙ toQlbar F ≅ toQlbar E` of the functors to the 2-colimit with the
  transition functors.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace PadicAlgCl

/-- The finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`: the index of the 2-colimit defining
`D_cons(X, ℚ̄_ℓ)`. -/
def FiniteExtension (l : ℕ) [Fact l.Prime] : Type :=
  {E : IntermediateField ℚ_[l] (PadicAlgCl l) // FiniteDimensional ℚ_[l] E}

instance (l : ℕ) [Fact l.Prime] (E : FiniteExtension l) : FiniteDimensional ℚ_[l] E.1 := E.2

end PadicAlgCl

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

namespace DerivedCategory

/-- The objects of `D_cons(X, ℚ̄_ℓ)`: the objects of `D(X, ℚ̄_ℓ)` isomorphic to `K ⊗_E ℚ̄_ℓ`
for some finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and some `K` in `D_cons(X, E)`. -/
def constructibleQlbar : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l))))) :=
  ⨆ E : PadicAlgCl.FiniteExtension l,
    (DerivedCategoryConstructibleRational.extendScalarsQlbar X l E.1).essImage

/-- The morphisms of `D_cons(X, ℚ̄_ℓ)`: the composites of morphisms of `D(X, ℚ̄_ℓ)` isomorphic,
as arrows, to `g ⊗_E ℚ̄_ℓ` for some finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and some
morphism `g` of `D_cons(X, E)`. -/
def constructibleQlbarHom : MorphismProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l))))) :=
  (⨆ E : PadicAlgCl.FiniteExtension l,
    (⊤ : MorphismProperty _).map
      (DerivedCategoryConstructibleRational.extendScalarsQlbar X l E.1)).multiplicativeClosure

instance : (constructibleQlbarHom X l).IsMultiplicative := by
  unfold constructibleQlbarHom
  infer_instance

variable {X l}

lemma constructibleQlbar_extendScalarsQlbar_obj (E : PadicAlgCl.FiniteExtension l)
    (K : DerivedCategoryConstructibleRational X l E.1) :
    constructibleQlbar X l
      ((DerivedCategoryConstructibleRational.extendScalarsQlbar X l E.1).obj K) :=
  (ObjectProperty.prop_iSup_iff _ _).2 ⟨E, Functor.obj_mem_essImage _ K⟩

lemma constructibleQlbarHom_extendScalarsQlbar_map (E : PadicAlgCl.FiniteExtension l)
    {K L : DerivedCategoryConstructibleRational X l E.1} (g : K ⟶ L) :
    constructibleQlbarHom X l
      ((DerivedCategoryConstructibleRational.extendScalarsQlbar X l E.1).map g) :=
  .of _ ((MorphismProperty.iSup_iff _ _).2 ⟨E, MorphismProperty.map_mem_map _ _ g trivial⟩)

/-- Every isomorphism of `D(X, ℚ̄_ℓ)` out of an object of `D_cons(X, ℚ̄_ℓ)` is a morphism of
`D_cons(X, ℚ̄_ℓ)`: if `e : K ⊗_E ℚ̄_ℓ ≅ M`, then `f : M ⟶ N` is isomorphic, as an arrow, to
`𝟙 K ⊗_E ℚ̄_ℓ`, through `e` and `e ≪≫ asIso f`. -/
lemma constructibleQlbarHom_of_isIso {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l))))} (hM : constructibleQlbar X l M)
    (f : M ⟶ N) [IsIso f] : constructibleQlbarHom X l f := by
  obtain ⟨E, K, ⟨e⟩⟩ := (ObjectProperty.prop_iSup_iff _ _).1 hM
  exact .of _ ((MorphismProperty.iSup_iff _ _).2
    ⟨E, K, K, 𝟙 K, trivial, ⟨Arrow.isoMk e (e ≪≫ asIso f)⟩⟩)

end DerivedCategory

/-- The category `D_cons(X, ℚ̄_ℓ)` of constructible objects with coefficients in `ℚ̄_ℓ`: the
2-colimit of the categories `D_cons(X, E)` over the finite extensions `E` of `ℚ_ℓ` inside
`ℚ̄_ℓ`, realized inside `D(X, ℚ̄_ℓ)` as the subcategory with objects
`DerivedCategory.constructibleQlbar` and morphisms `DerivedCategory.constructibleQlbarHom`.
It is in general not a full subcategory of `D(X, ℚ̄_ℓ)`. -/
@[reducible]
def DerivedCategoryConstructibleQlbar : Type _ :=
  WideSubcategory ((DerivedCategory.constructibleQlbarHom X l).inverseImage
    (DerivedCategory.constructibleQlbar X l).ι)

namespace DerivedCategoryConstructibleQlbar

/-- The inclusion `D_cons(X, ℚ̄_ℓ) ⥤ D(X, ℚ̄_ℓ)`. -/
@[reducible]
noncomputable def ι : DerivedCategoryConstructibleQlbar X l ⥤ DerivedCategory (Sheaf
    (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl l)))) :=
  wideSubcategoryInclusion _ ⋙ (DerivedCategory.constructibleQlbar X l).ι

example : (ι X l).Faithful := inferInstance

variable {X l}

/-- An isomorphism of `D(X, ℚ̄_ℓ)` between objects of `D_cons(X, ℚ̄_ℓ)` is an isomorphism of
`D_cons(X, ℚ̄_ℓ)`. -/
@[simps!]
noncomputable def isoMk {M N : DerivedCategoryConstructibleQlbar X l}
    (e : (ι X l).obj M ≅ (ι X l).obj N) : M ≅ N :=
  WideSubcategory.isoMk (ObjectProperty.isoMk _ e)
    (DerivedCategory.constructibleQlbarHom_of_isIso M.obj.property e.hom)
    (DerivedCategory.constructibleQlbarHom_of_isIso N.obj.property e.inv)

end DerivedCategoryConstructibleQlbar

namespace DerivedCategoryConstructibleRational

/-- The functor `D_cons(X, E) ⥤ D_cons(X, ℚ̄_ℓ)` to the 2-colimit, for a finite extension `E`
of `ℚ_ℓ` inside `ℚ̄_ℓ`: the extension of scalars `- ⊗_E ℚ̄_ℓ`. -/
@[simps]
noncomputable def toQlbar (E : PadicAlgCl.FiniteExtension l) :
    DerivedCategoryConstructibleRational X l E.1 ⥤ DerivedCategoryConstructibleQlbar X l where
  obj K := ⟨⟨(extendScalarsQlbar X l E.1).obj K,
    DerivedCategory.constructibleQlbar_extendScalarsQlbar_obj E K⟩⟩
  map g := ⟨ObjectProperty.homMk ((extendScalarsQlbar X l E.1).map g),
    DerivedCategory.constructibleQlbarHom_extendScalarsQlbar_map E g⟩
  map_id K := by ext; exact (extendScalarsQlbar X l E.1).map_id K
  map_comp f g := by ext; exact (extendScalarsQlbar X l E.1).map_comp f g

/-- The functor to the 2-colimit lifts the extension of scalars `- ⊗_E ℚ̄_ℓ`. -/
noncomputable def toQlbarCompιIso (E : PadicAlgCl.FiniteExtension l) :
    toQlbar X l E ⋙ DerivedCategoryConstructibleQlbar.ι X l ≅ extendScalarsQlbar X l E.1 :=
  Iso.refl _

/-- For finite extensions `E ⊆ F` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the functors to the 2-colimit are
compatible with the extension of scalars `- ⊗_E F : D_cons(X, E) ⥤ D_cons(X, F)`: this is
`extendScalarsQlbarComp`, as an isomorphism in `D_cons(X, ℚ̄_ℓ)`. -/
noncomputable def extendScalarsCompToQlbarIso (E F : PadicAlgCl.FiniteExtension l)
    [Algebra E.1 F.1] [IsScalarTower E.1 F.1 (PadicAlgCl l)] [FiniteDimensional E.1 F.1] :
    extendScalars X l E.1 F.1 ⋙ toQlbar X l F ≅ toQlbar X l E :=
  NatIso.ofComponents
    (fun K ↦ DerivedCategoryConstructibleQlbar.isoMk
      ((extendScalarsQlbarComp X l E.1 F.1).app K).symm)
    fun f ↦ by ext; exact ((extendScalarsQlbarComp X l E.1 F.1).inv.naturality f)

end DerivedCategoryConstructibleRational
