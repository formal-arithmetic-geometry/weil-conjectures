/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Basic

/-!
# Algebras of an endofunctor with invertible structure morphism

Let `F : C ⥤ C` be an endofunctor. An algebra of `F` in the sense of
`CategoryTheory.Endofunctor.Algebra` is an object `a` of `C` together with a morphism
`str : F.obj a ⟶ a`. This file studies the algebras whose structure morphism is an
isomorphism: the object property `CategoryTheory.Endofunctor.Algebra.IsIsoStr` and the
full subcategory `CategoryTheory.Endofunctor.IsoAlgebra` it cuts out. Since a morphism of
algebras carries no condition beyond the commuting square, `IsoAlgebra F` is a full
subcategory of `Algebra F` and inherits its category structure, its forgetful functor and
its `ext` and `isoMk` lemmas.

The structure isomorphism of such an algebra can be iterated: `IsoAlgebra.strIterate`
is the composite `Φ^[n] : Fⁿ a ≅ a`. This is the form in which Frobenius structures
appear: a Weil sheaf on a scheme over a finite field is an algebra with invertible
structure morphism for the Frobenius pullback, and the `n`-fold Frobenius operators of
the trace formula are the images of `strIterate n`.

Algebras are also transported along a functor `L : C ⥤ D` equipped with a commutation
datum with the endofunctors: `Algebra.mapOfNatTrans` for a natural transformation
`e : L ⋙ G ⟶ F ⋙ L`, and `IsoAlgebra.mapOfNatIso` for an isomorphism. The case `L = 𝟭 C` is
`CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`.

## Main definitions

- `CategoryTheory.Endofunctor.Algebra.mapOfNatTrans`: transport of algebras along a
  functor equipped with a commutation transformation with the endofunctors.
- `CategoryTheory.Endofunctor.Algebra.IsIsoStr`: the property of an algebra that its
  structure morphism is an isomorphism.
- `CategoryTheory.Endofunctor.IsoAlgebra`: the category of algebras with invertible
  structure morphism, with its structure isomorphism `IsoAlgebra.str`, its forgetful
  functor `IsoAlgebra.forget`, the iterated structure isomorphism
  `IsoAlgebra.strIterate` and the transport `IsoAlgebra.mapOfNatIso`.
-/

@[expose] public section

namespace CategoryTheory.Endofunctor

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Algebra

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D}

/-- Transport of algebras of `F : C ⥤ C` to algebras of `G : D ⥤ D` along a functor
`L : C ⥤ D` equipped with a commutation transformation `e : L ⋙ G ⟶ F ⋙ L`: an algebra
`(a, str)` of `F` is sent to `L a` with the structure morphism

```
        e.app a          L str
G (L a) -------> L (F a) -------> L a
```

The case `L = 𝟭 C` is `CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`. -/
@[simps]
def mapOfNatTrans (e : L ⋙ G ⟶ F ⋙ L) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := L.obj A.a
      str := e.app A.a ≫ L.map A.str }
  map {A B} φ :=
    { f := L.map φ.f
      h := by
        have h := e.naturality φ.f
        simp only [Functor.comp_map] at h
        rw [reassoc_of% h, ← L.map_comp, φ.h, L.map_comp, Category.assoc] }
  map_id A := Algebra.ext (L.map_id A.a)
  map_comp φ ψ := Algebra.ext (L.map_comp φ.f ψ.f)

end Map

/-- The property of an algebra of an endofunctor that its structure morphism is an
isomorphism. The full subcategory it cuts out is
`CategoryTheory.Endofunctor.IsoAlgebra`. -/
def IsIsoStr (F : C ⥤ C) : ObjectProperty (Algebra F) :=
  fun A ↦ IsIso A.str

end Algebra

/-- The category of algebras of an endofunctor `F : C ⥤ C` whose structure morphism is an
isomorphism, the full subcategory of `CategoryTheory.Endofunctor.Algebra F` cut out by
`CategoryTheory.Endofunctor.Algebra.IsIsoStr`. An object is an object `a` of `C` together
with an isomorphism `Φ : F.obj a ≅ a`, and a morphism is a morphism of the underlying
objects commuting with the structure isomorphisms. -/
def IsoAlgebra (F : C ⥤ C) : Type max u v :=
  (Algebra.IsIsoStr F).FullSubcategory

namespace IsoAlgebra

variable {F : C ⥤ C}

instance : Category (IsoAlgebra F) :=
  inferInstanceAs (Category (Algebra.IsIsoStr F).FullSubcategory)

instance (K : IsoAlgebra F) : IsIso K.obj.str :=
  K.property

/-- The inclusion of the algebras with invertible structure morphism into all
algebras. -/
def ι (F : C ⥤ C) : IsoAlgebra F ⥤ Algebra F :=
  (Algebra.IsIsoStr F).ι

/-- The underlying object of an algebra with invertible structure morphism. -/
abbrev carrier (K : IsoAlgebra F) : C :=
  K.obj.a

/-- The structure isomorphism `Φ : F.obj a ≅ a` of an algebra with invertible structure
morphism. -/
noncomputable def str (K : IsoAlgebra F) : F.obj K.carrier ≅ K.carrier :=
  asIso K.obj.str

@[simp]
lemma str_hom (K : IsoAlgebra F) : K.str.hom = K.obj.str :=
  rfl

/-- The algebra with invertible structure morphism given by an object `a` and an
isomorphism `Φ : F.obj a ≅ a`. -/
def mk (a : C) (Φ : F.obj a ≅ a) : IsoAlgebra F :=
  ⟨{ a := a, str := Φ.hom }, inferInstanceAs (IsIso Φ.hom)⟩

@[simp]
lemma mk_carrier (a : C) (Φ : F.obj a ≅ a) : (mk a Φ).carrier = a :=
  rfl

@[simp]
lemma mk_str (a : C) (Φ : F.obj a ≅ a) : (mk a Φ).str = Φ :=
  Iso.ext rfl

/-- The forgetful functor to the underlying category, discarding the structure
isomorphisms. -/
def forget (F : C ⥤ C) : IsoAlgebra F ⥤ C :=
  ι F ⋙ Algebra.forget F

@[simp]
lemma forget_obj (K : IsoAlgebra F) : (forget F).obj K = K.carrier :=
  rfl

@[simp]
lemma forget_map {K L : IsoAlgebra F} (φ : K ⟶ L) : (forget F).map φ = φ.hom.f :=
  rfl

/-- The coherently iterated structure isomorphism `Φ^[n] : Fⁿ a ≅ a`, defined recursively
by `Φ^[0] = 𝟙 a` and `Φ^[n + 1] = Φ ∘ F(Φ^[n])`. The `n`-fold Frobenius operators of the
trace formula are functorial images of these isomorphisms; they are not separately chosen
operators. -/
noncomputable def strIterate (K : IsoAlgebra F) : ∀ n : ℕ, (F.iterate n).obj K.carrier ≅ K.carrier
  | 0 => Iso.refl K.carrier
  | n + 1 => F.mapIso (K.strIterate n) ≪≫ K.str

@[simp]
lemma strIterate_zero (K : IsoAlgebra F) : K.strIterate 0 = Iso.refl K.carrier :=
  rfl

@[simp]
lemma strIterate_succ (K : IsoAlgebra F) (n : ℕ) :
    K.strIterate (n + 1) = F.mapIso (K.strIterate n) ≪≫ K.str :=
  rfl

@[simp]
lemma strIterate_one (K : IsoAlgebra F) : K.strIterate 1 = K.str := by
  ext
  simp

section Map

variable {G : D ⥤ D} {L : C ⥤ D}

/-- Transport of algebras with invertible structure morphism along a functor `L : C ⥤ D`
equipped with a commutation isomorphism `e : L ⋙ G ≅ F ⋙ L`: the restriction of
`CategoryTheory.Endofunctor.Algebra.mapOfNatTrans`, which is well defined since the
transported structure morphism

```
        e.app a          L Φ
G (L a) -------> L (F a) -----> L a
```

is again an isomorphism. -/
noncomputable def mapOfNatIso (e : L ⋙ G ≅ F ⋙ L) : IsoAlgebra F ⥤ IsoAlgebra G :=
  (Algebra.IsIsoStr G).lift (ι F ⋙ Algebra.mapOfNatTrans e.hom) fun K ↦ by
    change IsIso (e.hom.app K.carrier ≫ L.map K.obj.str)
    have : IsIso (e.hom.app K.carrier) := (e.app K.carrier).isIso_hom
    infer_instance

@[simp]
lemma mapOfNatIso_obj_carrier (e : L ⋙ G ≅ F ⋙ L) (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).carrier = L.obj K.carrier :=
  rfl

@[simp]
lemma mapOfNatIso_obj_str (e : L ⋙ G ≅ F ⋙ L) (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).str = e.app K.carrier ≪≫ L.mapIso K.str :=
  Iso.ext rfl

@[simp]
lemma mapOfNatIso_map_hom_f (e : L ⋙ G ≅ F ⋙ L) {K L' : IsoAlgebra F} (φ : K ⟶ L') :
    ((mapOfNatIso e).map φ).hom.f = L.map φ.hom.f :=
  rfl

end Map

section Map₂

variable {F₁ : C ⥤ C} {F₂ : D ⥤ D}

/-- A pair of algebras with invertible structure morphism, for `F₁` and `F₂`, is an algebra with
invertible structure morphism for the product endofunctor `F₁.prod F₂`, with structure
isomorphism `Φ_K × Φ_L`. -/
noncomputable def prod : IsoAlgebra F₁ × IsoAlgebra F₂ ⥤ IsoAlgebra (F₁.prod F₂) where
  obj KL := mk (KL.1.carrier, KL.2.carrier) (KL.1.str.prod KL.2.str)
  map {KL KL'} φ := ObjectProperty.homMk
    { f := (φ.1.hom.f, φ.2.hom.f)
      h := Prod.ext φ.1.hom.h φ.2.hom.h }

@[simp]
lemma prod_obj_carrier (KL : IsoAlgebra F₁ × IsoAlgebra F₂) :
    (prod.obj KL).carrier = (KL.1.carrier, KL.2.carrier) :=
  rfl

@[simp]
lemma prod_obj_str (KL : IsoAlgebra F₁ × IsoAlgebra F₂) :
    (prod.obj KL).str = KL.1.str.prod KL.2.str :=
  mk_str _ _

variable {E : Type*} [Category* E] {G : E ⥤ E} (B : C ⥤ D ⥤ E)

/-- Transport of algebras with invertible structure morphism along a bifunctor
`B : C ⥤ D ⥤ E` equipped with a commutation isomorphism
`e_{a,b} : G (B a b) ≅ B (F₁ a) (F₂ b)`, natural in `a` and `b` (an isomorphism of functors
`C × D ⥤ E`): the pair `(K, L)` is sent to `B K L` with the structure isomorphism

```
             e                  B Φ_K Φ_L
G (B K L) -------> B (F₁ K) (F₂ L) ---------> B K L
```

It is the one-variable transport `mapOfNatIso e` along `uncurry B`, applied to the product
algebra `prod.obj (K, L)` and curried. This is the transport of Weil structures along a tensor
product. -/
noncomputable def mapOfNatIso₂
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B) :
    IsoAlgebra F₁ ⥤ IsoAlgebra F₂ ⥤ IsoAlgebra G :=
  Functor.curry.obj (prod ⋙ mapOfNatIso e)

@[simp]
lemma mapOfNatIso₂_obj_obj_carrier
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B)
    (K : IsoAlgebra F₁) (L : IsoAlgebra F₂) :
    (((mapOfNatIso₂ B e).obj K).obj L).carrier = (B.obj K.carrier).obj L.carrier :=
  rfl

lemma mapOfNatIso₂_obj_obj_str
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B)
    (K : IsoAlgebra F₁) (L : IsoAlgebra F₂) :
    (((mapOfNatIso₂ B e).obj K).obj L).str =
      e.app (K.carrier, L.carrier) ≪≫ (Functor.uncurry.obj B).mapIso (K.str.prod L.str) := by
  ext
  simp [mapOfNatIso₂]

end Map₂

end IsoAlgebra

end CategoryTheory.Endofunctor
