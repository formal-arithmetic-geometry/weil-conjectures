/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructiblePullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.WeilSheaf.GeometricFrobenius

/-!

# Weil sheaves and Weil complexes

For an endofunctor `G : C ⥤ C`, a *Weil object* is a pair `(K, Φ)` of an object
`K : C` together with an isomorphism `Φ : G.obj K ≅ K`. The isomorphism `Φ` is
structure data, not the proposition that some isomorphism exists. A morphism of Weil
objects `(K, Φ_K) ⟶ (L, Φ_L)` is a morphism `u : K ⟶ L` commuting with the structure
isomorphisms, `u ∘ Φ_K = Φ_L ∘ G.map u`. This defines the category
`CategoryTheory.WeilObject G`, a strict variant of `CategoryTheory.Endofunctor.Algebra`
in which the structure morphism is an isomorphism. No group-action formalism is
required: one generator `G` together with the coherently iterated structure
isomorphisms `WeilObject.strIterate` is sufficient.

Now let `X₀` be a scheme over a finite field `k` with structure morphism
`f : X₀ ⟶ Spec k`, and let `X` be its geometric fiber with geometric Frobenius
`g_X : X ≅ X` (see `WeilConjectures.WeilSheaf.GeometricFrobenius`). Pullback along
`g_X` is an endofunctor

- `G_X = g_X^*` of the category of étale sheaves on `X` with coefficients in a
  category `A` (`AlgebraicGeometry.Etale.frobeniusPullback`), and, being exact, it
  induces an endofunctor
- of the derived category of étale sheaves on `X`
  (`AlgebraicGeometry.Etale.derivedFrobeniusPullback`).

A *Weil sheaf* on `X` is an étale sheaf `F` together with an isomorphism
`Φ : G_X F ≅ F`; a *Weil complex* on `X` is an object `K` of the derived category of
étale sheaves together with an isomorphism `Φ : G_X K ≅ K`. These are the categories
`AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`, obtained by
specializing `CategoryTheory.WeilObject` to the Frobenius pullback endofunctors.

Since the pullback `g_X^*` on sheaves is exact, its action on the derived category is
the localization of its termwise action on complexes
(`CategoryTheory.Functor.mapDerivedCategory`); no unbounded left derived functor
machinery is needed for the Frobenius pullback. Two further layers are provided here:

- Since the derived pullback preserves the bounded constructible subcategory
  `Dᵇc(X, A)` (assumed in `WeilConjectures.DerivedCategory.ConstructiblePullback`), the
  Frobenius pullback restricts to an endofunctor of `Dᵇc(X, A)` and yields the category
  `AlgebraicGeometry.WeilComplexBoundedConstructible` of bounded constructible Weil
  complexes.
- Since `G_X` is t-exact, a Weil complex induces for every `n` a Weil sheaf structure
  `g_X^* Hⁿ(K) ≅ Hⁿ(G_X K) ≅ Hⁿ(K)` on its `n`-th homology sheaf. This is packaged as
  the functors `AlgebraicGeometry.WeilComplex.homologyFunctor` and
  `AlgebraicGeometry.WeilComplexBoundedConstructible.homologyFunctor` into
  `AlgebraicGeometry.WeilSheaf`, built from the general transport of Weil objects
  `CategoryTheory.WeilObject.map` along the homology commutation isomorphism
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` of the exact functor
  `g_X^*`.

The canonical Weil structure on objects descended from `X₀` and the transport of Weil
structures through `Rf_!` are subsequent layers built on top of these definitions.

## Main definitions

- `CategoryTheory.Functor.iterate`: the `n`-fold composition of an endofunctor.
- `CategoryTheory.WeilObject`: the category of objects with a `G`-equivariance
  isomorphism.
- `CategoryTheory.WeilObject.forget`: the forgetful functor to the underlying category.
- `CategoryTheory.WeilObject.strIterate`: the coherently iterated structure isomorphism
  `Φ^[n] : Gⁿ K ≅ K`, defined recursively by `Φ^[0] = 𝟙` and
  `Φ^[n+1] = Φ ∘ G(Φ^[n])`.
- `CategoryTheory.WeilObject.map`: transport of Weil objects along a functor equipped
  with a commutation isomorphism with the endofunctors.
- `AlgebraicGeometry.Etale.frobeniusPullback`: the Frobenius pullback endofunctor
  `G_X = g_X^*` on étale sheaves on the geometric fiber.
- `AlgebraicGeometry.WeilSheaf`: the category of Weil sheaves on the geometric fiber.
- `AlgebraicGeometry.Etale.derivedFrobeniusPullback`: the Frobenius pullback
  endofunctor on the derived category of étale sheaves on the geometric fiber.
- `AlgebraicGeometry.WeilComplex`: the category of Weil complexes on the geometric
  fiber.
- `AlgebraicGeometry.WeilComplex.homologyFunctor`: the Weil sheaf structure on the
  homology sheaves of a Weil complex.
- `AlgebraicGeometry.Etale.derivedFrobeniusPullbackBoundedConstructible`: the Frobenius
  pullback endofunctor on the bounded constructible derived category `Dᵇc(X, A)`.
- `AlgebraicGeometry.WeilComplexBoundedConstructible`: the category of bounded
  constructible Weil complexes, with its comparison functor `toWeilComplex` and the
  Weil sheaf structure `homologyFunctor` on its homology sheaves.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold composition of an endofunctor, with `G.iterate 0 = 𝟭 C` and
`G.iterate (n + 1) = G.iterate n ⋙ G`. -/
def Functor.iterate (G : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => G.iterate n ⋙ G

@[simp]
lemma Functor.iterate_zero (G : C ⥤ C) : G.iterate 0 = 𝟭 C :=
  rfl

@[simp]
lemma Functor.iterate_succ (G : C ⥤ C) (n : ℕ) : G.iterate (n + 1) = G.iterate n ⋙ G :=
  rfl

/-- A *Weil object* for an endofunctor `G : C ⥤ C` is an object `K` of `C` together
with an isomorphism `Φ : G.obj K ≅ K`. The isomorphism is structure data. For the
Frobenius pullback endofunctor on étale sheaves on the geometric fiber of a scheme over
a finite field this specializes to Weil sheaves and Weil complexes. -/
structure WeilObject (G : C ⥤ C) : Type max u v where
  /-- The underlying object. -/
  obj : C
  /-- The structure isomorphism `Φ : G.obj K ≅ K`. -/
  str : G.obj obj ≅ obj

namespace WeilObject

variable {G : C ⥤ C}

/-- A morphism of Weil objects `(K, Φ_K) ⟶ (L, Φ_L)` is a morphism `u : K ⟶ L` of the
underlying objects satisfying `u ∘ Φ_K = Φ_L ∘ G.map u`. -/
@[ext]
structure Hom (K L : WeilObject G) where
  /-- The underlying morphism. -/
  hom : K.obj ⟶ L.obj
  /-- The compatibility with the structure isomorphisms. -/
  comm : G.map hom ≫ L.str.hom = K.str.hom ≫ hom := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (WeilObject G) where
  Hom := Hom
  id K := { hom := 𝟙 K.obj }
  comp φ ψ := { hom := φ.hom ≫ ψ.hom }
  id_comp φ := Hom.ext (Category.id_comp φ.hom)
  comp_id φ := Hom.ext (Category.comp_id φ.hom)
  assoc φ ψ χ := Hom.ext (Category.assoc φ.hom ψ.hom χ.hom)

@[ext]
lemma hom_ext {K L : WeilObject G} {φ ψ : K ⟶ L} (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

@[simp]
lemma id_hom (K : WeilObject G) : Hom.hom (𝟙 K) = 𝟙 K.obj :=
  rfl

@[simp]
lemma comp_hom {K L M : WeilObject G} (φ : K ⟶ L) (ψ : L ⟶ M) :
    (φ ≫ ψ).hom = φ.hom ≫ ψ.hom :=
  rfl

/-- The forgetful functor from Weil objects to the underlying category, discarding the
structure isomorphisms. -/
@[simps]
def forget (G : C ⥤ C) : WeilObject G ⥤ C where
  obj K := K.obj
  map φ := φ.hom

/-- The coherently iterated structure isomorphism `Φ^[n] : Gⁿ K ≅ K` of a Weil object,
defined recursively by `Φ^[0] = 𝟙 K` and `Φ^[n+1] = Φ ∘ G(Φ^[n])`. The `n`-fold
Frobenius operators of the trace formula are functorial images of these isomorphisms;
they are not separately chosen operators. -/
def strIterate (K : WeilObject G) : ∀ n : ℕ, (G.iterate n).obj K.obj ≅ K.obj
  | 0 => Iso.refl K.obj
  | n + 1 => G.mapIso (K.strIterate n) ≪≫ K.str

@[simp]
lemma strIterate_zero (K : WeilObject G) : K.strIterate 0 = Iso.refl K.obj :=
  rfl

lemma strIterate_succ (K : WeilObject G) (n : ℕ) :
    K.strIterate (n + 1) = G.mapIso (K.strIterate n) ≪≫ K.str :=
  rfl

@[simp]
lemma strIterate_one (K : WeilObject G) :
    K.strIterate 1 = G.mapIso (Iso.refl K.obj) ≪≫ K.str :=
  rfl

section Map

variable {D : Type u'} [Category.{v'} D]

/-- Transport of Weil objects along a functor `F : C ⥤ D` equipped with a commutation
isomorphism `e : F ⋙ H ≅ G ⋙ F` with the endofunctors: a Weil object `(K, Φ)` for `G`
is sent to `F K` with the structure isomorphism `H (F K) ≅ F (G K) ≅ F K`. For the
homology functor on the derived category of étale sheaves, equipped with the
commutation isomorphism expressing the t-exactness of the Frobenius pullback, this
sends Weil complexes to the Weil sheaves on their homology. -/
def map {H : D ⥤ D} {F : C ⥤ D} (e : F ⋙ H ≅ G ⋙ F) :
    WeilObject G ⥤ WeilObject H where
  obj K :=
    { obj := F.obj K.obj
      str := e.app K.obj ≪≫ F.mapIso K.str }
  map {K L} φ :=
    { hom := F.map φ.hom
      comm := by
        have h := e.hom.naturality φ.hom
        simp only [Functor.comp_map] at h
        simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
        rw [reassoc_of% h, ← F.map_comp, φ.comm, F.map_comp, Category.assoc] }
  map_id K := hom_ext (F.map_id K.obj)
  map_comp φ ψ := hom_ext (F.map_comp φ.hom ψ.hom)

end Map

end WeilObject

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

section WeilSheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]
variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The Frobenius pullback endofunctor `G_X := g_X^*` on étale sheaves on the geometric
fiber `X` of a scheme over a finite field, the pullback along the geometric Frobenius
`g_X`. -/
noncomputable abbrev Etale.frobeniusPullback :
    Sheaf (f.geometricFiber).smallEtaleTopology A ⥤
      Sheaf (f.geometricFiber).smallEtaleTopology A :=
  Etale.upperStar A f.geometricFrobenius.hom

/-- A *Weil sheaf* on the geometric fiber `X` of a scheme over a finite field is an
étale sheaf `F` on `X` together with an isomorphism `Φ : g_X^* F ≅ F` along the
geometric Frobenius. The isomorphism `Φ` is structure data. Morphisms are morphisms of
sheaves commuting with the structure isomorphisms. -/
noncomputable def WeilSheaf : Type _ :=
  WeilObject (Etale.frobeniusPullback A f)

noncomputable instance : Category (WeilSheaf A f) :=
  inferInstanceAs (Category (WeilObject (Etale.frobeniusPullback A f)))

/-- The forgetful functor from Weil sheaves on the geometric fiber to étale sheaves,
discarding the Frobenius structure isomorphisms. -/
noncomputable def WeilSheaf.forget :
    WeilSheaf A f ⥤ Sheaf (f.geometricFiber).smallEtaleTopology A :=
  WeilObject.forget (Etale.frobeniusPullback A f)

end WeilSheaf

section WeilComplex

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The Frobenius pullback endofunctor `G_X` on the derived category of étale sheaves
on the geometric fiber `X` of a scheme over a finite field, induced by the exact
pullback `g_X^*` along the geometric Frobenius. Since `g_X^*` is exact, this is the
correct derived pullback: no left derived functor machinery is needed. -/
noncomputable abbrev Etale.derivedFrobeniusPullback :
    DerivedCategory (Sheaf (f.geometricFiber).smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf (f.geometricFiber).smallEtaleTopology A) :=
  (Etale.frobeniusPullback A f).mapDerivedCategory

/-- A *Weil complex* on the geometric fiber `X` of a scheme over a finite field is an
object `K` of the derived category of étale sheaves on `X` together with an
isomorphism `Φ : G_X K ≅ K` along the derived Frobenius pullback. The isomorphism `Φ`
is structure data. Morphisms are morphisms of the derived category commuting with the
structure isomorphisms. -/
noncomputable def WeilComplex : Type _ :=
  WeilObject (Etale.derivedFrobeniusPullback A f)

noncomputable instance : Category (WeilComplex A f) :=
  inferInstanceAs (Category (WeilObject (Etale.derivedFrobeniusPullback A f)))

/-- The forgetful functor from Weil complexes on the geometric fiber to the derived
category of étale sheaves, discarding the Frobenius structure isomorphisms. -/
noncomputable def WeilComplex.forget :
    WeilComplex A f ⥤ DerivedCategory (Sheaf (f.geometricFiber).smallEtaleTopology A) :=
  WeilObject.forget (Etale.derivedFrobeniusPullback A f)

/-- Since the Frobenius pullback `g_X^*` is t-exact, the `n`-th homology sheaf of a
Weil complex carries the induced Weil sheaf structure
`g_X^* Hⁿ(K) ≅ Hⁿ(G_X K) ≅ Hⁿ(K)`: the transport of the Weil structure along the
homology functor via the commutation isomorphism
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`. -/
noncomputable def WeilComplex.homologyFunctor (n : ℤ) :
    WeilComplex A f ⥤ WeilSheaf A f :=
  WeilObject.map
    ((Etale.frobeniusPullback A f).mapDerivedCategoryHomologyFunctorIso n)

end WeilComplex

section WeilComplexBoundedConstructible

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The Frobenius pullback endofunctor `G_X` on the bounded constructible derived
category `Dᵇc(X, A)` of the geometric fiber: the restriction of
`Etale.derivedFrobeniusPullback`, using that the derived pullback preserves bounded
constructible objects
(`Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory`). -/
noncomputable def Etale.derivedFrobeniusPullbackBoundedConstructible :
    Dᵇc(f.geometricFiber, A) ⥤ Dᵇc(f.geometricFiber, A) :=
  (Etale.DerivedCategory.boundedConstructible A f.geometricFiber).lift
    (Etale.DerivedCategoryBoundedConstructible.ι A f.geometricFiber ⋙
      Etale.derivedFrobeniusPullback A f)
    (fun K ↦ Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory A
      f.geometricFrobenius.hom K.property)

/-- A *bounded constructible Weil complex* on the geometric fiber `X` of a scheme over
a finite field is an object `K` of the bounded constructible derived category
`Dᵇc(X, A)` together with an isomorphism `Φ : G_X K ≅ K` along the Frobenius pullback.
The isomorphism `Φ` is structure data. Morphisms are morphisms of `Dᵇc(X, A)` commuting
with the structure isomorphisms. -/
noncomputable def WeilComplexBoundedConstructible : Type _ :=
  WeilObject (Etale.derivedFrobeniusPullbackBoundedConstructible A f)

noncomputable instance : Category (WeilComplexBoundedConstructible A f) :=
  inferInstanceAs
    (Category (WeilObject (Etale.derivedFrobeniusPullbackBoundedConstructible A f)))

/-- The forgetful functor from bounded constructible Weil complexes to `Dᵇc(X, A)`,
discarding the Frobenius structure isomorphisms. -/
noncomputable def WeilComplexBoundedConstructible.forget :
    WeilComplexBoundedConstructible A f ⥤ Dᵇc(f.geometricFiber, A) :=
  WeilObject.forget (Etale.derivedFrobeniusPullbackBoundedConstructible A f)

/-- A bounded constructible Weil complex is in particular a Weil complex: the inclusion
of `Dᵇc(X, A)` into the derived category commutes definitionally with the Frobenius
pullbacks and transports the Weil structure. -/
noncomputable def WeilComplexBoundedConstructible.toWeilComplex :
    WeilComplexBoundedConstructible A f ⥤ WeilComplex A f :=
  WeilObject.map
    (F := Etale.DerivedCategoryBoundedConstructible.ι A f.geometricFiber) (Iso.refl _)

/-- The Weil sheaf structure on the `n`-th homology sheaf of a bounded constructible
Weil complex, obtained through the underlying Weil complex. -/
noncomputable def WeilComplexBoundedConstructible.homologyFunctor (n : ℤ) :
    WeilComplexBoundedConstructible A f ⥤ WeilSheaf A f :=
  WeilComplexBoundedConstructible.toWeilComplex A f ⋙ WeilComplex.homologyFunctor A f n

end WeilComplexBoundedConstructible

end AlgebraicGeometry

end
