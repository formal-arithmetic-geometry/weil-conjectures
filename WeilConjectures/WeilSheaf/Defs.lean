/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
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
machinery is needed for the Frobenius pullback. The restriction of Weil complexes to
the bounded constructible subcategory `Dᵇc(X, A)`, the canonical Weil structure on
objects descended from `X₀`, and the transport of Weil structures through `Rf_!` are
subsequent layers built on top of these definitions.

## Main definitions

- `CategoryTheory.Functor.iterate`: the `n`-fold composition of an endofunctor.
- `CategoryTheory.WeilObject`: the category of objects with a `G`-equivariance
  isomorphism.
- `CategoryTheory.WeilObject.forget`: the forgetful functor to the underlying category.
- `CategoryTheory.WeilObject.strIterate`: the coherently iterated structure isomorphism
  `Φ^[n] : Gⁿ K ≅ K`, defined recursively by `Φ^[0] = 𝟙` and
  `Φ^[n+1] = Φ ∘ G(Φ^[n])`.
- `AlgebraicGeometry.Etale.upperStar_additive`: the pullback `g^*` on étale sheaves
  with values in a preadditive category is additive.
- `AlgebraicGeometry.Etale.frobeniusPullback`: the Frobenius pullback endofunctor
  `G_X = g_X^*` on étale sheaves on the geometric fiber.
- `AlgebraicGeometry.WeilSheaf`: the category of Weil sheaves on the geometric fiber.
- `AlgebraicGeometry.Etale.derivedFrobeniusPullback`: the Frobenius pullback
  endofunctor on the derived category of étale sheaves on the geometric fiber.
- `AlgebraicGeometry.WeilComplex`: the category of Weil complexes on the geometric
  fiber.

-/

@[expose] public section

universe w v v' u u'

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

end WeilObject

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

section Additive

variable (A : Type u') [Category.{v'} A] [Preadditive A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [∀ F : Y.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F]
variable [HasWeakSheafify Z.smallEtaleTopology A]

/-- The pullback `g^*` on étale sheaves with values in a preadditive category is
additive, being left adjoint to the additive pushforward `g_*`. -/
instance Etale.upperStar_additive : (Etale.upperStar A g).Additive :=
  (Etale.upperStarLowerStarAdjunction A g).left_adjoint_additive

end Additive

section WeilSheaf

variable (A : Type u') [Category.{v'} A]
variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
variable [∀ F : (f.geometricFiber).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ f.geometricFrobenius.hom).op.HasLeftKanExtension F]
variable [HasWeakSheafify (f.geometricFiber).smallEtaleTopology A]

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

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
variable [∀ F : (f.geometricFiber).Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ f.geometricFrobenius.hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory.{w} (Sheaf (f.geometricFiber).smallEtaleTopology A)]

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

end WeilComplex

end AlgebraicGeometry

end
