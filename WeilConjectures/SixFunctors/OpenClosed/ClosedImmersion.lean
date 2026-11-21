/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.SixFunctors.OpenClosed.Stalk

/-!

# The pushforward along a closed immersion is fully faithful

For a closed immersion `i : Z ⟶ X` the pushforward `i_*` of étale sheaves is fully
faithful: the counit of `i^* ⊣ i_*` is an isomorphism, so `i^* i_* H ≅ H` naturally in the
sheaf `H` on `Z`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarCompComapSheafFiberIso`: the stalk of `i_* H` at the
  point `Φ.comap i.Etale` of `X` is the stalk of `H` at `s`.
- `AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit`: the counit of
  `i^* ⊣ i_*` is an isomorphism.
- `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`, with the corresponding `Full` and
  `Faithful` instances: the pushforward along a closed immersion is fully faithful.

## Implementation details

Being an isomorphism is checked at the geometric points `s` of `Z`, with fibre functor
`Φ = pointSmallEtale s`. Transposing along the composed adjunction
`i^* ⋙ Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor ⋙ i_*` reduces this to identifying the stalk
of `i_* H` at `Φ.comap i.Etale` with the stalk of `H` at `s`; this is
`AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso` transported along
`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso`. The inverse image point is used because
its skyscraper sheaf functor is, on the nose, that of `s` followed by `i_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

/-- **The stalk of a pushforward along a closed immersion, at the inverse image point.**
For a closed immersion `i : Z ⟶ X` and a geometric point `s : Spec Ω ⟶ Z`, the stalk of
`i_* H` at the point `(pointSmallEtale s).comap i.Etale` of the small étale site of `X` is
the stalk of `H` at `s`, naturally in the sheaf `H`. -/
noncomputable def Etale.lowerStarCompComapSheafFiberIso :
    (i)_*[A] ⋙ ((pointSmallEtale s).comap i.Etale (Hom.coverPreserving_etale i)).sheafFiber ≅
      (pointSmallEtale s).sheafFiber :=
  Functor.isoWhiskerLeft _
      (GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso i s)) ≪≫
    Etale.lowerStarCompSheafFiberIso A i s

omit [HasSmallSiteSheafify A] in
/-- `AlgebraicGeometry.Etale.lowerStarCompComapSheafFiberIso` is compatible with the
canonical maps from the sections: a section of `H` over `V ×_X Z`, that is a section of
`i_* H` over `V`, has the same germ at `x` computed in either stalk. In other words the
triangle of germ maps
```
                        (i_* H)(V) = H(V ×_X Z)
                       / \
     toPresheafFiber at (V, x) toPresheafFiber at (V ×_X Z, x)
                     / \
                    ↓ ↓
  ((i_* H) at Φ.comap i.Etale) --- lowerStarCompComapSheafFiberIso ---> (H at s)
```
commutes, where `Φ = pointSmallEtale s`. -/
@[reassoc]
lemma Etale.toPresheafFiber_lowerStarCompComapSheafFiberIso_hom_app
    (H : Sheaf Z.smallEtaleTopology A) (V : X.Etale)
    (x : ((pointSmallEtale s).comap i.Etale (Hom.coverPreserving_etale i)).fiber.obj V) :
    ((pointSmallEtale s).comap i.Etale (Hom.coverPreserving_etale i)).toPresheafFiber V x
          ((i)_*[A].obj H).obj ≫
        (Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H =
      (pointSmallEtale s).toPresheafFiber (i.Etale.obj V) x H.obj := by
  have h₁ : (Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H =
      (GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso i s)).hom.app
        ((i)_*[A].obj H) ≫ (Etale.lowerStarCompPresheafFiberIso A i s).hom.app H.obj := rfl
  have h₂ : ((pointSmallEtale s).comap i.Etale (Hom.coverPreserving_etale i)).toPresheafFiber
        V x ((i)_*[A].obj H).obj ≫
      (GrothendieckTopology.Point.sheafFiberIso (pointSmallEtaleComapIso i s)).hom.app
        ((i)_*[A].obj H) =
      (pointSmallEtale (s ≫ i)).toPresheafFiber V
        ((pointSmallEtaleFiberEtaleIso i s).hom.app V x) (i.Etale.op ⋙ H.obj) := by
    simp only [GrothendieckTopology.Point.sheafFiberIso_hom,
      GrothendieckTopology.Point.Hom.sheafFiber, Functor.whiskerLeft_app,
      GrothendieckTopology.Point.Hom.presheafFiber_app,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
    rfl
  rw [h₁, ← Category.assoc, h₂,
    Etale.toPresheafFiber_lowerStarCompPresheafFiberIso_hom_app A i s H.obj V
      ((pointSmallEtaleFiberEtaleIso i s).hom.app V x),
    (pointSmallEtaleFiberEtaleIso i s).hom_inv_id_app_apply V x]

omit [HasSmallSiteSheafify A] in
/-- Pushing a morphism `H ⟶ Φ.skyscraperSheaf M` forward along `i_*` is, up to the
adjunction between the stalk at `Φ.comap i.Etale` and its skyscraper sheaf functor, the
same as composing with the stalk comparison
`AlgebraicGeometry.Etale.lowerStarCompComapSheafFiberIso`. -/
private lemma Etale.lowerStar_map_skyscraperSheafAdjunction_homEquiv
    (H : Sheaf Z.smallEtaleTopology A) (M : A)
    (g : (pointSmallEtale s).sheafFiber.obj H ⟶ M) :
    (i)_*[A].map ((pointSmallEtale s).skyscraperSheafAdjunction.homEquiv H M g) =
      ((pointSmallEtale s).comap i.Etale
          (Hom.coverPreserving_etale i)).skyscraperSheafAdjunction.homEquiv
        ((i)_*[A].obj H) M
        ((Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H ≫ g) := by
  have e₁ := (pointSmallEtale s).skyscraperSheafAdjunction_homEquiv_apply_hom
    (F := H) (M := M) g
  have e₂ := ((pointSmallEtale s).comap i.Etale
      (Hom.coverPreserving_etale i)).skyscraperSheafAdjunction_homEquiv_apply_hom
    (F := (i)_*[A].obj H) (M := M)
    ((Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H ≫ g)
  apply Sheaf.hom_ext
  ext ⟨V⟩ : 2
  apply Limits.Pi.hom_ext
  intro y
  have hl := congrArg (fun (t : H.obj ⟶ (pointSmallEtale s).skyscraperPresheaf M) ↦
    t.app (op (i.Etale.obj V)) ≫ Pi.π (fun _ ↦ M) y) e₁
  have hr := congrArg (fun (t : ((i)_*[A].obj H).obj ⟶ ((pointSmallEtale s).comap i.Etale
      (Hom.coverPreserving_etale i)).skyscraperPresheaf M) ↦
    t.app (op V) ≫ Pi.π (fun _ ↦ M) y) e₂
  -- the two sides are computed in five steps, each of which is one lemma
  have h₁ := (pointSmallEtale s).skyscraperPresheafHomEquiv_app_π g (i.Etale.obj V) y
  have h₂ := (Etale.toPresheafFiber_lowerStarCompComapSheafFiberIso_hom_app_assoc
    A i s H V y g).symm
  have h₃ := (((pointSmallEtale s).comap i.Etale
    (Hom.coverPreserving_etale i)).skyscraperPresheafHomEquiv_app_π
      ((Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H ≫ g) V y).symm
  -- `i_*` of the transpose of `g`, evaluated at `V` and projected to the factor `y`
  refine hl.trans ?_
  -- is the germ map of `H` at `(i.Etale.obj V, y)` followed by `g`
  refine h₁.trans ?_
  -- which is the germ map of `i_* H` at `(V, y)`, the stalk comparison, and then `g`
  refine h₂.trans ?_
  -- that is the transpose at `Φ.comap i.Etale` of the stalk comparison followed by `g`
  refine h₃.trans ?_
  -- evaluated at `V` and projected to the factor `y`
  exact hr.symm

omit [HasSmallSiteSheafify A] in
/-- **The stalk at a geometric point of `Z` of the counit of `i^* ⊣ i_*` is an
isomorphism**, for a closed immersion `i : Z ⟶ X`. -/
theorem Etale.isIso_sheafFiber_map_upperStarLowerStarAdjunction_counit_app
    (H : Sheaf Z.smallEtaleTopology A) :
    IsIso ((pointSmallEtale s).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction A i).counit.app H)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  set e₁ := ((Etale.upperStarLowerStarAdjunction A i).comp
    (pointSmallEtale s).skyscraperSheafAdjunction).homEquiv ((i)_*[A].obj H) M
  set e₂ := ((pointSmallEtale s).comap i.Etale
    (Hom.coverPreserving_etale i)).skyscraperSheafAdjunction.homEquiv ((i)_*[A].obj H) M
  rw [← e₁.bijective.of_comp_iff']
  have key : ⇑e₁ ∘ (fun (g : (pointSmallEtale s).sheafFiber.obj H ⟶ M) ↦
      (pointSmallEtale s).sheafFiber.map
        ((Etale.upperStarLowerStarAdjunction A i).counit.app H) ≫ g) =
      ⇑e₂ ∘ (fun (g : (pointSmallEtale s).sheafFiber.obj H ⟶ M) ↦
        (Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H ≫ g) := by
    funext g
    exact (Adjunction.comp_homEquiv_map_counit_app_comp (Etale.upperStarLowerStarAdjunction A i)
      (pointSmallEtale s).skyscraperSheafAdjunction H M g).trans
      (Etale.lowerStar_map_skyscraperSheafAdjunction_homEquiv A i s H M g)
  have h : Function.Bijective (⇑e₂ ∘ fun (g : (pointSmallEtale s).sheafFiber.obj H ⟶ M) ↦
      (Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H ≫ g) :=
    e₂.bijective.comp ((isIso_iff_coyoneda_map_bijective
      ((Etale.lowerStarCompComapSheafFiberIso A i s).hom.app H)).1 inferInstance M)
  rwa [← key] at h

omit [HasSmallSiteSheafify A] in
/-- The universe-lifted form of
`AlgebraicGeometry.Etale.isIso_sheafFiber_map_upperStarLowerStarAdjunction_counit_app`: the
stalk of the counit of `i^* ⊣ i_*` at a geometric point of `Z`, taken at the universe of
the coefficients, is an isomorphism. -/
theorem Etale.isIso_uliftSheafFiber_map_upperStarLowerStarAdjunction_counit_app
    (H : Sheaf Z.smallEtaleTopology A) :
    IsIso ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := A)).map
      ((Etale.upperStarLowerStarAdjunction A i).counit.app H)) := by
  rw [NatIso.isIso_map_iff ((pointSmallEtale s).uliftSheafFiberIso A) _]
  exact Etale.isIso_sheafFiber_map_upperStarLowerStarAdjunction_counit_app A i s H

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)]
  [ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The counit of `i^* ⊣ i_*` is an isomorphism at every sheaf**, for a closed immersion
`i : Z ⟶ X`. -/
instance Etale.isIso_upperStarLowerStarAdjunction_counit_app
    (H : Sheaf Z.smallEtaleTopology A) :
    IsIso ((Etale.upperStarLowerStarAdjunction A i).counit.app H) :=
  Scheme.isIso_of_isIso_sheafFiber_map _ (fun _ ↦
    Etale.isIso_uliftSheafFiber_map_upperStarLowerStarAdjunction_counit_app A i _ H)

include hJ in
/-- **The counit of `i^* ⊣ i_*` is an isomorphism**, for a closed immersion `i : Z ⟶ X`,
that is, `i^* i_* H ≅ H` naturally in the sheaf `H` on `Z`. -/
instance Etale.isIso_upperStarLowerStarAdjunction_counit :
    IsIso (Etale.upperStarLowerStarAdjunction A i).counit :=
  NatIso.isIso_of_isIso_app _

include hJ in
/-- **The pushforward along a closed immersion is fully faithful.** -/
noncomputable def Etale.fullyFaithfulLowerStar : (i)_*[A].FullyFaithful :=
  (Etale.upperStarLowerStarAdjunction A i).fullyFaithfulROfIsIsoCounit

include hJ in
/-- The `Full` half of `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`, as an instance. -/
instance Etale.full_lowerStar : (i)_*[A].Full :=
  (Etale.fullyFaithfulLowerStar A i).full

include hJ in
/-- The `Faithful` half of `AlgebraicGeometry.Etale.fullyFaithfulLowerStar`, as an
instance. -/
instance Etale.faithful_lowerStar : (i)_*[A].Faithful :=
  (Etale.fullyFaithfulLowerStar A i).faithful

end AlgebraicGeometry
