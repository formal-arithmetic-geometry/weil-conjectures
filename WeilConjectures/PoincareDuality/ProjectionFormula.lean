/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Abstract
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
(`WeilConjectures.PoincareDuality.Abstract`). It is the composite of three canonical maps:

1. the projection morphism `PF^*_g : Rg_* A ⊗ᴸ B ⟶ Rg_* (A ⊗ᴸ Lg^* B)` of the adjunction
   `Lg^* ⊣ Rg_*`, the mate of `Lg^* (Rg_* A ⊗ᴸ B) ≅ Lg^* Rg_* A ⊗ᴸ Lg^* B ⟶ A ⊗ᴸ Lg^* B`
   (`CategoryTheory.Adjunction.projectionMorphism`, using the monoidal structure of `Lg^*` of
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, restricted to `Dᵇc` in
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), at
   `A = Di_! K`;
2. the *inverse* of the projection comparison
   `q_{i,M,N} : Di_! (M ⊗ᴸ Li^* N) ⟶ Di_! M ⊗ᴸ N` of the adjunction `Di_! ⊣ Li^*` along the open
   immersion `i` (`CategoryTheory.Adjunction.projectionComparison`), which is an isomorphism
   (`ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`): this is the derived
   projection formula for the extension by zero;
3. the identification `Li^* Lg^* B ≅ Lf^* B`.

## Main definitions

- `ProEtale.CondensedRing.properProjectionMorphism`: `PF^*_g` for any morphism `g` (the name
  records that it is only expected to be an isomorphism for `g` proper).
- `ProEtale.CondensedRing.openImmersionProjectionComparison`: `q_j` for an open immersion `j`.
- `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification`: `PF^!_f` with
  respect to a compactification, on the unbounded derived categories.
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism`: `PF^!_f` on
  bounded constructible complexes, for a morphism `f` of separated `k`-schemes of finite type
  and the compactification `compactificationOverField f` defining
  `boundedConstructibleLowerShriek`.
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection`: the same morphisms
  bundled into a natural transformation of bifunctors `(K, B) ↦ Rf_! K ⊗ᴸ B` to
  `(K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B)`. This is the version used by Verdier duality.

## Main results

- `ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`: `q_j` is an isomorphism. It is
  the projection map `openImmersionProjectionComparison'` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection`.
- `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_right` and
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_right`:
  `PF^!_{f,K,B}` is natural in `B`.
  Its proof is the naturality of the three constituent maps, assembled for abstract functors:
  `Adjunction.projectionMorphism_natural_right`,
  `Adjunction.inv_projectionComparison_natural_right` and that of
  `leftDerivedUpperStarCompactificationIso`. The bounded constructible version is its image
  under the faithful inclusion, first for an arbitrary compactification
  (`boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_right`).
- `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_left` and
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_left`:
  `PF^!_{f,K,B}` is natural in `K`, in the same way.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`: the derived
  projection formula for `Rf_!` on bounded constructible complexes (Input 2.1 of
  `WeilConjectures/PoincareDuality/Verdier_Poincare_Maps_ProEtale_Condensed_EN.tex`). It is
  deduced from the proper case `g` and from base change; neither is available in derived form.

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
adjunction `Lg^* ⊣ Rg_*`: the mate of `Lg^* (Rg_* A ⊗ᴸ B) ≅ Lg^* Rg_* A ⊗ᴸ Lg^* B ⟶ A ⊗ᴸ Lg^* B`.
It is the derived projection formula for `Rg_*` when it is an isomorphism, which is expected
for `g` proper. -/
noncomputable def properProjectionMorphism
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (R((g)_*⟦Λ⟧)).obj A ⊗ B ⟶ (R((g)_*⟦Λ⟧)).obj (A ⊗ (L((g)^*⟦Λ⟧)).obj B) :=
  (derivedUpperStarLowerStarAdjunction Λ g).projectionMorphism A B

@[reassoc]
lemma properProjectionMorphism_natural_right
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (h : B ⟶ B') :
    (R((g)_*⟦Λ⟧)).obj A ◁ h ≫ properProjectionMorphism Λ g A B' =
      properProjectionMorphism Λ g A B ≫
        (R((g)_*⟦Λ⟧)).map (A ◁ (L((g)^*⟦Λ⟧)).map h) :=
  (derivedUpperStarLowerStarAdjunction Λ g).projectionMorphism_natural_right A h

end Proper

/-! ### The projection comparison of `Dj_! ⊣ Lj^*` -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `Dj_! ⊣ Lj^*` along an open immersion `j`, with the derived pullback
`L((j)^*⟦Λ⟧)` (rather than the levelwise `D((j)^*⟦Λ⟧)`) as right adjoint. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open⟦Λ⟧) ⊣ L((j)^*⟦Λ⟧) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

/-- The projection comparison `q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N` of the adjunction
`Dj_! ⊣ Lj^*` along an open immersion `j`: the adjoint of
`M ⊗ᴸ Lj^* N ⟶ Lj^* Dj_! M ⊗ᴸ Lj^* N ⟶ Lj^* (Dj_! M ⊗ᴸ N)`. -/
noncomputable def openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (D((j)_!open⟦Λ⟧)).obj (M ⊗ (L((j)^*⟦Λ⟧)).obj N) ⟶ (D((j)_!open⟦Λ⟧)).obj M ⊗ N :=
  (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).projectionComparison M N

/-- **The derived projection formula for the extension by zero**: the projection comparison
`q_j` along an open immersion is an isomorphism. See the module docstring. -/
instance isIso_openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (openImmersionProjectionComparison Λ j M N) :=
  inferInstanceAs (IsIso (((openImmersionProjectionComparison' Λ j).app M).app N))

@[reassoc]
lemma openImmersionProjectionComparison_natural_right
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    {N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (h : N ⟶ N') :
    (D((j)_!open⟦Λ⟧)).map (M ◁ (L((j)^*⟦Λ⟧)).map h) ≫
        openImmersionProjectionComparison Λ j M N' =
      openImmersionProjectionComparison Λ j M N ≫ (D((j)_!open⟦Λ⟧)).obj M ◁ h :=
  Adjunction.projectionComparison_natural_right
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j) M h

@[reassoc]
lemma inv_openImmersionProjectionComparison_natural_right
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    {N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (h : N ⟶ N') :
    (D((j)_!open⟦Λ⟧)).obj M ◁ h ≫ inv (openImmersionProjectionComparison Λ j M N') =
      inv (openImmersionProjectionComparison Λ j M N) ≫
        (D((j)_!open⟦Λ⟧)).map (M ◁ (L((j)^*⟦Λ⟧)).map h) := by
  rw [IsIso.eq_inv_comp, ← openImmersionProjectionComparison_natural_right_assoc,
    IsIso.hom_inv_id, Category.comp_id]

end OpenImmersion

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
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the projection morphism `PF^*_g` at `Di_! K`, the inverse of the
projection comparison `q_i`, and the identification `Li^* Lg^* B ≅ Lf^* B`. -/
noncomputable def exceptionalProjectionMorphismOfCompactification
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Rf_!(c)⟦Λ⟧).obj K ⊗ B ⟶ (Rf_!(c)⟦Λ⟧).obj (K ⊗ (L((f)^*⟦Λ⟧)).obj B) :=
  properProjectionMorphism Λ c.g ((D((c.i)_!open⟦Λ⟧)).obj K) B ≫
    (R((c.g)_*⟦Λ⟧)).map
      (inv (openImmersionProjectionComparison Λ c.i K ((L((c.g)^*⟦Λ⟧)).obj B)) ≫
        (D((c.i)_!open⟦Λ⟧)).map
          (K ◁ (leftDerivedUpperStarCompactificationIso Λ c).inv.app B))

/-- The naturality of `exceptionalProjectionMorphismOfCompactification` in its second variable,
for abstract functors: the composite of a projection morphism natural in `B`, an inverse
projection comparison natural in `N` and the identification `Lf^* ≅ Lg^* ⋙ Li^*`. -/
private lemma exceptionalProjectionMorphism_natural_right_aux {𝒰 𝒵 𝒴 : Type*} [Category 𝒰]
    [Category 𝒵] [Category 𝒴] [MonoidalCategory 𝒰] [MonoidalCategory 𝒵] [MonoidalCategory 𝒴]
    (I : 𝒰 ⥤ 𝒵) (G : 𝒵 ⥤ 𝒴) (Fg : 𝒴 ⥤ 𝒵) (Fi : 𝒵 ⥤ 𝒰) (Ff : 𝒴 ⥤ 𝒰) (e : Ff ≅ Fg ⋙ Fi)
    (K : 𝒰) (pm : ∀ (A : 𝒵) (B : 𝒴), G.obj A ⊗ B ⟶ G.obj (A ⊗ Fg.obj B))
    (hpm : ∀ (A : 𝒵) {B B' : 𝒴} (h : B ⟶ B'),
      G.obj A ◁ h ≫ pm A B' = pm A B ≫ G.map (A ◁ Fg.map h))
    (iq : ∀ N : 𝒵, I.obj K ⊗ N ⟶ I.obj (K ⊗ Fi.obj N))
    (hiq : ∀ {N N' : 𝒵} (h : N ⟶ N'), I.obj K ◁ h ≫ iq N' = iq N ≫ I.map (K ◁ Fi.map h))
    {B B' : 𝒴} (h : B ⟶ B') :
    G.obj (I.obj K) ◁ h ≫ pm (I.obj K) B' ≫ G.map (iq (Fg.obj B') ≫ I.map (K ◁ e.inv.app B')) =
      (pm (I.obj K) B ≫ G.map (iq (Fg.obj B) ≫ I.map (K ◁ e.inv.app B))) ≫
        G.map (I.map (K ◁ Ff.map h)) := by
  rw [reassoc_of% hpm, ← G.map_comp, Category.assoc, ← G.map_comp, reassoc_of% hiq,
    ← I.map_comp, ← MonoidalCategory.whiskerLeft_comp, Category.assoc, ← I.map_comp,
    ← MonoidalCategory.whiskerLeft_comp]
  have he := e.inv.naturality h
  dsimp at he
  rw [he]

/-- The exceptional projection morphism is natural in its second variable. -/
@[reassoc]
lemma exceptionalProjectionMorphismOfCompactification_natural_right
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (h : B ⟶ B') :
    (Rf_!(c)⟦Λ⟧).obj K ◁ h ≫ exceptionalProjectionMorphismOfCompactification Λ c K B' =
      exceptionalProjectionMorphismOfCompactification Λ c K B ≫
        (Rf_!(c)⟦Λ⟧).map (K ◁ (L((f)^*⟦Λ⟧)).map h) := by
  exact exceptionalProjectionMorphism_natural_right_aux D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧)
    L((c.g)^*⟦Λ⟧) L((c.i)^*⟦Λ⟧) L((f)^*⟦Λ⟧) (leftDerivedUpperStarCompactificationIso Λ c) K
    (properProjectionMorphism Λ c.g)
    (fun A _ _ h ↦ properProjectionMorphism_natural_right Λ c.g A h)
    (fun N ↦ inv (openImmersionProjectionComparison Λ c.i K N))
    (fun h ↦ inv_openImmersionProjectionComparison_natural_right Λ c.i K h) h


/-- The naturality of `exceptionalProjectionMorphismOfCompactification` in its first variable,
for abstract functors. -/
private lemma exceptionalProjectionMorphism_natural_left_aux {𝒰 𝒵 𝒴 : Type*} [Category 𝒰]
    [Category 𝒵] [Category 𝒴] [MonoidalCategory 𝒰] [MonoidalCategory 𝒵] [MonoidalCategory 𝒴]
    (I : 𝒰 ⥤ 𝒵) (G : 𝒵 ⥤ 𝒴) (Fg : 𝒴 ⥤ 𝒵) (Fi : 𝒵 ⥤ 𝒰) (Ff : 𝒴 ⥤ 𝒰) (e : Ff ≅ Fg ⋙ Fi)
    (pm : ∀ (A : 𝒵) (B : 𝒴), G.obj A ⊗ B ⟶ G.obj (A ⊗ Fg.obj B))
    (hpm : ∀ {A A' : 𝒵} (φ : A ⟶ A') (B : 𝒴),
      G.map φ ▷ B ≫ pm A' B = pm A B ≫ G.map (φ ▷ Fg.obj B))
    (iq : ∀ (K : 𝒰) (N : 𝒵), I.obj K ⊗ N ⟶ I.obj (K ⊗ Fi.obj N))
    (hiq : ∀ {K K' : 𝒰} (φ : K ⟶ K') (N : 𝒵),
      I.map φ ▷ N ≫ iq K' N = iq K N ≫ I.map (φ ▷ Fi.obj N))
    {K K' : 𝒰} (φ : K ⟶ K') (B : 𝒴) :
    G.map (I.map φ) ▷ B ≫ pm (I.obj K') B ≫ G.map (iq K' (Fg.obj B) ≫ I.map (K' ◁ e.inv.app B)) =
      (pm (I.obj K) B ≫ G.map (iq K (Fg.obj B) ≫ I.map (K ◁ e.inv.app B))) ≫
        G.map (I.map (φ ▷ Ff.obj B)) := by
  rw [reassoc_of% hpm, ← G.map_comp, Category.assoc, ← G.map_comp, reassoc_of% hiq,
    ← I.map_comp, Category.assoc, ← I.map_comp, whisker_exchange]

/-- The exceptional projection morphism is natural in its first variable. -/
@[reassoc]
lemma exceptionalProjectionMorphismOfCompactification_natural_left
    {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (φ : K ⟶ K')
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Rf_!(c)⟦Λ⟧).map φ ▷ B ≫ exceptionalProjectionMorphismOfCompactification Λ c K' B =
      exceptionalProjectionMorphismOfCompactification Λ c K B ≫
        (Rf_!(c)⟦Λ⟧).map (φ ▷ (L((f)^*⟦Λ⟧)).obj B) :=
  exceptionalProjectionMorphism_natural_left_aux D((c.i)_!open⟦Λ⟧) R((c.g)_*⟦Λ⟧)
    L((c.g)^*⟦Λ⟧) L((c.i)^*⟦Λ⟧) L((f)^*⟦Λ⟧) (leftDerivedUpperStarCompactificationIso Λ c)
    (properProjectionMorphism Λ c.g)
    (fun φ B ↦ (derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism_natural_left φ B)
    (fun K N ↦ inv (openImmersionProjectionComparison Λ c.i K N))
    (fun {K K'} φ N ↦ by
      exact @CategoryTheory.Adjunction.inv_projectionComparison_natural_left _ _ _ _ _ _ _ _
        (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i) _ _ _ φ N
        (isIso_openImmersionProjectionComparison Λ c.i K N)
        (isIso_openImmersionProjectionComparison Λ c.i K' N)) φ B

end OfCompactification

/-! ### The exceptional projection morphism on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **derived exceptional projection morphism**
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded constructible complexes: the
morphism `exceptionalProjectionMorphismOfCompactification` for the compactification
`compactificationOverField f` defining `boundedConstructibleLowerShriek`, the inclusions
`Dᵇc ⥤ D` being fully faithful and monoidal. -/
noncomputable def boundedConstructibleExceptionalProjectionMorphism (K : Dᵇc(X.left)⟦Λ⟧)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriek Λ ℓ f).obj K ⊗ B ⟶
      (boundedConstructibleLowerShriek Λ ℓ f).obj
        (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification Λ (compactificationOverField f) K.obj B.obj)

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is natural in its second variable. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_right
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Λ⟧) {B B' : Dᵇc(Y.left)⟦Λ⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ◁ h ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ B')
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B'))
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj B'.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj B.obj) ≫
        (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map
          (K ◁ (boundedConstructibleUpperStar Λ ℓ f).map h) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  exact exceptionalProjectionMorphismOfCompactification_natural_right Λ c K.obj h.hom

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
second variable. It is the image of
`exceptionalProjectionMorphismOfCompactification_natural_right` under the faithful inclusion,
proved for an arbitrary compactification and specialised (unfolding the chosen compactification
directly times out). -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_right (K : Dᵇc(X.left)⟦Λ⟧)
    {B B' : Dᵇc(Y.left)⟦Λ⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriek Λ ℓ f).obj K ◁ h ≫
        boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B' =
      boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          (K ◁ (boundedConstructibleUpperStar Λ ℓ f).map h) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_right Λ ℓ f
    (compactificationOverField f) K h

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is natural in its first variable. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_left
    (c : Compactification f.left) {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map φ ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K' ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K' ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification Λ c K'.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj B.obj) ≫
        (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map
          (φ ▷ (boundedConstructibleUpperStar Λ ℓ f).obj B) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  exact exceptionalProjectionMorphismOfCompactification_natural_left Λ c φ.hom B.obj

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
first variable, as `boundedConstructibleExceptionalProjectionMorphism_natural_right`. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_left {K K' : Dᵇc(X.left)⟦Λ⟧}
    (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriek Λ ℓ f).map φ ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K' B =
      boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          (φ ▷ (boundedConstructibleUpperStar Λ ℓ f).obj B) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_left Λ ℓ f
    (compactificationOverField f) φ B

/-- The **derived exceptional projection morphism** on bounded constructible complexes, as a
natural transformation of bifunctors `Dᵇc(X) ⥤ Dᵇc(Y) ⥤ Dᵇc(Y)`
```
(K, B) ↦ Rf_! K ⊗ᴸ B   ⟶   (K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B),
```
with components `boundedConstructibleExceptionalProjectionMorphism`. This is the form in which
`PF^!` enters `CategoryTheory.Verdier`. -/
noncomputable def boundedConstructibleExceptionalProjection :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriek Λ ℓ f) ⟶
      curriedTensorPost (boundedConstructibleLowerShriek Λ ℓ f) ⋙
        (Functor.whiskeringLeft _ _ _).obj (boundedConstructibleUpperStar Λ ℓ f) where
  app K :=
    { app B := boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B
      naturality _ _ h :=
        boundedConstructibleExceptionalProjectionMorphism_natural_right Λ ℓ f K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦
    boundedConstructibleExceptionalProjectionMorphism_natural_left Λ ℓ f φ B

@[simp]
lemma boundedConstructibleExceptionalProjection_app_app (K : Dᵇc(X.left)⟦Λ⟧)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleExceptionalProjection Λ ℓ f).app K).app B =
      boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B :=
  rfl

/-- **The derived projection formula for `Rf_!`**: the exceptional projection morphism
`PF^!_{f,K,B}` is an isomorphism for bounded constructible `K` and `B`. See the module
docstring. -/
instance isIso_boundedConstructibleExceptionalProjectionMorphism (K : Dᵇc(X.left)⟦Λ⟧)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso (boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B) :=
  sorry

instance isIso_boundedConstructibleExceptionalProjection_app_app (K : Dᵇc(X.left)⟦Λ⟧)
    (B : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso (((boundedConstructibleExceptionalProjection Λ ℓ f).app K).app B) :=
  isIso_boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
