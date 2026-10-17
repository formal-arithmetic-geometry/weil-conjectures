/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.IntegralResidueDerivedMonoidal

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
   immersion `i` (`CategoryTheory.Adjunction.projectionComparison`), which is *assumed* to be an
   isomorphism (`ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`): this is the
   derived projection formula for the extension by zero;
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

- `ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_right` and
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_right`:
  `PF^!_{f,K,B}` is natural in `B`.
  Its proof (sorried for now) is the naturality of the three constituent maps:
  `Adjunction.projectionMorphism_natural_right`,
  `Adjunction.inv_projectionComparison_natural_right` and that of
  `leftDerivedUpperStarCompactificationIso`. The bounded constructible version is its image
  under the faithful inclusion, also sorried: the direct proof times out.
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_left`:
  `PF^!_{f,K,B}` is natural in `K` (sorried for now).

## Sorried input

- `ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`: `q_j` is an isomorphism.
  On module objects `j_!` is exact and `j^*` is restriction, so `j_!(M ⊗ j^* N) ≅ j_! M ⊗ N`
  holds already on the underived tensor products (`Adjunction.HasProjectionFormula` for
  `j_! ⊣ j^*`), and both sides preserve K-flat resolutions.
- `ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`: the derived
  projection formula for `Rf_!` on bounded constructible complexes (Input 2.1 of
  `WeilConjectures/PoincareDuality/Verdier_Poincare_Maps_ProEtale_Condensed_EN.tex`). It is
  deduced from the proper case `g` and from base change; neither is available in derived form.

-/

@[expose] public section

-- Do not expand the K-injective internal-Hom construction during elaboration.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived

attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

private lemma projectionMorphism_natural_left_local {F : D ⥤ C} {G : C ⥤ D}
    (adj : F ⊣ G) [F.OplaxMonoidal] {A A' : C} (h : A ⟶ A') (B : D) :
    G.map h ▷ B ≫ adj.projectionMorphism A' B =
      adj.projectionMorphism A B ≫ G.map (h ▷ F.obj B) := by
  rw [projectionMorphism, projectionMorphism, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right]
  congr 1
  rw [← δ_natural_left_assoc]
  simpa only [comp_whiskerRight, Category.assoc, Functor.comp_map, Functor.id_map] using
    congrArg (fun k ↦ δ F (G.obj A) B ≫ k ▷ F.obj B) (adj.counit.naturality h)

private lemma projectionComparison_natural_left_local {P : C ⥤ D} {S : D ⥤ C}
    (adj : P ⊣ S) [S.LaxMonoidal] {M M' : C} (h : M ⟶ M') (N : D) :
    P.map (h ▷ S.obj N) ≫ adj.projectionComparison M' N =
      adj.projectionComparison M N ≫ P.map h ▷ N := by
  rw [projectionComparison, projectionComparison, ← homEquiv_naturality_left_symm,
    ← homEquiv_naturality_right_symm]
  congr 1
  rw [Category.assoc, ← μ_natural_left,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simpa only [Functor.id_map, Functor.comp_map] using
    congrArg (fun k ↦ k ▷ S.obj N ≫ μ S (P.obj M') N) (adj.unit.naturality h)

end CategoryTheory.Adjunction

namespace CategoryTheory

private lemma compose_map_square_local {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A A' B B' E E' : C} {X X' : D}
    (s : X ⟶ X') (p : X ⟶ G.obj A) (p' : X' ⟶ G.obj A')
    (u : A ⟶ A') (q : A ⟶ B) (q' : A' ⟶ B')
    (v : B ⟶ B') (r : B ⟶ E) (r' : B' ⟶ E') (w : E ⟶ E')
    (hp : s ≫ p' = p ≫ G.map u) (hq : u ≫ q' = q ≫ v) (hr : v ≫ r' = r ≫ w) :
    s ≫ (p' ≫ G.map (q' ≫ r')) = (p ≫ G.map (q ≫ r)) ≫ G.map w := by
  rw [← Category.assoc, hp, Category.assoc, ← G.map_comp]
  rw [← Category.assoc u, hq, Category.assoc q, hr]
  simp only [G.map_comp, Category.assoc]

private lemma map_whiskerLeft_square_local {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [MonoidalCategory C] (P : C ⥤ E) {S R : D ⥤ C} (t : S ⟶ R)
    (K : C) {B B' : D} (h : B ⟶ B') :
    P.map (K ◁ S.map h) ≫ P.map (K ◁ t.app B') =
      P.map (K ◁ t.app B) ≫ P.map (K ◁ R.map h) := by
  rw [← P.map_comp, ← P.map_comp, ← whiskerLeft_comp, ← whiskerLeft_comp, t.naturality]

private lemma map_whisker_exchange_local {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] (P : C ⥤ D) {K K' A B : C} (φ : K ⟶ K') (t : A ⟶ B) :
    P.map (φ ▷ A) ≫ P.map (K' ◁ t) = P.map (K ◁ t) ≫ P.map (φ ▷ B) := by
  rw [← P.map_comp, ← P.map_comp, ← whisker_exchange]

private lemma full_whiskerLeft_hom_local {C : Type*} [Category* C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] (K : P.FullSubcategory)
    {B B' : P.FullSubcategory} (h : B ⟶ B') :
    (K ◁ h).hom = K.obj ◁ h.hom := rfl

private lemma full_whiskerRight_hom_local {C : Type*} [Category* C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] {K K' : P.FullSubcategory}
    (φ : K ⟶ K') (B : P.FullSubcategory) :
    (φ ▷ B).hom = φ.hom ▷ B.obj := rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

attribute [local instance 3000] projectionDerivedMonoidal

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

/-- Naturality of the proper projection morphism in its first argument. -/
private lemma properProjectionMorphism_natural_left
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (φ : A ⟶ A')
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (R((g)_*⟦Λ⟧)).map φ ▷ B ≫ properProjectionMorphism Λ g A' B =
      properProjectionMorphism Λ g A B ≫
        (R((g)_*⟦Λ⟧)).map (φ ▷ (L((g)^*⟦Λ⟧)).obj B) :=
  Adjunction.projectionMorphism_natural_left_local
    (derivedUpperStarLowerStarAdjunction Λ g) φ B

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
  sorry

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

/-- Naturality of the open projection comparison in its first argument. -/
@[reassoc]
private lemma openImmersionProjectionComparison_natural_left
    {M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (φ : M ⟶ M')
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (D((j)_!open⟦Λ⟧)).map (φ ▷ (L((j)^*⟦Λ⟧)).obj N) ≫
        openImmersionProjectionComparison Λ j M' N =
      openImmersionProjectionComparison Λ j M N ≫ (D((j)_!open⟦Λ⟧)).map φ ▷ N :=
  Adjunction.projectionComparison_natural_left_local
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j) φ N

/-- Naturality of the inverse open projection comparison in its first argument. -/
private lemma inv_openImmersionProjectionComparison_natural_left
    {M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (φ : M ⟶ M')
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (D((j)_!open⟦Λ⟧)).map φ ▷ N ≫ inv (openImmersionProjectionComparison Λ j M' N) =
      inv (openImmersionProjectionComparison Λ j M N) ≫
        (D((j)_!open⟦Λ⟧)).map (φ ▷ (L((j)^*⟦Λ⟧)).obj N) := by
  rw [IsIso.eq_inv_comp, ← openImmersionProjectionComparison_natural_left_assoc,
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

/-- The exceptional projection morphism is natural in its second variable. -/
@[reassoc]
lemma exceptionalProjectionMorphismOfCompactification_natural_right
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (h : B ⟶ B') :
    (Rf_!(c)⟦Λ⟧).obj K ◁ h ≫ exceptionalProjectionMorphismOfCompactification Λ c K B' =
      exceptionalProjectionMorphismOfCompactification Λ c K B ≫
        (Rf_!(c)⟦Λ⟧).map (K ◁ (L((f)^*⟦Λ⟧)).map h) := by
  dsimp only [exceptionalProjectionMorphismOfCompactification]
  refine CategoryTheory.compose_map_square_local (R((c.g)_*⟦Λ⟧))
    _ _ _ ((D((c.i)_!open⟦Λ⟧)).obj K ◁ (L((c.g)^*⟦Λ⟧)).map h) _ _
    ((D((c.i)_!open⟦Λ⟧)).map
      (K ◁ (L((c.i)^*⟦Λ⟧)).map ((L((c.g)^*⟦Λ⟧)).map h)))
    _ _ _ ?_ ?_ ?_
  · exact properProjectionMorphism_natural_right Λ c.g _ h
  · exact inv_openImmersionProjectionComparison_natural_right Λ c.i K
      ((L((c.g)^*⟦Λ⟧)).map h)
  · exact CategoryTheory.map_whiskerLeft_square_local (D((c.i)_!open⟦Λ⟧))
      (leftDerivedUpperStarCompactificationIso Λ c).inv K h

/-- Naturality of the compactification projection morphism in its first argument. -/
private lemma exceptionalProjectionMorphismOfCompactification_natural_left
    {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (φ : K ⟶ K')
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Rf_!(c)⟦Λ⟧).map φ ▷ B ≫ exceptionalProjectionMorphismOfCompactification Λ c K' B =
      exceptionalProjectionMorphismOfCompactification Λ c K B ≫
        (Rf_!(c)⟦Λ⟧).map (φ ▷ (L((f)^*⟦Λ⟧)).obj B) := by
  dsimp only [exceptionalProjectionMorphismOfCompactification, Functor.comp_map]
  refine CategoryTheory.compose_map_square_local (R((c.g)_*⟦Λ⟧))
    _ _ _ ((D((c.i)_!open⟦Λ⟧)).map φ ▷ (L((c.g)^*⟦Λ⟧)).obj B) _ _
    ((D((c.i)_!open⟦Λ⟧)).map
      (φ ▷ (L((c.i)^*⟦Λ⟧)).obj ((L((c.g)^*⟦Λ⟧)).obj B)))
    _ _ _ ?_ ?_ ?_
  · exact properProjectionMorphism_natural_left Λ c.g _ B
  · exact inv_openImmersionProjectionComparison_natural_left Λ c.i φ
      ((L((c.g)^*⟦Λ⟧)).obj B)
  · exact CategoryTheory.map_whisker_exchange_local (D((c.i)_!open⟦Λ⟧)) φ
      ((leftDerivedUpperStarCompactificationIso Λ c).inv.app B)

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

private lemma projection_lower_obj (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleLowerShriek Λ ℓ f).obj K).obj =
      (Rf_!(compactificationOverField f)⟦Λ⟧).obj K.obj := rfl

private lemma projection_lower_map {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K') :
    ((boundedConstructibleLowerShriek Λ ℓ f).map φ).hom =
      (Rf_!(compactificationOverField f)⟦Λ⟧).map φ.hom := rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
private lemma projection_upper_obj (B : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStar Λ ℓ f).obj B).obj =
      (L((f.left)^*⟦Λ⟧)).obj B.obj := rfl

omit [IsEllAdicFinitenessCoefficient ℓ Λ] in
private lemma projection_upper_map {B B' : Dᵇc(Y.left)⟦Λ⟧} (h : B ⟶ B') :
    ((boundedConstructibleUpperStar Λ ℓ f).map h).hom =
      (L((f.left)^*⟦Λ⟧)).map h.hom := rfl

private lemma projection_hom (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B).hom =
      exceptionalProjectionMorphismOfCompactification Λ (compactificationOverField f)
        K.obj B.obj := by
  simp only [boundedConstructibleExceptionalProjectionMorphism, ObjectProperty.homMk_hom]

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
second variable. It is the image of
`exceptionalProjectionMorphismOfCompactification_natural_right` under the faithful inclusion;
the direct term proof times out on unfolding the restricted functors, so it is `sorry`ed for
now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_right (K : Dᵇc(X.left)⟦Λ⟧)
    {B B' : Dᵇc(Y.left)⟦Λ⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriek Λ ℓ f).obj K ◁ h ≫
        boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B' =
      boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          (K ◁ (boundedConstructibleUpperStar Λ ℓ f).map h) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, projection_hom,
    CategoryTheory.full_whiskerLeft_hom_local, projection_lower_obj,
    projection_lower_map, projection_upper_map]
  exact exceptionalProjectionMorphismOfCompactification_natural_right Λ
    (compactificationOverField f) K.obj h.hom

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
first variable. Like `boundedConstructibleExceptionalProjectionMorphism_natural_right`, it
follows from the naturality of the three constituent maps; it is `sorry`ed for now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_left {K K' : Dᵇc(X.left)⟦Λ⟧}
    (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriek Λ ℓ f).map φ ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K' B =
      boundedConstructibleExceptionalProjectionMorphism Λ ℓ f K B ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          (φ ▷ (boundedConstructibleUpperStar Λ ℓ f).obj B) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, projection_hom,
    CategoryTheory.full_whiskerRight_hom_local, projection_lower_map, projection_upper_obj]
  exact exceptionalProjectionMorphismOfCompactification_natural_left Λ
    (compactificationOverField f) φ.hom B.obj

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
