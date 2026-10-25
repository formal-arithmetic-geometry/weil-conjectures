/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

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
  `boundedConstructibleLowerShriek`. It is stated for each of the `ℓ`-adic coefficient rings
  `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (in the namespaces `ProEtale.CondensedRing`,
  `ProEtale.CondensedRing.ContinuousMapRingObj` and `ProEtale.CondensedRing.PadicIntegersRingObj`),
  as are the declarations below.
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
        (Rf_!(c)⟦Λ⟧).map (K ◁ (L((f)^*⟦Λ⟧)).map h) :=
  sorry

end OfCompactification

/-! ### The exceptional projection morphism on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **derived exceptional projection morphism**
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded constructible complexes
(`ℚ̄_ℓ`-coefficient): the morphism `exceptionalProjectionMorphismOfCompactification` for the
compactification `compactificationOverField f` defining `boundedConstructibleLowerShriek`, the
inclusions `Dᵇc ⥤ D` being fully faithful and monoidal. -/
noncomputable def boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ f).obj K ⊗ B ⟶
      (boundedConstructibleLowerShriek ℓ f).obj
        (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj B) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification (Profinite.padicAlgClRingObj ℓ)
      (compactificationOverField f) K.obj B.obj)

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
second variable (`ℚ̄_ℓ`-coefficient). It is the image of
`exceptionalProjectionMorphismOfCompactification_natural_right` under the faithful inclusion;
the direct term proof times out on unfolding the restricted functors, so it is `sorry`ed for
now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_right
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {B B' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriek ℓ f).obj K ◁ h ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ f K B' =
      boundedConstructibleExceptionalProjectionMorphism ℓ f K B ≫
        (boundedConstructibleLowerShriek ℓ f).map
          (K ◁ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map h) :=
  sorry

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
first variable (`ℚ̄_ℓ`-coefficient). Like
`boundedConstructibleExceptionalProjectionMorphism_natural_right`, it follows from the naturality of
the three constituent maps; it is `sorry`ed for now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_left
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ f).map φ ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ f K' B =
      boundedConstructibleExceptionalProjectionMorphism ℓ f K B ≫
        (boundedConstructibleLowerShriek ℓ f).map
          (φ ▷ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj B) :=
  sorry

/-- The **derived exceptional projection morphism** on bounded constructible complexes, as a
natural transformation of bifunctors `Dᵇc(X) ⥤ Dᵇc(Y) ⥤ Dᵇc(Y)`
```
(K, B) ↦ Rf_! K ⊗ᴸ B   ⟶   (K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B),
```
with components `boundedConstructibleExceptionalProjectionMorphism` (`ℚ̄_ℓ`-coefficient). This is
the form in which `PF^!` enters `CategoryTheory.Verdier`. -/
noncomputable def boundedConstructibleExceptionalProjection :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriek ℓ f) ⟶
      curriedTensorPost (boundedConstructibleLowerShriek ℓ f) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) where
  app K :=
    { app B := boundedConstructibleExceptionalProjectionMorphism ℓ f K B
      naturality _ _ h :=
        boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ f K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦
    boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ f φ B

/-- The components of `boundedConstructibleExceptionalProjection` (`ℚ̄_ℓ`-coefficient). -/
@[simp]
lemma boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleExceptionalProjection ℓ f).app K).app B =
      boundedConstructibleExceptionalProjectionMorphism ℓ f K B :=
  rfl

/-- **The derived projection formula for `Rf_!`** (`ℚ̄_ℓ`-coefficient): the exceptional projection
morphism `PF^!_{f,K,B}` is an isomorphism for bounded constructible `K` and `B`. See the module
docstring. -/
instance isIso_boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (boundedConstructibleExceptionalProjectionMorphism ℓ f K B) :=
  sorry

/-- The components of the exceptional projection are isomorphisms (`ℚ̄_ℓ`-coefficient). -/
instance isIso_boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (((boundedConstructibleExceptionalProjection ℓ f).app K).app B) :=
  isIso_boundedConstructibleExceptionalProjectionMorphism ℓ f K B

end BoundedConstructible

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **derived exceptional projection morphism**
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded constructible complexes
(`E`-coefficient): the morphism `exceptionalProjectionMorphismOfCompactification` for the
compactification `compactificationOverField f` defining `boundedConstructibleLowerShriek`, the
inclusions `Dᵇc ⥤ D` being fully faithful and monoidal. -/
noncomputable def boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleLowerShriek ℓ E f).obj K ⊗ B ⟶
      (boundedConstructibleLowerShriek ℓ E f).obj
        (K ⊗ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).obj B) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification (Profinite.continuousMapRingObj E)
      (compactificationOverField f) K.obj B.obj)

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
second variable (`E`-coefficient). It is the image of
`exceptionalProjectionMorphismOfCompactification_natural_right` under the faithful inclusion;
the direct term proof times out on unfolding the restricted functors, so it is `sorry`ed for
now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_right
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)
    {B B' : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriek ℓ E f).obj K ◁ h ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ E f K B' =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B ≫
        (boundedConstructibleLowerShriek ℓ E f).map
          (K ◁ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).map h) :=
  sorry

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
first variable (`E`-coefficient). Like
`boundedConstructibleExceptionalProjectionMorphism_natural_right`, it follows from the naturality of
the three constituent maps; it is `sorry`ed for now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_left
    {K K' : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧}
    (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleLowerShriek ℓ E f).map φ ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ E f K' B =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B ≫
        (boundedConstructibleLowerShriek ℓ E f).map
          (φ ▷ (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f).obj B) :=
  sorry

/-- The **derived exceptional projection morphism** on bounded constructible complexes, as a
natural transformation of bifunctors `Dᵇc(X) ⥤ Dᵇc(Y) ⥤ Dᵇc(Y)`
```
(K, B) ↦ Rf_! K ⊗ᴸ B   ⟶   (K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B),
```
with components `boundedConstructibleExceptionalProjectionMorphism` (`E`-coefficient). This is the
form in which `PF^!` enters `CategoryTheory.Verdier`. -/
noncomputable def boundedConstructibleExceptionalProjection :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriek ℓ E f) ⟶
      curriedTensorPost (boundedConstructibleLowerShriek ℓ E f) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f) where
  app K :=
    { app B := boundedConstructibleExceptionalProjectionMorphism ℓ E f K B
      naturality _ _ h :=
        boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ E f K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦
    boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ E f φ B

/-- The components of `boundedConstructibleExceptionalProjection` (`E`-coefficient). -/
@[simp]
lemma boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleExceptionalProjection ℓ E f).app K).app B =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B :=
  rfl

/-- **The derived projection formula for `Rf_!`** (`E`-coefficient): the exceptional projection
morphism `PF^!_{f,K,B}` is an isomorphism for bounded constructible `K` and `B`. See the module
docstring. -/
instance isIso_boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    IsIso (boundedConstructibleExceptionalProjectionMorphism ℓ E f K B) :=
  sorry

/-- The components of the exceptional projection are isomorphisms (`E`-coefficient). -/
instance isIso_boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    IsIso (((boundedConstructibleExceptionalProjection ℓ E f).app K).app B) :=
  isIso_boundedConstructibleExceptionalProjectionMorphism ℓ E f K B

end BoundedConstructible

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **derived exceptional projection morphism**
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded constructible complexes
(`𝒪_E`-coefficient): the morphism `exceptionalProjectionMorphismOfCompactification` for the
compactification `compactificationOverField f` defining `boundedConstructibleLowerShriek`, the
inclusions `Dᵇc ⥤ D` being fully faithful and monoidal. -/
noncomputable def boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleLowerShriek ℓ E f).obj K ⊗ B ⟶
      (boundedConstructibleLowerShriek ℓ E f).obj
        (K ⊗ (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj B) :=
  ObjectProperty.homMk
    (exceptionalProjectionMorphismOfCompactification (Profinite.padicIntegersRingObj ℓ E)
      (compactificationOverField f) K.obj B.obj)

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
second variable (`𝒪_E`-coefficient). It is the image of
`exceptionalProjectionMorphismOfCompactification_natural_right` under the faithful inclusion;
the direct term proof times out on unfolding the restricted functors, so it is `sorry`ed for
now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_right
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    {B B' : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧} (h : B ⟶ B') :
    (boundedConstructibleLowerShriek ℓ E f).obj K ◁ h ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ E f K B' =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B ≫
        (boundedConstructibleLowerShriek ℓ E f).map
          (K ◁ (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).map h) :=
  sorry

/-- The exceptional projection morphism on bounded constructible complexes is natural in its
first variable (`𝒪_E`-coefficient). Like
`boundedConstructibleExceptionalProjectionMorphism_natural_right`, it follows from the naturality of
the three constituent maps; it is `sorry`ed for now. -/
@[reassoc]
lemma boundedConstructibleExceptionalProjectionMorphism_natural_left
    {K K' : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    (φ : K ⟶ K') (B : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleLowerShriek ℓ E f).map φ ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ E f K' B =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B ≫
        (boundedConstructibleLowerShriek ℓ E f).map
          (φ ▷ (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj B) :=
  sorry

/-- The **derived exceptional projection morphism** on bounded constructible complexes, as a
natural transformation of bifunctors `Dᵇc(X) ⥤ Dᵇc(Y) ⥤ Dᵇc(Y)`
```
(K, B) ↦ Rf_! K ⊗ᴸ B   ⟶   (K, B) ↦ Rf_! (K ⊗ᴸ Lf^* B),
```
with components `boundedConstructibleExceptionalProjectionMorphism` (`𝒪_E`-coefficient). This is the
form in which `PF^!` enters `CategoryTheory.Verdier`. -/
noncomputable def boundedConstructibleExceptionalProjection :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriek ℓ E f) ⟶
      curriedTensorPost (boundedConstructibleLowerShriek ℓ E f) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f) where
  app K :=
    { app B := boundedConstructibleExceptionalProjectionMorphism ℓ E f K B
      naturality _ _ h :=
        boundedConstructibleExceptionalProjectionMorphism_natural_right ℓ E f K h }
  naturality _ _ φ := NatTrans.ext <| funext fun B ↦
    boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ E f φ B

/-- The components of `boundedConstructibleExceptionalProjection` (`𝒪_E`-coefficient). -/
@[simp]
lemma boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleExceptionalProjection ℓ E f).app K).app B =
      boundedConstructibleExceptionalProjectionMorphism ℓ E f K B :=
  rfl

/-- **The derived projection formula for `Rf_!`** (`𝒪_E`-coefficient): the exceptional projection
morphism `PF^!_{f,K,B}` is an isomorphism for bounded constructible `K` and `B`. See the module
docstring. -/
instance isIso_boundedConstructibleExceptionalProjectionMorphism
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    IsIso (boundedConstructibleExceptionalProjectionMorphism ℓ E f K B) :=
  sorry

/-- The components of the exceptional projection are isomorphisms (`𝒪_E`-coefficient). -/
instance isIso_boundedConstructibleExceptionalProjection_app_app
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    IsIso (((boundedConstructibleExceptionalProjection ℓ E f).app K).app B) :=
  isIso_boundedConstructibleExceptionalProjectionMorphism ℓ E f K B

end BoundedConstructible

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
