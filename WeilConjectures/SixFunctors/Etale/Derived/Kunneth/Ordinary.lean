/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# The Künneth map in ordinary étale cohomology

Let `A` be a monoidal Grothendieck abelian coefficient category. For a commutative square of
schemes

```
  W --q--> Y
  |        |
  p        g
  v        v
  X --f--> S
```

with diagonal `c = p ≫ f = q ≫ g`, the *Künneth map* is the morphism

`κ_{E,K} : Rf_* E ⊗ᴸ Rg_* K ⟶ Rc_* (Lp^* E ⊗ᴸ Lq^* K)`

in `D(S_ét)`, adjoint to `Lc^*(Rf_* E ⊗ᴸ Rg_* K) ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lq^* Lg^* Rg_* K ⟶
Lp^* E ⊗ᴸ Lq^* K`. The variant needed for the proof of the Künneth formula is the
*base change map for a pushforward tensored with a complex*: for a commutative square
`h ≫ f' = e ≫ g` it is the morphism

`A' ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* A' ⊗ᴸ Le^* F)`,

adjoint to `Lh^*(A' ⊗ᴸ Lf'^* Rg_* F) ≅ Lh^* A' ⊗ᴸ Le^* Lg^* Rg_* F ⟶ Lh^* A' ⊗ᴸ Le^* F`.

This file also introduces the constant complex functor `D(Λ) ⥤ D(X_ét, Λ)` and the (torsion
étale) cohomological dimension, and states the inputs of the Künneth formula (Stacks, Section
0F0Y and following).

## Main definitions

- `AlgebraicGeometry.Etale.kunnethMap` (`def-kun-kunneth-map`): the Künneth map.
- `AlgebraicGeometry.Etale.tensorBaseChangeMap`: the map of `lem-kun-0f1j` and `lem-kun-0f1n`.
- `AlgebraicGeometry.Etale.constantFunctor` (`def-kun-constant-sheaf`): `K ↦ K_X`.
- `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`,
  `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism` (`def-kun-cd`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Maps

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {S X Y W : Scheme.{u}}

/-- Blueprint `def-kun-kunneth-map`: the Künneth map.

For a commutative square `p ≫ f = c = q ≫ g` (with `p : W ⟶ X`, `q : W ⟶ Y`, `f : X ⟶ S`,
`g : Y ⟶ S`) and `E ∈ D(X_ét)`, `K ∈ D(Y_ét)`, the Künneth map

`κ_{E,K} : Rf_* E ⊗ᴸ Rg_* K ⟶ Rc_* (Lp^* E ⊗ᴸ Lq^* K)`

is the transpose along `Lc^* ⊣ Rc_*` of the composite

`Lc^*(Rf_* E ⊗ᴸ Rg_* K) ≅ Lp^* Lf^* (Rf_* E ⊗ᴸ Rg_* K) ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lp^* Lf^* Rg_* K
  ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lq^* Lg^* Rg_* K ⟶ Lp^* E ⊗ᴸ Lq^* K`

of the composition isomorphism `Lc^* ≅ Lp^* Lf^*`, the monoidality of `Lf^*` and of `Lp^*`, the
composition isomorphisms `Lp^* Lf^* ≅ Lc^* ≅ Lq^* Lg^*`, and the counits of `Lf^* ⊣ Rf_*` and
`Lg^* ⊣ Rg_*`. The monoidality isomorphism of `Lc^*` of the blueprint is taken here in the form
`Lc^* ≅ Lp^* Lf^*` followed by the monoidality of `Lf^*` and `Lp^*`. -/
noncomputable def kunnethMap (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(S)[A]).obj (R((f)_*[A]).obj E)).obj (R((g)_*[A]).obj K) ⟶
      R((c)_*[A]).obj (((-⊗ᴸ-(W)[A]).obj (L((p)^*[A]).obj E)).obj (L((q)^*[A]).obj K)) :=
  (derivedUpperStarLowerStarAdjunction A c).homEquiv _ _
    ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
      L((p)^*[A]).map (((leftDerivedUpperStarTensorComparison A f).app _).app _) ≫
      ((leftDerivedUpperStarTensorComparison A p).app _).app _ ≫
      ((-⊗ᴸ-(W)[A]).map
        (L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app _ ≫
      ((-⊗ᴸ-(W)[A]).obj _).map ((leftDerivedUpperStarComp A p f c hp.symm).inv.app _ ≫
        (leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)))

variable {X' S' T : Scheme.{u}}

/-- The base change map for a pushforward tensored with a complex (`lem-kun-0f1j`,
`lem-kun-0f1n`): for a commutative square `h ≫ f' = e ≫ g` (with `h : Y ⟶ X'`, `e : Y ⟶ T`,
`f' : X' ⟶ S'`, `g : T ⟶ S'`) and `M ∈ D(X'_ét)`, `F ∈ D(T_ét)`, the morphism

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

is the transpose along `Lh^* ⊣ Rh_*` of the composite

`Lh^*(M ⊗ᴸ Lf'^* Rg_* F) ≅ Lh^* M ⊗ᴸ Lh^* Lf'^* Rg_* F ≅ Lh^* M ⊗ᴸ Le^* Lg^* Rg_* F
  ⟶ Lh^* M ⊗ᴸ Le^* F`

of the monoidality of `Lh^*`, the composition isomorphisms through `L(h ≫ f')^*` and the counit
of `Lg^* ⊣ Rg_*`. -/
noncomputable def tensorBaseChangeMap (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (w : h ≫ f' = e ≫ g) (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X')[A]).obj M).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      R((h)_*[A]).obj (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).obj (L((e)^*[A]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A h).app _).app _ ≫
      ((-⊗ᴸ-(Y)[A]).obj _).map ((leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)))

/-- The base change map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` is natural in `M` and
`F`. -/
@[reassoc]
lemma tensorBaseChangeMap_naturality (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (w : h ≫ f' = e ≫ g) {M M' : DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology A)} (φ : M ⟶ M') (ψ : F ⟶ F') :
    ((-⊗ᴸ-(X')[A]).map φ).app _ ≫
        ((-⊗ᴸ-(X')[A]).obj M').map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
          tensorBaseChangeMap A h e f' g w M' F' =
      tensorBaseChangeMap A h e f' g w M F ≫ R((h)_*[A]).map
        (((-⊗ᴸ-(Y)[A]).map (L((h)^*[A]).map φ)).app _ ≫
          ((-⊗ᴸ-(Y)[A]).obj _).map (L((e)^*[A]).map ψ)) := by
  rw [tensorBaseChangeMap, tensorBaseChangeMap, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A h).naturality φ)
    (L((f')^*[A]).obj (R((g)_*[A]).obj F))
  have h₂ := ((leftDerivedUpperStarTensorComparison A h).app M').naturality
    (L((f')^*[A]).map (R((g)_*[A]).map ψ))
  have hv : L((h)^*[A]).map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
      (leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F') =
      ((leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)) ≫
        L((e)^*[A]).map ψ := by
    have n₁ := (leftDerivedUpperStarComp A h f').inv.naturality (R((g)_*[A]).map ψ)
    have n₂ := (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.naturality (R((g)_*[A]).map ψ)
    simp only [Functor.comp_map] at n₁ n₂
    rw [reassoc_of% n₁, reassoc_of% n₂]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 3
    exact (derivedUpperStarLowerStarAdjunction A _).counit.naturality _
  simp only [derivedTensor, curriedTensor_obj_map, curriedTensor_map_app,
    Category.assoc, leftDerivedUpperStarDerivedTensor,
    derivedTensorLeftDerivedUpperStar] at h₁ h₂ hv ⊢
  have h₁' : L((h)^*[A]).map (φ ▷ L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
      ((leftDerivedUpperStarTensorComparison A h).app M').app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F)) =
      ((leftDerivedUpperStarTensorComparison A h).app M).app
          (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
        L((h)^*[A]).map φ ▷ L((h)^*[A]).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) := h₁
  have h₂' : L((h)^*[A]).map (M' ◁ L((f')^*[A]).map (R((g)_*[A]).map ψ)) ≫
      ((leftDerivedUpperStarTensorComparison A h).app M').app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F')) =
      ((leftDerivedUpperStarTensorComparison A h).app M').app
          (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
        L((h)^*[A]).obj M' ◁ L((h)^*[A]).map (L((f')^*[A]).map (R((g)_*[A]).map ψ)) := h₂
  rw [reassoc_of% h₂', reassoc_of% h₁']
  congr 1
  rw [← whiskerLeft_comp, hv, whiskerLeft_comp, whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The composition isomorphism `Rp_* ⋙ Rf_* ≅ Rc_*` for `p ≫ f = c`: the conjugate of the
composition isomorphism `Lc^* ≅ Lf^* ⋙ Lp^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`)
under the derived adjunctions `Lc^* ⊣ Rc_*` and `Lf^* ⋙ Lp^* ⊣ Rp_* ⋙ Rf_*`. -/
noncomputable def rightDerivedLowerStarCompIsoOfComp (p : W ⟶ X) (f : X ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) : R((p)_*[A]) ⋙ R((f)_*[A]) ≅ R((c)_*[A]) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction A f).comp
      (derivedUpperStarLowerStarAdjunction A p)) (derivedUpperStarLowerStarAdjunction A c)
    (leftDerivedUpperStarComp A p f c hp.symm)

omit [Etale.UpperStarPreservesFlat A] in
/-- The counit of `Lc^* ⊣ Rc_*` composed with `Lc^*` of the composition isomorphism
`Rf_* Rp_* ≅ Rc_*` is the counit of the composite adjunction `Lf^* ⋙ Lp^* ⊣ Rp_* ⋙ Rf_*`. -/
@[reassoc]
lemma map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit (p : W ⟶ X) (f : X ⟶ S)
    (c : W ⟶ S) (hp : p ≫ f = c) (M : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    L((c)^*[A]).map ((rightDerivedLowerStarCompIsoOfComp A p f c hp).hom.app M) ≫
        (derivedUpperStarLowerStarAdjunction A c).counit.app M =
      (leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
        L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app _) ≫
          (derivedUpperStarLowerStarAdjunction A p).counit.app M := by
  rw [rightDerivedLowerStarCompIsoOfComp, conjugateIsoEquiv_apply_hom, conjugateEquiv_counit,
    Adjunction.comp_counit_app]
  rfl

/-- Blueprint `lem-kun-kunneth-via-0f1n`: the Künneth map `Rf_* E ⊗ᴸ Rg_* K ⟶ Rc_* (Lp^* E ⊗ᴸ
Lq^* K)` is the composite of the projection map `Rf_* E ⊗ᴸ Rg_* K ⟶ Rf_*(E ⊗ᴸ Lf^* Rg_* K)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`), of `Rf_*` applied to the base
change map `E ⊗ᴸ Lf^* Rg_* K ⟶ Rp_*(Lp^* E ⊗ᴸ Lq^* K)` of
`AlgebraicGeometry.Etale.tensorBaseChangeMap`, and of the composition isomorphism
`Rf_* Rp_* ≅ Rc_*`. -/
lemma kunnethMap_eq (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    kunnethMap A p q f g c hp hq E K =
      ((rightDerivedLowerStarProjectionMap A f).app E).app (R((g)_*[A]).obj K) ≫
        R((f)_*[A]).map (tensorBaseChangeMap A p q f g (hp.trans hq.symm) E K) ≫
          (rightDerivedLowerStarCompIsoOfComp A p f c hp).hom.app _ := by
  subst hp
  apply ((derivedUpperStarLowerStarAdjunction A (p ≫ f)).homEquiv _ _).symm.injective
  rw [kunnethMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc,
    map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit]
  simp only [NatTrans.naturality_assoc, Functor.comp_map]
  congr 1
  have hε := (derivedUpperStarLowerStarAdjunction A f).counit.naturality
    (tensorBaseChangeMap A p q f g (rfl.trans hq.symm) E K)
  simp only [Functor.comp_map, Functor.id_map] at hε
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc]
  erw [hε]
  have hpc : L((f)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app E).app
        (R((g)_*[A]).obj K)) ≫ (derivedUpperStarLowerStarAdjunction A f).counit.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj (R((g)_*[A]).obj K))) =
      ((leftDerivedUpperStarTensorComparison A f).app (R((f)_*[A]).obj E)).app
          (R((g)_*[A]).obj K) ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E)).app
          (L((f)^*[A]).obj (R((g)_*[A]).obj K)) :=
    map_rightDerivedLowerStarProjectionMap_comp_counit A f E _
  rw [reassoc_of% hpc]
  have hT : L((p)^*[A]).map (tensorBaseChangeMap A p q f g (rfl.trans hq.symm) E K) ≫
      (derivedUpperStarLowerStarAdjunction A p).counit.app _ =
      ((derivedUpperStarLowerStarAdjunction A p).homEquiv _ _).symm
        (tensorBaseChangeMap A p q f g (rfl.trans hq.symm) E K) := by
    rw [Adjunction.homEquiv_counit]
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc, Functor.map_comp_assoc, hT,
    tensorBaseChangeMap,
    Equiv.symm_apply_apply]
  congr 1
  have hn : L((p)^*[A]).map (((-⊗ᴸ-(X)[A]).map
        ((derivedUpperStarLowerStarAdjunction A f).counit.app E)).app
          (L((f)^*[A]).obj (R((g)_*[A]).obj K))) ≫
      ((leftDerivedUpperStarTensorComparison A p).app E).app
        (L((f)^*[A]).obj (R((g)_*[A]).obj K)) =
      ((leftDerivedUpperStarTensorComparison A p).app
          (L((f)^*[A]).obj (R((f)_*[A]).obj E))).app (L((f)^*[A]).obj (R((g)_*[A]).obj K)) ≫
        ((-⊗ᴸ-(W)[A]).map
          (L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app
            (L((p)^*[A]).obj (L((f)^*[A]).obj (R((g)_*[A]).obj K))) :=
    NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A p).naturality
      ((derivedUpperStarLowerStarAdjunction A f).counit.app E))
      (L((f)^*[A]).obj (R((g)_*[A]).obj K))
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, Functor.id_obj]

/-- Blueprint `lem-kun-kunneth-map-natural`: the Künneth map is natural in both variables. -/
@[reassoc]
lemma kunnethMap_naturality (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    {E E' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (φ : E ⟶ E') (ψ : K ⟶ K') :
    ((-⊗ᴸ-(S)[A]).map (R((f)_*[A]).map φ)).app _ ≫
        ((-⊗ᴸ-(S)[A]).obj _).map (R((g)_*[A]).map ψ) ≫ kunnethMap A p q f g c hp hq E' K' =
      kunnethMap A p q f g c hp hq E K ≫ R((c)_*[A]).map
        (((-⊗ᴸ-(W)[A]).map (L((p)^*[A]).map φ)).app _ ≫
          ((-⊗ᴸ-(W)[A]).obj _).map (L((q)^*[A]).map ψ)) := by
  have h₁ : ((-⊗ᴸ-(S)[A]).map (R((f)_*[A]).map φ)).app (R((g)_*[A]).obj K) ≫
      ((rightDerivedLowerStarProjectionMap A f).app E').app (R((g)_*[A]).obj K) =
      ((rightDerivedLowerStarProjectionMap A f).app E).app (R((g)_*[A]).obj K) ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map φ).app (L((f)^*[A]).obj (R((g)_*[A]).obj K))) :=
    NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A f).naturality φ) _
  have h₂ : ((-⊗ᴸ-(S)[A]).obj (R((f)_*[A]).obj E')).map (R((g)_*[A]).map ψ) ≫
      ((rightDerivedLowerStarProjectionMap A f).app E').app (R((g)_*[A]).obj K') =
      ((rightDerivedLowerStarProjectionMap A f).app E').app (R((g)_*[A]).obj K) ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).obj E').map (L((f)^*[A]).map (R((g)_*[A]).map ψ))) :=
    ((rightDerivedLowerStarProjectionMap A f).app E').naturality _
  have h₃ := (rightDerivedLowerStarCompIsoOfComp A p f c hp).hom.naturality
    (((-⊗ᴸ-(W)[A]).map (L((p)^*[A]).map φ)).app _ ≫
      ((-⊗ᴸ-(W)[A]).obj _).map (L((q)^*[A]).map ψ))
  simp only [Functor.comp_map] at h₃
  rw [kunnethMap_eq, kunnethMap_eq, reassoc_of% h₂, reassoc_of% h₁]
  simp only [Category.assoc]
  rw [← h₃,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, tensorBaseChangeMap_naturality, Functor.map_comp_assoc]

end Maps

section MonoidalEquivalence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
  {B : Type u'} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [HasDerivedCategory.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B]
  [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]

/-- A monoidal additive equivalence `F : B ⥤ X_ét` onto the category of `A`-valued étale sheaves
on `X` commutes with the derived tensor products:
`D(F)(N ⊗ᴸ M) ≅ D(F) N ⊗ᴸ D(F) M`. -/
noncomputable def mapDerivedCategoryObjTensorIsoDerivedTensor
    (F : B ⥤ Sheaf X.smallEtaleTopology A) [F.Monoidal] [F.IsEquivalence] [F.Additive]
    (N M : DerivedCategory B) :
    F.mapDerivedCategory.obj (N ⊗ M) ≅
      ((derivedTensor A X).obj (F.mapDerivedCategory.obj N)).obj (F.mapDerivedCategory.obj M) :=
  (DerivedCategory.tensorLeftCompMapDerivedCategoryIso F N).app M

end MonoidalEquivalence

section DirectSums

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- Blueprint `lem-kun-derived-tensor-direct-sums`: the derived tensor product `K ⊗ᴸ -` with a
fixed complex commutes with direct sums, being left adjoint to `RHom(K, -)`
(`AlgebraicGeometry.Etale.derivedTensorHomAdjunction`). -/
instance preservesColimitsOfShape_derivedTensor_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (J : Type*) :
    PreservesColimitsOfShape (Discrete J) ((-⊗ᴸ-(X)[A]).obj K) :=
  (derivedTensorHomAdjunction A K).leftAdjoint_preservesColimits.preservesColimitsOfShape

end DirectSums

section Constant

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- Blueprint `def-kun-constant-sheaf`: constant sheaves and constant complexes.

The constant complex functor `D(Λ) ⥤ D(X_ét, Λ)`, `K ↦ K_X`: the functor induced on derived
categories by the exact constant sheaf functor `M ↦ M_X`. -/
noncomputable def constantFunctor :
    DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory

/-- The constant complex functor commutes with the shifts. -/
noncomputable instance : (constantFunctor Λ X).CommShift ℤ :=
  inferInstanceAs
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory.CommShift ℤ)

/-- The constant complex functor is a triangulated functor. -/
instance : (constantFunctor Λ X).IsTriangulated :=
  inferInstanceAs
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory.IsTriangulated)

end Constant

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Inputs

/-- Blueprint `lem-kun-0f1j`: base change for a pushforward tensored with a bounded below complex
of finite Tor amplitude.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

with both squares cartesian and `g` quasi-compact and quasi-separated, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for every bounded below `E ∈ D(X_ét, Λ)` of Tor amplitude in `[n, ∞)` and every
bounded below `F ∈ D(T_ét, Λ)`. -/
theorem isIso_tensorBaseChangeMap_of_isGE [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m n : ℤ)
    (_hE : DerivedCategory.TStructure.t.IsGE E m)
    (_hEt : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < n →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        X).obj E).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (_hF : DerivedCategory.TStructure.t.IsGE F m) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  sorry

/-- Blueprint `lem-kun-0f1n`: base change for a pushforward tensored with an arbitrary complex.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

of `K`-schemes of finite type with both squares cartesian, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `F ∈ D(T_ét, Λ)`, unbounded. -/
theorem isIso_tensorBaseChangeMap [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType t] [QuasiCompact t]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') (_hg : g ≫ b = t)
    (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  sorry

/-- The terminal object `𝟙 X` of the small étale site of `X`. -/
noncomputable def etaleTerminal (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem @AlgebraicGeometry.Etale X)

/-- `𝟙 X` is terminal in the small étale site of `X`. -/
noncomputable def isTerminalEtaleTerminal (X : Scheme.{u}) : IsTerminal (etaleTerminal X) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X

/-- The evaluation morphism `⊕_{s ∈ Γ(X, F)} Λ_X ⟶ F`, `1_s ↦ s`, of an étale sheaf of
`Λ`-modules. -/
noncomputable def globalSectionsEvaluation (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∐ (fun _ : F.obj.obj (op (etaleTerminal X)) ↦
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶ F :=
  Sigma.desc fun s ↦ ((constantSheafAdj _ _ (isTerminalEtaleTerminal X)).homEquiv _ _).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s))

/-- Blueprint `def-kun-global-generated` (for sheaves of `Λ`-modules): `F` is *globally
generated* if its evaluation morphism `⊕_{s ∈ Γ(X, F)} Λ_X ⟶ F` is an epimorphism. -/
def IsGloballyGenerated (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Prop :=
  Epi (globalSectionsEvaluation Λ X F)

/-- Blueprint `lem-kun-pullback-constant`: the inverse image of a constant complex is the
constant complex, `Lf^*(C_Y) ≅ C_X`. -/
noncomputable def constantFunctorCompLeftDerivedUpperStarIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantFunctor Λ Y ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅ constantFunctor Λ X :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (constantSheafCompUpperStarIso Λ f)

section Point

variable {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, the sheafification map of a presheaf of `Λ`-modules on
the small étale site of `Spec k` is bijective on global sections: every covering sieve of the
terminal object contains the identity. -/
lemma bijective_toSheafify_app_etalePoint
    (P : (Spec (.of k)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    Function.Bijective
      ((toSheafify (Spec (.of k)).smallEtaleTopology P).app (op (etalePoint k))) := by
  constructor
  · intro x y h
    have := id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
      (Presheaf.equalizerSieve_mem (Spec (.of k)).smallEtaleTopology
        (toSheafify (Spec (.of k)).smallEtaleTopology P) x y h)
    simpa using this
  · intro s
    obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
      (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology
        (toSheafify (Spec (.of k)).smallEtaleTopology P) (U := op (etalePoint k)) s)
    exact ⟨t, ht.trans (by simp)⟩

instance additive_sheafSections_obj (U : (Spec (.of k)).Etaleᵒᵖ) :
    ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj U).Additive where
  map_add := rfl

instance additive_constantSheaf (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Additive :=
  inferInstanceAs (Functor.const _ ⋙ presheafToSheaf _ _).Additive

instance isIso_unit_constantSheafAdj_etalePoint :
    IsIso (constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      isTerminalEtalePoint).unit := by
  have (M : ModuleCat.{u + 1} Λ) : IsIso ((constantSheafAdj (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).unit.app M) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app, sheafificationAdjunction_unit_app]
    have : IsIso ((constantPresheafAdj (ModuleCat.{u + 1} Λ)
        (isTerminalEtalePoint (k := k))).unit.app M) := by
      rw [constantPresheafAdj_unit_app]; infer_instance
    have : IsIso ((toSheafify (Spec (.of k)).smallEtaleTopology
        ((Functor.const _).obj M)).app (op (etalePoint k))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toSheafify_app_etalePoint Λ _)
    dsimp
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Over a separably closed field `k`, a morphism of étale sheaves of `Λ`-modules on `Spec k`
which is bijective on global sections is an isomorphism. -/
lemma isIso_of_isIso_app_etalePoint
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [hφ : IsIso (φ.hom.app (op (etalePoint k)))] : IsIso φ := by
  let Γ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etalePoint k))
  have hinj := (ConcreteCategory.isIso_iff_bijective _).1 hφ
  have : Γ.IsRightAdjoint := (constantSheafAdj _ _ isTerminalEtalePoint).isRightAdjoint
  have : Mono φ := by
    refine Preadditive.mono_of_kernel_zero ?_
    have hK : IsZero (kernel φ) := isZero_of_subsingleton_sections_of_isSepClosed _ ⟨fun x y ↦ by
      have hι : Mono (Γ.map (kernel.ι φ)) := Γ.map_mono _
      rw [ModuleCat.mono_iff_injective] at hι
      apply hι
      apply hinj.1
      change ((kernel.ι φ ≫ φ).hom.app _) x = ((kernel.ι φ ≫ φ).hom.app _) y
      simp⟩
    exact hK.eq_of_src _ _
  have : Epi φ := by
    refine Preadditive.epi_of_cokernel_zero ?_
    have hQ : IsZero (cokernel φ) := isZero_of_subsingleton_sections_of_isSepClosed _ ⟨fun x y ↦ by
      have h0 : ∀ z, (cokernel.π φ).hom.app (op (etalePoint k)) z = 0 := fun z ↦ by
        obtain ⟨w, rfl⟩ := hinj.2 z
        change ((φ ≫ cokernel.π φ).hom.app _) w = 0
        simp
      obtain ⟨x', rfl⟩ := surjective_app_of_epi_of_isSepClosed k (cokernel.π φ) x
      obtain ⟨y', rfl⟩ := surjective_app_of_epi_of_isSepClosed k (cokernel.π φ) y
      rw [h0, h0]⟩
    exact hQ.eq_of_tgt _ _
  exact isIso_of_mono_of_epi φ

instance isIso_counit_constantSheafAdj_etalePoint :
    IsIso (constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      isTerminalEtalePoint).counit := by
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtalePoint (k := k))
  have (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso (adj.counit.app F) := by
    have : IsIso ((adj.counit.app F).hom.app (op (etalePoint k))) := by
      have h := adj.right_triangle_components F
      have : IsIso (adj.unit.app (((sheafSections _ _).obj (op (etalePoint k))).obj F)) :=
        inferInstance
      have : IsIso (adj.unit.app (((sheafSections _ _).obj (op (etalePoint k))).obj F) ≫
          ((sheafSections _ _).obj (op (etalePoint k))).map (adj.counit.app F)) := by
        rw [h]; infer_instance
      exact IsIso.of_isIso_comp_left (adj.unit.app _)
        (((sheafSections _ _).obj (op (etalePoint k))).map (adj.counit.app F))
    exact isIso_of_isIso_app_etalePoint Λ _
  exact NatIso.isIso_of_isIso_app _

/-- Over a separably closed field `k`, étale sheaves of `Λ`-modules on `Spec k` are
`Λ`-modules: the constant sheaf functor is an equivalence, with inverse the global sections. -/
noncomputable def constantSheafEquivalenceOfIsSepClosed :
    ModuleCat.{u + 1} Λ ≌ Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    isTerminalEtalePoint).toEquivalence

instance isEquivalence_sheafSections_etalePoint :
    ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (etalePoint k))).IsEquivalence :=
  (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).isEquivalence_inverse

/-- Over a separably closed field `k`, the derived global sections on `Spec k` are induced by the
exact global sections functor: `RΓ(Spec k, -) ≅ D(Γ(Spec k, -))`. -/
noncomputable def rightDerivedGlobalSectionsIsoOfIsSepClosed :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) ≅
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).mapDerivedCategory :=
  Functor.rightDerivedFunctorNatIso (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _

/-- Blueprint `lem-kun-0ezp` (cohomology of a separably closed point, for sheaves of
`Λ`-modules): over a separably closed field `k`, `H^q(Spec k, F) = 0` for every étale sheaf `F`
of `Λ`-modules on `Spec k` and every `q ≠ 0`. -/
theorem isZero_cohomology_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) (Spec (.of k)) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let Γ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etalePoint k))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
    ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app _ ≪≫
      (Γ.mapDerivedCategorySingleFunctor 0).app F ≪≫
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u + 1} Λ) 0).app (Γ.obj F)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _)
  exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hq

/-- Over a separably closed field `k`, every object `C` of `D((Spec k)_ét, Λ)` is the constant
complex on its derived global sections: `C ≅ RΓ(Spec k, C)_{Spec k}`. -/
theorem nonempty_iso_constantFunctor_rightDerivedGlobalSections_of_isSepClosed
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (C ≅ (constantFunctor Λ (Spec (.of k))).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)) :=
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).functor.Additive :=
    additive_constantSheaf Λ _
  letI : (constantSheafEquivalenceOfIsSepClosed Λ (k := k)).inverse.Additive :=
    additive_sheafSections_obj Λ _
  ⟨((constantSheafEquivalenceOfIsSepClosed Λ).mapDerivedCategory.counitIso.app C).symm ≪≫
    (constantFunctor Λ _).mapIso ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app C).symm⟩

/-- Blueprint `lem-kun-03qu-global-generation` (for sheaves of `Λ`-modules): over a separably
closed field `k`, every étale sheaf of `Λ`-modules on `Spec k` is globally generated. -/
theorem isGloballyGenerated_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsGloballyGenerated Λ (Spec (.of k)) F := by
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleTerminal (Spec (.of k)))
  let Γ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etaleTerminal (Spec (.of k))))
  have : Γ.IsEquivalence := isEquivalence_sheafSections_etalePoint Λ
  refine Γ.epi_of_epi_map ?_
  rw [ModuleCat.epi_iff_surjective]
  intro s
  refine ⟨(adj.unit.app (ModuleCat.of Λ Λ) ≫ Γ.map (Sigma.ι
    (fun _ : F.obj.obj (op (etaleTerminal (Spec (.of k)))) ↦ (constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) s))
      (1 : Λ), ?_⟩
  have h := adj.homEquiv_unit (ModuleCat.of Λ Λ) F
    ((adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s)))
  rw [Equiv.apply_symm_apply] at h
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Γ.map_comp,
    globalSectionsEvaluation, Sigma.ι_desc, ← h]
  simp only [ModuleCat.hom_ofHom]
  exact one_smul Λ s
/-- Over a separably closed field `k`, the derived global sections
`RΓ(Spec k, -) : D((Spec k)_ét, Λ) ⥤ D(Λ)` are compatible with the derived tensor products:
`RΓ(Spec k, C ⊗ᴸ C') ≅ RΓ(Spec k, C) ⊗ᴸ RΓ(Spec k, C')`. -/
theorem nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed
    (C C' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj C') ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C') := by
  let E := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  let _ : E.functor.Additive := additive_constantSheaf Λ _
  let _ : E.inverse.Additive := additive_sheafSections_obj Λ _
  let F := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : F.IsEquivalence := E.isEquivalence_functor
  let R := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let T := derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let e (X) : F.mapDerivedCategory.obj (R.obj X) ≅ X :=
    F.mapDerivedCategory.mapIso ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app X) ≪≫
      E.mapDerivedCategory.counitIso.app X
  let e' (N) : R.obj (F.mapDerivedCategory.obj N) ≅ N :=
    (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app _ ≪≫
      (E.mapDerivedCategory.unitIso.app N).symm
  let i : (T.obj C).obj C' ≅ F.mapDerivedCategory.obj (R.obj C ⊗ R.obj C') :=
    (T.mapIso (e C).symm).app C' ≪≫ (T.obj _).mapIso (e C').symm ≪≫
      (mapDerivedCategoryObjTensorIsoDerivedTensor _ _ F (R.obj C) (R.obj C')).symm
  exact ⟨R.mapIso i ≪≫ e' (R.obj C ⊗ R.obj C')⟩

/-- Over a separably closed field `k`, a morphism `a : X ⟶ Spec k` has finite cohomological
dimension as soon as `X` has: by the Leray isomorphism, the global sections of the sheaf
`R^q a_* F` on `Spec k`, which determine it, are `H^q(X, F)`. -/
theorem hasFiniteCohomologicalDimensionMorphism_of_isSepClosed {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (hX : HasFiniteCohomologicalDimension Λ X) :
    HasFiniteCohomologicalDimensionMorphism Λ a := by
  obtain ⟨d, hd⟩ := hX
  refine ⟨d, fun F q hq ↦ ?_⟩
  let Γ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etalePoint k))
  have : Γ.IsEquivalence := isEquivalence_sheafSections_etalePoint Λ
  let K := (R((a)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hz : IsZero (Γ.obj ((DerivedCategory.homologyFunctor _ q).obj K)) :=
    (hd F q hq).of_iso ((Γ.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _))
  exact (IsZero.iff_id_eq_zero _).2 (Γ.map_injective (by
    rw [Γ.map_id, Γ.map_zero]
    exact hz.eq_of_src _ _))

/-- Blueprint `lem-kun-0f12`: tensor product with a constant complex.

Let `k` be a separably closed field, `Λ` a torsion ring, and `a : X ⟶ Spec k` a morphism from a
quasi-compact quasi-separated scheme `X` of finite cohomological dimension. For
`E ∈ D(X_ét, Λ)` and `C ∈ D((Spec k)_ét, Λ)` the projection map
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)

`Ra_* E ⊗ᴸ C ⟶ Ra_*(E ⊗ᴸ La^* C)`

is an isomorphism. Under the equivalence of étale sheaves on `Spec k` with `Λ`-modules
(`AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed`), `Ra_*` is `RΓ(X, -)` and
`La^*` is the constant complex functor `C ↦ C_X`
(`AlgebraicGeometry.Etale.constantFunctorCompLeftDerivedUpperStarIso`), and the projection map
is the canonical map `RΓ(X, E) ⊗ᴸ C ⟶ RΓ(X, E ⊗ᴸ C_X)` of the blueprint: it is adjoint to
`La^*(Ra_* E ⊗ᴸ C) ≅ La^* Ra_* E ⊗ᴸ La^* C ⟶ E ⊗ᴸ La^* C`, as in the proof of
`lem-kun-kunneth-via-0f1n`. -/
theorem isIso_rightDerivedLowerStarProjectionMap_of_isSepClosed {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : HasFiniteCohomologicalDimension Λ X)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) a).app E).app C) := by
  have : QuasiCompact a := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 ‹_›
  have : QuasiSeparated a := (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).2 ‹_›
  have (J : Type (u + 1)) := preservesCoproducts_rightDerivedLowerStar Λ a
    (hasFiniteCohomologicalDimensionMorphism_of_isSepClosed Λ a hX) J
  let e := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  letI : e.functor.Additive := additive_constantSheaf Λ _
  letI : e.inverse.Additive := additive_sheafSections_obj Λ _
  -- the constant complex functor `D(Λ) ⥤ D((Spec k)_ét, Λ)`, an equivalence
  have : (constantFunctor Λ (Spec (.of k))).IsEquivalence :=
    e.mapDerivedCategory.isEquivalence_functor
  let τ : (-⊗ᴸ-(Spec (.of k))[ModuleCat.{u + 1} Λ]).obj ((R((a)_*[ModuleCat.{u + 1} Λ])).obj E) ⟶
      (L((a)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj E) ⋙
        R((a)_*[ModuleCat.{u + 1} Λ]) :=
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) a).app E
  have h₂ (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J)
      ((L((a)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj E) ⋙
        R((a)_*[ModuleCat.{u + 1} Λ])) :=
    have : PreservesColimitsOfShape (Discrete J) (L((a)^*[ModuleCat.{u + 1} Λ])) :=
      (derivedUpperStarLowerStarAdjunction _ a).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    inferInstance
  have hτ : IsIso (Functor.whiskerLeft (constantFunctor Λ (Spec (.of k))) τ) := by
    refine DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self (T := DerivedCategory _)
      (Functor.whiskerLeft (constantFunctor Λ (Spec (.of k))) τ) ?_
    dsimp only [Functor.whiskerLeft_app]
    have hunit : IsIso (τ.app (𝟙_ _)) :=
      isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit _ a E
    refine (NatTrans.isIso_app_iff_of_iso τ ?_).2 hunit
    exact (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso
        (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm ≪≫
      singleFunctorObjUnitIso _ _
  have := (NatTrans.isIso_iff_isIso_app _).1 hτ
    ((constantFunctor Λ (Spec (.of k))).objPreimage C)
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((constantFunctor Λ (Spec (.of k))).objObjPreimageIso C)).1 this

end Point

end Inputs

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- The projection map `Ra_{X*} E ⊗ᴸ C ⟶ Ra_{X*}(E ⊗ᴸ La_X^* C)` is an isomorphism for a
finite-type scheme `X` over a separably closed field `k` (`lem-kun-0f12`, with `lem-kun-0f10`). -/
instance isIso_rightDerivedLowerStarProjectionMap_app_app
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) aX).app E).app C) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  isIso_rightDerivedLowerStarProjectionMap_of_isSepClosed Λ aX
    (hasFiniteCohomologicalDimension_of_isSepClosed Λ aX) E C

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- `RΓ(X, E) ⊗ᴸ RΓ(Spec k, C) ≅ RΓ(X, E ⊗ᴸ La_X^* C)` for a finite-type scheme `X` over a
separably closed field `k`: the tensor product with a constant complex (`lem-kun-0f12`), read
in `D(Λ)` through `RΓ(Spec k, -)`. -/
theorem nonempty_iso_rightDerivedGlobalSections_derivedTensor_leftDerivedUpperStar
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
          ((L((aX)^*[ModuleCat.{u + 1} Λ])).obj C))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed Λ
    ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj E) C
  exact ⟨whiskerRightIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app E).symm _ ≪≫ e.symm ≪≫
    (rightDerivedGlobalSections _ (Spec (.of k))).mapIso
      (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) aX).app E).app C)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app _⟩

/-- Blueprint `thm-kun-0f1p`: the Künneth formula in étale cohomology.

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X`, `Y` schemes of finite type over `k`. For a cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  v         v
  X --a_X-> Spec k
```

and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`, unbounded, the Künneth map
(`AlgebraicGeometry.Etale.kunnethMap`)

`κ_{E,K} : Ra_{X*} E ⊗ᴸ Ra_{Y*} K ⟶ Rc_*(Lp₁^* E ⊗ᴸ Lp₂^* K)`, `c = p₁ ≫ a_X`,

is an isomorphism in `D((Spec k)_ét, Λ)`; through `RΓ(Spec k, -)` it is the map
`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ⟶ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)`
(`AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isSepClosed`).

Following the blueprint, `κ_{E,K}` is the composite (`lem-kun-kunneth-via-0f1n`,
`AlgebraicGeometry.Etale.kunnethMap_eq`) of the projection map of `a_X`, an isomorphism by
`lem-kun-0f12`, of `Ra_{X*}` applied to the base change map of `lem-kun-0f1n` for the diagram
`X = X ⟵ W`, `Spec k = Spec k ⟵ Y`, and of the composition isomorphism
`Ra_{X*} Rp₁_* ≅ Rc_*`. -/
theorem isIso_kunnethMap_of_isSepClosed {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY (p₁ ≫ aX) rfl sq.w.symm E K) := by
  have h := isIso_tensorBaseChangeMap Λ aX (𝟙 _) aY (𝟙 X) aX p₁ p₂ aY (Category.comp_id _)
    (IsPullback.of_horiz_isIso (by simp)) sq E K
  let ι := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app E
  have hn := tensorBaseChangeMap_naturality (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY sq.w ι.hom
    (𝟙 K)
  have : IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY sq.w E K) :=
    have := IsIso.of_isIso_fac_left hn
    @IsIso.of_isIso_comp_left _ _ _ _ _ ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ].obj E).map
      (L((aX)^*[ModuleCat.{u + 1} Λ]).map (R((aY)_*[ModuleCat.{u + 1} Λ]).map (𝟙 K)))) _ _ this
  rw [kunnethMap_eq]
  infer_instance

/-- Blueprint `thm-kun-0f1p`, in `D(Λ)`: the Künneth formula
`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ≅ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)` for schemes `X`, `Y` of finite type over a
separably closed field `k`, `W = X ×_k Y`, and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`. It is
`RΓ(Spec k, -)` applied to the Künneth map (`isIso_kunnethMap_of_isSepClosed`), together with
the Leray isomorphisms and the compatibility of `RΓ(Spec k, -)` with `⊗ᴸ`. -/
theorem nonempty_iso_kunneth_of_isSepClosed {W : Scheme.{u}} (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  have := isIso_kunnethMap_of_isSepClosed Λ aX aY p₁ p₂ sq E K
  obtain ⟨e⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_of_isSepClosed Λ
    ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj E) ((R((aY)_*[ModuleCat.{u + 1} Λ])).obj K)
  exact ⟨(((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app E).symm ⊗ᵢ
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aY).app K).symm) ≪≫ e.symm ≪≫
    (rightDerivedGlobalSections _ (Spec (.of k))).mapIso
      (asIso (kunnethMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY (p₁ ≫ aX) rfl sq.w.symm E K)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ (p₁ ≫ aX)).app _⟩

end Kunneth

end Etale

end AlgebraicGeometry
