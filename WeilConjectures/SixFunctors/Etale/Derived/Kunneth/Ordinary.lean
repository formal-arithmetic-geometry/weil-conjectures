/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

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

`Lc^*(Rf_* E ⊗ᴸ Rg_* K) ≅ Lc^* Rf_* E ⊗ᴸ Lc^* Rg_* K ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lq^* Lg^* Rg_* K
  ⟶ Lp^* E ⊗ᴸ Lq^* K`

of the monoidality of `Lc^*`, the composition isomorphisms `Lc^* ≅ Lp^* Lf^*`,
`Lc^* ≅ Lq^* Lg^*`, and the counits of `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*`. -/
noncomputable def kunnethMap (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(S)[A]).obj (R((f)_*[A]).obj E)).obj (R((g)_*[A]).obj K) ⟶
      R((c)_*[A]).obj (((-⊗ᴸ-(W)[A]).obj (L((p)^*[A]).obj E)).obj (L((q)^*[A]).obj K)) :=
  (derivedUpperStarLowerStarAdjunction A c).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A c).app _).app _ ≫
      ((-⊗ᴸ-(W)[A]).map ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app _ ≫
      ((-⊗ᴸ-(W)[A]).obj _).map ((leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)))

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
  rw [kunnethMap, kunnethMap, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h₁ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A c).naturality
    (R((f)_*[A]).map φ)) (R((g)_*[A]).obj K)
  have h₂ := ((leftDerivedUpperStarTensorComparison A c).app
    (R((f)_*[A]).obj E')).naturality (R((g)_*[A]).map ψ)
  simp only [Functor.map_comp, Category.assoc] at h₁ h₂ ⊢
  have hu : ∀ {E E' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : E ⟶ E'),
      L((c)^*[A]).map (R((f)_*[A]).map φ) ≫
        (leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E') =
      ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E)) ≫
        L((p)^*[A]).map φ := fun φ ↦ by
    rw [NatTrans.naturality_assoc]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    congr 2
    exact (derivedUpperStarLowerStarAdjunction A _).counit.naturality _
  have hv : ∀ {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (ψ : K ⟶ K'),
      L((c)^*[A]).map (R((g)_*[A]).map ψ) ≫
        (leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K') =
      ((leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)) ≫
        L((q)^*[A]).map ψ := fun ψ ↦ by
    rw [NatTrans.naturality_assoc]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    congr 2
    exact (derivedUpperStarLowerStarAdjunction A _).counit.naturality _
  simp only [derivedTensor, curriedTensor_obj_map, curriedTensor_map_app, NatTrans.comp_app,
    Category.assoc, leftDerivedUpperStarDerivedTensor,
    derivedTensorLeftDerivedUpperStar] at h₁ h₂ hu hv ⊢
  have h₁' : L((c)^*[A]).map (R((f)_*[A]).map φ ▷ R((g)_*[A]).obj K) ≫
      ((leftDerivedUpperStarTensorComparison A c).app (R((f)_*[A]).obj E')).app
        (R((g)_*[A]).obj K) =
      ((leftDerivedUpperStarTensorComparison A c).app (R((f)_*[A]).obj E)).app
        (R((g)_*[A]).obj K) ≫
        L((c)^*[A]).map (R((f)_*[A]).map φ) ▷ L((c)^*[A]).obj (R((g)_*[A]).obj K) := h₁
  have h₂' : L((c)^*[A]).map (R((f)_*[A]).obj E' ◁ R((g)_*[A]).map ψ) ≫
      ((leftDerivedUpperStarTensorComparison A c).app (R((f)_*[A]).obj E')).app
        (R((g)_*[A]).obj K') =
      ((leftDerivedUpperStarTensorComparison A c).app (R((f)_*[A]).obj E')).app
        (R((g)_*[A]).obj K) ≫
        L((c)^*[A]).obj (R((f)_*[A]).obj E') ◁ L((c)^*[A]).map (R((g)_*[A]).map ψ) := h₂
  rw [reassoc_of% h₂', reassoc_of% h₁']
  congr 1
  simp only [Functor.id_obj, whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp]
  rw [hu, hv]

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

end Maps

section Constant

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The constant sheaf functor preserves finite limits: it is the constant presheaf functor
followed by sheafification. -/
instance preservesFiniteLimits_constantSheaf :
    PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)

/-- Blueprint `def-kun-constant-sheaf`: constant sheaves and constant complexes.

The constant complex functor `D(Λ) ⥤ D(X_ét, Λ)`, `K ↦ K_X`: the functor induced on derived
categories by the exact constant sheaf functor `M ↦ M_X`. -/
noncomputable def constantFunctor :
    DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory

/-- Blueprint `def-kun-cd` (for sheaves of `Λ`-modules): the scheme `X` has *finite
cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with `H^q(X, F) = 0` for
every étale sheaf `F` of `Λ`-modules and every `q > d`. For a torsion ring `Λ` every such sheaf
is a torsion abelian sheaf, so this follows from finiteness of the torsion étale cohomological
dimension `cd(X)` of the blueprint. -/
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

variable {X} in
/-- Blueprint `def-kun-cd` (for morphisms, and sheaves of `Λ`-modules): the morphism `f` has
*finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. -/
def HasFiniteCohomologicalDimensionMorphism {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)))

end Constant

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived pullback along the identity is the identity: `L(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) :
    L((𝟙 X)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  leftDerivedUpperStarIsoMapDerivedCategory _ (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarId _ X) ≪≫
      Functor.mapDerivedCategoryIdIso _

section Inputs

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (1).

Let `K` be a field and `f : X ⟶ Y` a morphism between `K`-schemes of finite type. For a torsion
coefficient ring `Λ`, the higher direct images `R^q f_*` of étale sheaves of `Λ`-modules vanish
in all large degrees `q`. -/
theorem hasFiniteCohomologicalDimensionMorphism (hΛ : IsAddTorsion Λ) {K : Type u} [Field K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f :=
  sorry

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (2).

Over a separably closed field `K`, a `K`-scheme `X` of finite type has finite étale
cohomological dimension: for a torsion coefficient ring `Λ`, `H^q(X, F) = 0` for every étale
sheaf `F` of `Λ`-modules and all large `q`. -/
theorem hasFiniteCohomologicalDimension_of_isSepClosed (hΛ : IsAddTorsion Λ) {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] :
    HasFiniteCohomologicalDimension Λ X :=
  sorry

/-- Blueprint `lem-kun-0f12`: tensor product with a constant complex.

Let `X` be a quasi-compact quasi-separated scheme of finite cohomological dimension and `Λ` a
torsion ring. For `E ∈ D(X_ét, Λ)` and `C ∈ D(Λ)`,

`RΓ(X, E) ⊗ᴸ C ≅ RΓ(X, E ⊗ᴸ C_X)`,

where `C_X` is the constant complex (`AlgebraicGeometry.Etale.constantFunctor`). -/
theorem nonempty_iso_rightDerivedGlobalSections_derivedTensor_constantFunctor
    (hΛ : IsAddTorsion Λ) (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : HasFiniteCohomologicalDimension Λ X)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗ C ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj ((constantFunctor Λ X).obj C))) :=
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

/-- The base change of the terminal object of `Y.Etale` along `f : X ⟶ Y` is terminal in
`X.Etale`. -/
noncomputable def isTerminalPullbackEtaleTerminal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsTerminal ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj
      (etaleTerminal Y)) :=
  have : IsIso ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj
      (etaleTerminal Y)).hom := by
    rw [MorphismProperty.Over.pullback_obj_hom]
    exact inferInstanceAs (IsIso (pullback.snd (𝟙 Y) f))
  (isTerminalEtaleTerminal X).ofIso (MorphismProperty.Over.isoMk
    (asIso ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj
      (etaleTerminal Y)).hom) (Category.comp_id _)).symm

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

/-- Blueprint `lem-kun-pullback-constant` (underived): the inverse image of a constant sheaf is
the constant sheaf, `f^*(M_Y) ≅ M_X`. Both functors are left adjoint to the global sections
functor on `X_ét`, since `Γ(Y, f_* G) = Γ(X, G)`. -/
noncomputable def constantSheafCompUpperStarIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ (f)^*[ModuleCat.{u + 1} Λ] ≅
      constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (((constantSheafAdj _ _ (isTerminalEtaleTerminal Y)).comp
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)).leftAdjointUniq
    (constantSheafAdj _ _ (isTerminalPullbackEtaleTerminal f))

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
end Point

end Inputs

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

omit [HasInvertibleExponent Λ (Spec (.of k))] in
/-- `RΓ(X, E ⊗ᴸ La_X^* C) ≅ RΓ(X, E) ⊗ᴸ RΓ(Spec k, C)` for a finite-type scheme `X` over a
separably closed field `k`: the tensor product with a constant complex
(`lem-kun-0f12`), through the identification of complexes on `Spec k` with constant complexes. -/
theorem nonempty_iso_rightDerivedGlobalSections_derivedTensor_leftDerivedUpperStar
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
          ((L((aX)^*[ModuleCat.{u + 1} Λ])).obj C))) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_constantFunctor Λ hΛ X
    (hasFiniteCohomologicalDimension_of_isSepClosed Λ hΛ aX) E
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)
  obtain ⟨e₂⟩ := nonempty_iso_constantFunctor_rightDerivedGlobalSections_of_isSepClosed Λ C
  exact ⟨e₁ ≪≫ (rightDerivedGlobalSections _ X).mapIso (((derivedTensor _ X).obj E).mapIso
    (((constantFunctorCompLeftDerivedUpperStarIso Λ aX).app _).symm ≪≫
      (L((aX)^*[ModuleCat.{u + 1} Λ])).mapIso e₂.symm))⟩

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

and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`, unbounded,

`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ≅ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)`.

Following the blueprint, it is the composite of the tensor product with a constant complex
(`lem-kun-0f12`), of `RΓ(X, -)` applied to the base change map of `lem-kun-0f1n` for the
diagram `X = X ⟵ W`, `Spec k = Spec k ⟵ Y`, and of the Leray isomorphisms. -/
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
  have := isIso_tensorBaseChangeMap Λ aX (𝟙 _) aY (𝟙 X) aX p₁ p₂ aY (Category.comp_id _)
    (IsPullback.of_horiz_isIso (by simp)) sq E K
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_leftDerivedUpperStar Λ aX
    E ((R((aY)_*[ModuleCat.{u + 1} Λ])).obj K)
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
  let ι := leftDerivedUpperStarId Λ X
  refine ⟨whiskerLeftIso _
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aY).app K).symm ≪≫ e₁ ≪≫
    (RΓ X).mapIso (((derivedTensor _ X).mapIso (ι.app E).symm).app _ ≪≫
      asIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) p₁ p₂ aX aY sq.w
        ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj E) K)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ p₁).app _ ≪≫
    (RΓ W).mapIso (((derivedTensor _ W).mapIso
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).mapIso (ι.app E))).app _)⟩

end Kunneth

end Etale

end AlgebraicGeometry
