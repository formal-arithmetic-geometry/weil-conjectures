/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionMapTraceCounit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Trace counits and tensoring with a fixed object

For `f : X ⟶ Y` admitting a compactification, an object `T` on `X` and `t : Rf_! T ⟶ 𝟙`, the
*trace counit* `Rf_!(G K) ≅ Rf_!(T ⊗ᴸ Lf^* K) ≅ Rf_! T ⊗ᴸ K ⟶ K` is the inverse of the projection
map followed by `t` (for `A = ModuleCat Λ` this is
`AlgebraicGeometry.Etale.lowerShriekTraceCounit`).
For `a : Lf^* N_Y ≅ N_X`, tensoring the trace counit at `K` with `N_Y` is the trace counit at
`K ⊗ᴸ N_Y`, read through the comparison `Rf_! M ⊗ᴸ N_Y ⟶ Rf_!(M ⊗ᴸ N_X)` (the projection map
followed by `a`) and an identification `θ : G K ⊗ᴸ N_X ⟶ G(K ⊗ᴸ N_Y)` compatible with the
associator (`AlgebraicGeometry.Etale.traceCounit_derivedTensorRight`). For `A = ModuleCat Λ` and
`N = Λ ⧸ J` this is the compatibility of trace counits with change of finite coefficients.

We also record the associator `(M ⊗ᴸ L) ⊗ᴸ N ≅ M ⊗ᴸ (L ⊗ᴸ N)` as a natural isomorphism in `L`
(`AlgebraicGeometry.Etale.derivedTensorObjCompDerivedTensorRightIso`).

## Implementation notes

The statements are made for a general coefficient category, so that the monoidal structure of
`D(X_ét)` is the one of `AlgebraicGeometry.Etale.derivedTensor` (see the implementation notes of
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction`). They are written with
`AlgebraicGeometry.Etale.derivedTensorRight` and with the inverses of the projection maps and
the trace counits as parameters, and are deduced from the curried form
`CategoryTheory.Adjunction.traceCounit_curriedTensor` of the abstract statement: the kernel then
never compares projection maps evaluated at objects written differently (such as `K ⊗ N` and
`(derivedTensorRight N).obj K`), which it cannot do in reasonable time.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The associator `(M ⊗ᴸ L) ⊗ᴸ N ≅ M ⊗ᴸ (L ⊗ᴸ N)`
(`AlgebraicGeometry.Etale.derivedTensorRightTensorIso`) is natural in `L`. -/
lemma derivedTensorRightTensorIso_hom_naturality {X : Scheme.{u}}
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {L L' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : L ⟶ L') :
    ((-⊗ᴸ-(X)[A]).obj M ⋙ derivedTensorRight A X N).map g ≫
        (derivedTensorRightTensorIso A N M L').hom =
      (derivedTensorRightTensorIso A N M L).hom ≫
        (derivedTensorRight A X N ⋙ (-⊗ᴸ-(X)[A]).obj M).map g :=
  associator_naturality_middle _ _ _

/-- Tensoring on the left with `M` commutes with tensoring on the right with `N`: the associator
`(M ⊗ᴸ L) ⊗ᴸ N ≅ M ⊗ᴸ (L ⊗ᴸ N)` (`AlgebraicGeometry.Etale.derivedTensorRightTensorIso`), natural
in `L`. -/
noncomputable def derivedTensorObjCompDerivedTensorRightIso (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (-⊗ᴸ-(X)[A]).obj M ⋙ derivedTensorRight A X N ≅
      derivedTensorRight A X N ⋙ (-⊗ᴸ-(X)[A]).obj M :=
  NatIso.ofComponents (fun L ↦ derivedTensorRightTensorIso A N M L)
    (fun g ↦ derivedTensorRightTensorIso_hom_naturality A M N g)

@[simp]
lemma derivedTensorObjCompDerivedTensorRightIso_hom_app (X : Scheme.{u})
    (M N L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorObjCompDerivedTensorRightIso A X M N).hom.app L =
      (derivedTensorRightTensorIso A N M L).hom :=
  rfl

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}}

/-- The associativity of the projection map of `Rf_!`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`), for the chosen
compactification. -/
private lemma projectionMap_assoc (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMap A f).app K).app L ▷ N ≫
        ((projectionMap A f).app (K ⊗ L((f)^*[A]).obj L)).app N ≫
        (R(f)_![A]).map (α_ K (L((f)^*[A]).obj L) (L((f)^*[A]).obj N)).hom =
      (α_ ((R(f)_![A]).obj K) L N).hom ≫
        ((projectionMap A f).app K).app (L ⊗ N) ≫
        (R(f)_![A]).map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app L).app N) :=
  projectionMapOfCompactification_assoc A _ K L N

/-- The naturality of the projection map of `Rf_!` in its first variable. -/
private lemma projectionMap_naturality_left (f : X ⟶ Y) [HasCompactification f]
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K')
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(f)_![A]).map φ ▷ L ≫ ((projectionMap A f).app K').app L =
      ((projectionMap A f).app K).app L ≫ (R(f)_![A]).map (φ ▷ (L((f)^*[A])).obj L) :=
  NatTrans.congr_app ((projectionMap A f).naturality φ) L

/-- **Trace counits tensored with a fixed object.** Let `f : X ⟶ Y` admit a compactification,
`t : Rf_! T ⟶ 𝟙`, `γ_K : G K ≅ T ⊗ᴸ Lf^* K` and `a : Lf^* N_Y ≅ N_X`, and let the projection maps
`PF_{T, K}` and `PF_{T, K ⊗ᴸ N_Y}` have inverses `p` and `p'`. Let
`θ : G K ⊗ᴸ N_X ⟶ G(K ⊗ᴸ N_Y)` be compatible with `γ` through the associator and
`Lf^*(K ⊗ᴸ N_Y) ≅ Lf^* K ⊗ᴸ N_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorRightIso`). Then the trace counit
`Rf_! γ_K ≫ p ≫ t ▷ K ≫ λ_K`, tensored with `N_Y`, is the comparison
`Rf_!(G K) ⊗ᴸ N_Y ⟶ Rf_!(G K ⊗ᴸ N_X)` (the projection map followed by `a`), followed by
`Rf_! θ` and the trace counit at `K ⊗ᴸ N_Y`. The trace counits are given as morphisms `τ` equal
to `t ▷ K ≫ λ_K`. -/
theorem traceCounit_derivedTensorRight (f : X ⟶ Y) [HasCompactification f]
    (T : DerivedCategory (Sheaf X.smallEtaleTopology A)) (t : (R(f)_![A]).obj T ⟶ 𝟙_ _)
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (γ : ∀ K, G.obj K ≅ ((-⊗ᴸ-(X)[A]).obj T).obj ((L((f)^*[A])).obj K))
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (p : (R(f)_![A]).obj (((-⊗ᴸ-(X)[A]).obj T).obj ((L((f)^*[A])).obj K)) ⟶
      ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj T)).obj K)
    (hp₁ : ((projectionMap A f).app T).app K ≫ p = 𝟙 _)
    (hp₂ : p ≫ ((projectionMap A f).app T).app K = 𝟙 _)
    (p' : (R(f)_![A]).obj (((-⊗ᴸ-(X)[A]).obj T).obj
        ((L((f)^*[A])).obj ((derivedTensorRight A Y NY).obj K))) ⟶
      ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj T)).obj ((derivedTensorRight A Y NY).obj K))
    (hp₁' : ((projectionMap A f).app T).app ((derivedTensorRight A Y NY).obj K) ≫ p' = 𝟙 _)
    (hp₂' : p' ≫ ((projectionMap A f).app T).app ((derivedTensorRight A Y NY).obj K) = 𝟙 _)
    (τK : ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj T)).obj K ⟶ K)
    (hτK : τK = t ▷ K ≫ (λ_ K).hom)
    (τKN : ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj T)).obj ((derivedTensorRight A Y NY).obj K) ⟶
      (derivedTensorRight A Y NY).obj K)
    (hτKN : τKN = t ▷ (derivedTensorRight A Y NY).obj K ≫
      (λ_ ((derivedTensorRight A Y NY).obj K)).hom)
    (θ : (derivedTensorRight A X NX).obj (G.obj K) ⟶ G.obj ((derivedTensorRight A Y NY).obj K))
    (hθ : θ ≫ (γ ((derivedTensorRight A Y NY).obj K)).hom =
      (derivedTensorRight A X NX).map (γ K).hom ≫
        (derivedTensorRightTensorIso A NX T ((L((f)^*[A])).obj K)).hom ≫
        ((-⊗ᴸ-(X)[A]).obj T).map ((leftDerivedUpperStarDerivedTensorRightIso A f a).app K).inv) :
    (((projectionMap A f).app (G.obj K)).app NY ≫
        (R(f)_![A]).map (((-⊗ᴸ-(X)[A]).obj (G.obj K)).map a.hom)) ≫
      (R(f)_![A]).map θ ≫
      ((R(f)_![A]).map (γ ((derivedTensorRight A Y NY).obj K)).hom ≫ p' ≫ τKN) =
    (derivedTensorRight A Y NY).map ((R(f)_![A]).map (γ K).hom ≫ p ≫ τK) := by
  have h := Adjunction.traceCounit_curriedTensor (fun K L ↦ ((projectionMap A f).app K).app L)
    (projectionMap_assoc A f) a.hom (projectionMap_naturality_left A f) T t K
    ((derivedTensorRight A Y NY).obj K) rfl
    (𝟙 _) (eqToHom_refl _ _).symm (γ K) (γ _)
    (((leftDerivedUpperStarTensorComparison A f).app K).app NY) HEq.rfl
    ((leftDerivedUpperStarDerivedTensorRightIso A f a).app K)
    (leftDerivedUpperStarDerivedTensorRightIso_hom_app A f a K)
    (derivedTensorRightTensorIso A NX T _) rfl p hp₁ hp₂ p' hp₁' hp₂' τK hτK τKN hτKN θ hθ
  rwa [Category.comp_id] at h

end AlgebraicGeometry.Etale
