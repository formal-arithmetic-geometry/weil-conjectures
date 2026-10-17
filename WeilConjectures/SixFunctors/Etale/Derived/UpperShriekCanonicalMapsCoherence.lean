/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!
# Composition of the tensor maps of `Rf^!`

For a morphism `f : X ⟶ Y` admitting a compactification and satisfying the projection formula,
the *tensor map* `τ_f(M, N) : Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`) is the transpose of the inverse
projection map followed by the counit; at `M = Λ_Y` it is the canonical map
`θ_{f,N} : ω_f ⊗ᴸ Lf^* N ⟶ Rf^! N` (`AlgebraicGeometry.Etale.dualizingComplexTensorMapOfIsIso`).
This file derives, for any coefficient category, the formal properties of `τ` and its behaviour
under composition used for cohomologically smooth morphisms
(`lem-pur-co-smooth-composition`, `lem-pur-co-smooth-etale-locality`), from two coherence
properties of the projection map: its compatibility with the associativity of `⊗ᴸ`
(`AlgebraicGeometry.Etale.ProjectionMapAssociativity`) and with a composition isomorphism
`Rh_! ≅ Rf_! ⋙ Rg_!` (`CategoryTheory.Adjunction.ProjectionCompCompatible`). Both hold for
finite coefficients (`sk-prop-sf-pf-coherence`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap_comp`: the tensor map of a
  composite is the composite of the tensor maps.
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMapOfIsIso_comp`: `θ_{f ≫ g, K}` is an
  isomorphism if `θ_{f, Lg^* K}` and `θ_{g, K}` are and `ω_g` is invertible.
- `AlgebraicGeometry.Etale.isIso_map_dualizingComplexTensorMapOfIsIso_of_comp`: if
  `θ_{u ≫ f, K}` is an isomorphism and `θ_u` is one everywhere, then `Ru^! θ_{f, K}` is one.
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_of_isIso_rightDerivedUpperShriek_map`:
  `Ru^!` reflects isomorphisms to `Lu^*` when `θ_u` is invertible and `ω_u` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product: otherwise `⊗` and `derivedTensor` use different instances, and unifying them
-- is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Predicates

variable (A)

/-- The projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` of `f` is compatible with the
associativity of the derived tensor product: the two maps
`(Rf_!M ⊗ᴸ N) ⊗ᴸ N' ⟶ Rf_!(M ⊗ᴸ (Lf^*N ⊗ᴸ Lf^*N'))`, applying the projection map twice, or once
to `N ⊗ᴸ N'` followed by the tensor comparison `Lf^*(N ⊗ᴸ N') ≅ Lf^*N ⊗ᴸ Lf^*N'`, agree. -/
structure ProjectionMapAssociativity {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Prop where
  assoc : ∀ (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      ((projectionMap A f).app M).app N ▷ N' ≫
          ((projectionMap A f).app (M ⊗ (L((f)^*[A])).obj N)).app N' ≫
          (R(f)_![A]).map (α_ M _ _).hom =
        (α_ _ N N').hom ≫ ((projectionMap A f).app M).app (N ⊗ N') ≫
          (R(f)_![A]).map (M ◁ (leftDerivedUpperStarTensorIso A f N N').hom)

end Predicates

section Invertible

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The derived pullback of an invertible object is invertible. -/
lemma isInvertible_leftDerivedUpperStar_obj
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hN : IsInvertible N) :
    IsInvertible ((L((f)^*[A])).obj N) := by
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  exact ⟨(L((f)^*[A])).obj N', ⟨(leftDerivedUpperStarTensorIso A f N N').symm ≪≫
      (L((f)^*[A])).mapIso e ≪≫ leftDerivedUpperStarUnitIso A f⟩,
    ⟨(leftDerivedUpperStarTensorIso A f N' N).symm ≪≫ (L((f)^*[A])).mapIso e' ≪≫
      leftDerivedUpperStarUnitIso A f⟩⟩

end Invertible

section TensorMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

lemma projectionMap_app_app_naturality_left
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(f)_![A]).map φ ▷ N ≫ ((projectionMap A f).app M').app N =
      ((projectionMap A f).app M).app N ≫ (R(f)_![A]).map (φ ▷ (L((f)^*[A])).obj N) :=
  NatTrans.congr_app ((projectionMap A f).naturality φ) N

lemma projectionMap_app_app_naturality_right
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (φ : N ⟶ N') :
    (R(f)_![A]).obj M ◁ φ ≫ ((projectionMap A f).app M).app N' =
      ((projectionMap A f).app M).app N ≫ (R(f)_![A]).map (M ◁ (L((f)^*[A])).map φ) :=
  ((projectionMap A f).app M).naturality φ

variable [(R(f)_![A]).IsLeftAdjoint] [IsIso (projectionMap A f)]

lemma dualizingComplexTensorMapOfIsIso_eq
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    dualizingComplexTensorMapOfIsIso f K =
      rightDerivedUpperShriekTensorMap f (𝟙_ _) K ≫ (R(f)^![A]).map (λ_ K).hom :=
  rfl

lemma isIso_dualizingComplexTensorMapOfIsIso_iff
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (dualizingComplexTensorMapOfIsIso f K) ↔
      IsIso (rightDerivedUpperShriekTensorMap f (𝟙_ _) K) := by
  rw [dualizingComplexTensorMapOfIsIso_eq, isIso_comp_right_iff]

/-- The tensor map at an invertible second variable is an isomorphism. -/
lemma isIso_rightDerivedUpperShriekTensorMap_of_isInvertible
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hN : IsInvertible N) :
    IsIso (rightDerivedUpperShriekTensorMap f M N) :=
  Adjunction.isIso_projectionTensorMap_of_isInvertible _ _
    (projectionMap_app_app_naturality_left f) hN (isInvertible_leftDerivedUpperStar_obj f hN) M

/-- The tensor map at `(M, N')` is an isomorphism if it is one at `(M, N)` for `N ≅ N'`. -/
lemma isIso_rightDerivedUpperShriekTensorMap_of_iso_right
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : N ≅ N')
    [IsIso (rightDerivedUpperShriekTensorMap f M N)] :
    IsIso (rightDerivedUpperShriekTensorMap f M N') :=
  Adjunction.isIso_projectionTensorMap_of_iso_right (rightDerivedUpperShriekAdjunction A f) _
    (projectionMap_app_app_naturality_right f) e

/-- The tensor map at `(M', N)` is an isomorphism if it is one at `(M, N)` for `M ≅ M'`. -/
lemma isIso_rightDerivedUpperShriekTensorMap_of_iso_left
    {M M' N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : M ≅ M')
    [IsIso (rightDerivedUpperShriekTensorMap f M N)] :
    IsIso (rightDerivedUpperShriekTensorMap f M' N) :=
  Adjunction.isIso_projectionTensorMap_of_iso_left (rightDerivedUpperShriekAdjunction A f) _
    (projectionMap_app_app_naturality_left f) e

variable {f} (hassoc : ProjectionMapAssociativity A f)
include hassoc

/-- The tensor map at `(M ⊗ N, N')` is an isomorphism if it is one at `(M, N)` and at
`(M, N ⊗ N')`. -/
lemma isIso_rightDerivedUpperShriekTensorMap_tensor_left
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    [IsIso (rightDerivedUpperShriekTensorMap f M N)]
    [IsIso (rightDerivedUpperShriekTensorMap f M (N ⊗ N'))] :
    IsIso (rightDerivedUpperShriekTensorMap f (M ⊗ N) N') :=
  Adjunction.isIso_projectionTensorMap_tensor_left (rightDerivedUpperShriekAdjunction A f) _
    (projectionMap_app_app_naturality_left f)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom) hassoc.assoc

/-- The tensor map at `(M, N ⊗ N')` is an isomorphism if it is one at `(M, N)` and at
`(M ⊗ N, N')`. -/
lemma isIso_rightDerivedUpperShriekTensorMap_tensor_right
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    [IsIso (rightDerivedUpperShriekTensorMap f M N)]
    [IsIso (rightDerivedUpperShriekTensorMap f (M ⊗ N) N')] :
    IsIso (rightDerivedUpperShriekTensorMap f M (N ⊗ N')) :=
  Adjunction.isIso_projectionTensorMap_tensor_right (rightDerivedUpperShriekAdjunction A f) _
    (projectionMap_app_app_naturality_left f)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom) hassoc.assoc

/-- If `θ_f` is an isomorphism at every object, then so is every tensor map of `f`. -/
lemma isIso_rightDerivedUpperShriekTensorMap_of_forall
    (hf : ∀ P, IsIso (dualizingComplexTensorMapOfIsIso (A := A) f P))
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (rightDerivedUpperShriekTensorMap f M N) := by
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) f M).1 (hf M)
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) f (M ⊗ N)).1 (hf _)
  have := isIso_rightDerivedUpperShriekTensorMap_tensor_left hassoc (M := 𝟙_ _) (N := M) (N' := N)
  exact isIso_rightDerivedUpperShriekTensorMap_of_iso_left (A := A) f (λ_ M)

end TensorMap

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
  [HasCompactification f] [HasCompactification g] [HasCompactification h]
  [(R(f)_![A]).IsLeftAdjoint] [(R(g)_![A]).IsLeftAdjoint] [(R(h)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A f)] [IsIso (projectionMap A g)] [IsIso (projectionMap A h)]
  (e : R(h)_![A] ≅ R(f)_![A] ⋙ R(g)_![A])
  (he : Adjunction.ProjectionCompCompatible (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M N ↦ ((projectionMap A g).app M).app N) (fun M N ↦ ((projectionMap A h).app M).app N)
    (fun N ↦ (leftDerivedUpperStarComp A f g h w.symm).hom.app N) e)
include he

set_option hygiene false in
/-- The isomorphism `Rh^! ≅ Rg^! ⋙ Rf^!` of right adjoints induced by `e`. -/
local notation "ρ[" e "]" =>
  Adjunction.rightAdjointUniq ((rightDerivedUpperShriekAdjunction A h).ofNatIsoLeft e)
    ((rightDerivedUpperShriekAdjunction A f).comp (rightDerivedUpperShriekAdjunction A g))

/-- **The tensor map of a composite.** For `h = f ≫ g` and a composition isomorphism
`e : Rh_! ≅ Rf_! ⋙ Rg_!` compatible with the projection maps, the tensor map of `h` is, through
the induced isomorphism `ρ : Rh^! ≅ Rg^! ⋙ Rf^!`, the composite of the tensor map of `f` at
`(Rg^! M, Lg^* N)` and of `Rf^!` of the tensor map of `g` at `(M, N)`. -/
theorem rightDerivedUpperShriekTensorMap_comp
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    rightDerivedUpperShriekTensorMap h M N ≫ (ρ[e]).hom.app (M ⊗ N) =
      (ρ[e]).hom.app M ▷ (L((h)^*[A])).obj N ≫
        (R(f)^![A]).obj ((R(g)^![A]).obj M) ◁
          (leftDerivedUpperStarComp A f g h w.symm).hom.app N ≫
        rightDerivedUpperShriekTensorMap f ((R(g)^![A]).obj M) ((L((g)^*[A])).obj N) ≫
        (R(f)^![A]).map (rightDerivedUpperShriekTensorMap g M N) :=
  Adjunction.projectionTensorMap_comp_rightAdjointUniq (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A g) (rightDerivedUpperShriekAdjunction A h) _ _ _
    (projectionMap_app_app_naturality_left f) (projectionMap_app_app_naturality_left g) _ e he M N

/-- **Composition of the canonical maps.** For `h = f ≫ g` with a composition isomorphism
compatible with the projection maps and an associative projection map of `f`: if `ω_g` is
invertible and `θ_{g, K}` and `θ_{f, Lg^* K}` are isomorphisms, then so is `θ_{h, K}`. The
tensor map of `h` at `(Λ, K)` factors through `τ_f(ω_g, Lg^* K)` and `Rf^! θ_{g, K}`; the first
is an isomorphism since `ω_g` is invertible and `θ_f` is invertible at
`Lg^* K ⊗ᴸ ω_g ≅ ω_g ⊗ᴸ Lg^* K` (`lem-pur-co-smooth-composition`). -/
theorem isIso_dualizingComplexTensorMapOfIsIso_comp (hassoc : ProjectionMapAssociativity A f)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hf : IsIso (dualizingComplexTensorMapOfIsIso f ((L((g)^*[A])).obj K)))
    (hg : IsIso (dualizingComplexTensorMapOfIsIso g K))
    (hω : IsInvertible (dualizingComplex A g)) :
    IsIso (dualizingComplexTensorMapOfIsIso h K) := by
  rw [isIso_dualizingComplexTensorMapOfIsIso_iff]
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) g K).1 hg
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) f _).1 hf
  have := isIso_rightDerivedUpperShriekTensorMap_of_isInvertible f
    (𝟙_ _ ⊗ (L((g)^*[A])).obj K) (N := (R(g)^![A]).obj (𝟙_ _)) hω
  have := isIso_rightDerivedUpperShriekTensorMap_tensor_right hassoc (M := 𝟙_ _)
    (N := (L((g)^*[A])).obj K) (N' := (R(g)^![A]).obj (𝟙_ _))
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip A Y
  have := isIso_rightDerivedUpperShriekTensorMap_of_iso_right f (M := 𝟙_ _)
    (N := (L((g)^*[A])).obj K ⊗ (R(g)^![A]).obj (𝟙_ _))
    (N' := (R(g)^![A]).obj (𝟙_ _) ⊗ (L((g)^*[A])).obj K)
    ((β.app ((L((g)^*[A])).obj K)).app ((R(g)^![A]).obj (𝟙_ _)))
  have := isIso_rightDerivedUpperShriekTensorMap_of_isInvertible f (𝟙_ _)
    (N := (R(g)^![A]).obj (𝟙_ _)) hω
  have := isIso_rightDerivedUpperShriekTensorMap_tensor_left hassoc (M := 𝟙_ _)
    (N := (R(g)^![A]).obj (𝟙_ _)) (N' := (L((g)^*[A])).obj K)
  have := isIso_rightDerivedUpperShriekTensorMap_of_iso_left f (N := (L((g)^*[A])).obj K)
    (λ_ ((R(g)^![A]).obj (𝟙_ _)))
  have hc := rightDerivedUpperShriekTensorMap_comp f g h w e he (𝟙_ _) K
  have : IsIso (rightDerivedUpperShriekTensorMap h (𝟙_ _) K ≫ (ρ[e]).hom.app (𝟙_ _ ⊗ K)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ρ[e]).hom.app (𝟙_ _ ⊗ K))

/-- **Descent of the canonical maps along a composite.** For `h = u ≫ f` with a composition
isomorphism compatible with the projection maps and an associative projection map of `u`: if
`θ_u` is an isomorphism at every object and `θ_{h, K}` is an isomorphism, then so is
`Ru^! θ_{f, K}` (`lem-pur-co-smooth-etale-locality`, step 3). -/
theorem isIso_map_dualizingComplexTensorMapOfIsIso_of_comp
    (hassoc : ProjectionMapAssociativity A f)
    (hf : ∀ P, IsIso (dualizingComplexTensorMapOfIsIso (A := A) f P))
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hh : IsIso (dualizingComplexTensorMapOfIsIso h K)) :
    IsIso ((R(f)^![A]).map (dualizingComplexTensorMapOfIsIso g K)) := by
  rw [isIso_dualizingComplexTensorMapOfIsIso_iff] at hh
  have := isIso_rightDerivedUpperShriekTensorMap_of_forall hassoc hf ((R(g)^![A]).obj (𝟙_ _))
    ((L((g)^*[A])).obj K)
  have hc := rightDerivedUpperShriekTensorMap_comp f g h w e he (𝟙_ _) K
  have : IsIso (rightDerivedUpperShriekTensorMap h (𝟙_ _) K ≫ (ρ[e]).hom.app (𝟙_ _ ⊗ K)) :=
    inferInstance
  rw [hc] at this
  have := (isIso_comp_left_iff _ _).1 this
  have := (isIso_comp_left_iff _ _).1 this
  have : IsIso ((R(f)^![A]).map (rightDerivedUpperShriekTensorMap g (𝟙_ _) K)) :=
    (isIso_comp_left_iff _ _).1 this
  rw [dualizingComplexTensorMapOfIsIso_eq, Functor.map_comp]
  infer_instance

end Composition

section Reflect

variable {U X : Scheme.{u}} (u : U ⟶ X) [HasCompactification u] [(R(u)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A u)]

/-- If `θ_u` is an isomorphism at every object and `ω_u` is invertible, then `Ru^!` reflects
isomorphisms to `Lu^*`: `Ru^! ≅ ω_u ⊗ᴸ Lu^*(-)`, and tensoring with an invertible object
reflects isomorphisms. -/
theorem isIso_leftDerivedUpperStar_map_of_isIso_rightDerivedUpperShriek_map
    (hu : ∀ P, IsIso (dualizingComplexTensorMapOfIsIso (A := A) u P))
    (hω : IsInvertible (dualizingComplex A u))
    {P Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : P ⟶ Q)
    (h : IsIso ((R(u)^![A]).map φ)) : IsIso ((L((u)^*[A])).map φ) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf U.smallEtaleTopology A)
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) u P).1 (hu P)
  have := (isIso_dualizingComplexTensorMapOfIsIso_iff (A := A) u Q).1 (hu Q)
  have hn := Adjunction.projectionTensorMap_naturality_right
    (rightDerivedUpperShriekAdjunction A u) _ (projectionMap_app_app_naturality_right u) (𝟙_ _) φ
  have : IsIso ((R(u)^![A]).map (𝟙_ _ ◁ φ)) := by
    rw [id_whiskerLeft, Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso ((R(u)^![A]).obj (𝟙_ _) ◁ (L((u)^*[A])).map φ ≫
      rightDerivedUpperShriekTensorMap u (𝟙_ _) Q) := by
    erw [hn]
    infer_instance
  have : IsIso ((R(u)^![A]).obj (𝟙_ _) ◁ (L((u)^*[A])).map φ) :=
    IsIso.of_isIso_comp_right _ (rightDerivedUpperShriekTensorMap u (𝟙_ _) Q)
  have hω' : IsInvertible ((R(u)^![A]).obj (𝟙_ _)) := hω
  exact hω'.isIso_of_isIso_whiskerLeft _

end Reflect

end Etale

end AlgebraicGeometry
