/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Stability of `Dctf`: closed immersions and finite open covers

This file bounds the exceptional inverse image `Ri^!` along a closed immersion through the
direct image along the open complement, and shows that membership in `D_c^[a, b]` with Tor
amplitude in `[a, b]` can be checked on a finite open cover.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Closed immersions: reduction to the open complement -/

section ClosedImmersion

open Pretriangulated

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

/-- For a closed immersion `i`, restricting an extension by zero recovers the complement:
`D(i^*) (Ri_! Q) ≅ Q`, since `Ri_! = Ri_* = D(i_*)` and `i^* i_* ≅ 𝟭`. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedLowerShriekIso {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    R(i)_![A] ⋙ D((i)^*[A]) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar A i ≪≫
    Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (FC := FC) A i) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (Etale.upperStarLowerStarAdjunction A i).counit) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is invariant under isomorphism. -/
lemma homologyConcentratedIn_of_iso {X : Scheme.{u}} {a b : ℤ}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (h : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a b K' := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₂` concentrated in `[a, b]` and
`X₃` in `[a, e]`, `b ≤ e`, the first term is concentrated in `[a, e + 1]`. -/
lemma homologyConcentratedIn_obj₁ {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e)
    (h₂ : _root_.DerivedCategory.homologyConcentratedIn a b T.obj₂)
    (h₃ : _root_.DerivedCategory.homologyConcentratedIn a e T.obj₃) :
    _root_.DerivedCategory.homologyConcentratedIn a (e + 1) T.obj₁ := by
  have hT' := inv_rot_of_distTriang T hT
  obtain ⟨g₂, l₂⟩ := h₂
  obtain ⟨g₃, l₃⟩ := h₃
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₁ (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift T.obj₃ a (-1) (a + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₁ (e + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift T.obj₃ e (-1) (e + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₃ b := l₂
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₃ a := g₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT' a
      (_root_.DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1)) ‹_›,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT' (e + 1) ‹_›
      (_root_.DerivedCategory.TStructure.t.isLE_of_le _ b (e + 1))⟩

end ClosedImmersion

/-! ### Gluing over a finite open cover -/

section Gluing

open ZeroObject

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- A homology sheaf vanishes if it vanishes after restriction to the members of an open
cover. -/
lemma isZero_homology_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ)
    (h : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((U i).ι)^*[A]).obj R))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A
    (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
    (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
    (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
      isIso_of_source_target_iso_zero _ ((h i.down).of_iso
        ((((U i.down).ι)^*[A].mapDerivedCategoryHomologyFunctorIso q).app R)).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso
    (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is local for an open cover. -/
lemma homologyConcentratedIn_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, _root_.DerivedCategory.homologyConcentratedIn a b (D(((U i).ι)^*[A]).obj R)) :
    _root_.DerivedCategory.homologyConcentratedIn a b R :=
  ⟨(_root_.DerivedCategory.isGE_iff R a).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isGE_iff _ a).1 (h i).1 q hq,
    (_root_.DerivedCategory.isLE_iff R b).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isLE_iff _ b).1 (h i).2 q hq⟩

omit [HasSmallSiteSheafify A] in
/-- Tor amplitude in `[a, b]` is local for an open cover. -/
lemma torAmplitudeIn_of_openCover [UpperStarPreservesFlat A] {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, torAmplitudeIn A (U i) a b (D(((U i).ι)^*[A]).obj R)) :
    torAmplitudeIn A X a b R := fun G ↦ by
  refine homologyConcentratedIn_of_openCover A U hU _ fun i ↦ ?_
  let j := (U i).ι
  let e : D((j)^*[A]).obj (R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj G) ≅
      D((j)^*[A]).obj R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj ((j)^*[A].obj G) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).app _).symm ≪≫
      leftDerivedUpperStarTensorIso A j _ _ ≪≫
      tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory A j).app R)
        ((singleFunctorCompLeftDerivedUpperStarIso A j).app G)
  obtain ⟨h₁, h₂⟩ := h i ((j)^*[A].obj G)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

end Gluing

end Etale

end AlgebraicGeometry
