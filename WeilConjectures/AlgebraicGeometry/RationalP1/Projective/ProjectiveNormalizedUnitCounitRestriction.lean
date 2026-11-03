/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitInversionCondition
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CounitInversionCondition
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ProjectionNaturality
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality

/-! # Normalized projective-line unit and counit on full subcategories

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-unit-counit.proof.md,
Well-definedness (1)--(3)
(blueprint: lem-sfb-projective-normalized-unit-counit-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u a b v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1

open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] tensorShiftIso twist rationalTwistFunctor projectionMateMap
  AlgebraicGeometry.ProEtale.RationalP1.projectionMap
  pushSectionIso supportedUnitIso singleUnitIso trace

-- Reuse the proved parametric private arguments of RationalP1UnitCounit locally.
section Naturality

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem compose_square {D : Type*} [Category* D]
    {A A' B B' C C' : D}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : C ⟶ C'}
    {p : A ⟶ B} {p' : A' ⟶ B'} {q : B ⟶ C} {q' : B' ⟶ C'}
    (hp : a ≫ p' = p ≫ b) (hq : b ≫ q' = q ≫ c) :
    a ≫ (p' ≫ q') = (p ≫ q) ≫ c := by
  rw [← Category.assoc, hp, Category.assoc, hq, Category.assoc]

private theorem map_square {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {A A' B B' : C}
    {a : A ⟶ A'} {b : B ⟶ B'} {q : A ⟶ B} {q' : A' ⟶ B'}
    (h : a ≫ q' = q ≫ b) :
    G.map a ≫ G.map q' = G.map q ≫ G.map b := by
  rw [← G.map_comp, h, G.map_comp]

private theorem inverse_square {D : Type*} [Category* D]
    {A A' B B' : D} {a : A ⟶ A'} {b : B ⟶ B'}
    {q : A ⟶ B} {q' : A' ⟶ B'} [IsIso q] [IsIso q']
    (h : a ≫ q' = q ≫ b) : b ≫ inv q' = inv q ≫ a := by
  apply (cancel_epi q).1
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem inverse_iso_square {D : Type*} [Category* D]
    {A A' B B' : D} (q : A ≅ B) (q' : A' ≅ B')
    {a : A ⟶ A'} {b : B ⟶ B'} (h : a ≫ q'.hom = q.hom ≫ b) :
    b ≫ q'.inv = q.inv ≫ a := by
  apply (cancel_epi q.hom).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

private theorem tensor_square {D : Type*} [Category* D] [MonoidalCategory D]
    {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom f (𝟙 B) ≫ (A' ◁ g) = (A ◁ g) ≫ tensorHom f (𝟙 B') := by
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp]

private def ProjectionMateNatural (a : ProjectionMateFamily Λ) : Prop :=
  ∀ {X S : Scheme.{u}} (g : X ⟶ S)
    {A A' : DerivedCategory (Modules Λ X)} (f : A ⟶ A')
    (B : DerivedCategory (Modules Λ S)),
    tensorHom ((moduleObjectDerivedPushforward Λ g).map f) (𝟙 B) ≫ a g A' B =
      a g A B ≫ (moduleObjectDerivedPushforward Λ g).map
        (tensorHom f (𝟙 ((moduleObjectDerivedPullback Λ g).obj B)))

attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem normalized_mate_naturality
    (a : ProjectionMateFamily Λ) (ha : ProjectionMateNormalized Λ a) :
    ProjectionMateNatural Λ a := by
  unfold ProjectionMateNatural ProjectionMateNormalized ProjectionMateFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  intro X S g A A' f B
  rw [eq_of_heq (ha g A' B), eq_of_heq (ha g A B)]
  have hm := congr_app
    (((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
      (moduleObjectDerivedTensorComparison Λ g)).naturality f) B
  change ((moduleObjectDerivedPushforward Λ g).map f ▷ B) ≫
      moduleObjectProjectionMate Λ g A' B =
    moduleObjectProjectionMate Λ g A B ≫ (moduleObjectDerivedPushforward Λ g).map
      (f ▷ (moduleObjectDerivedPullback Λ g).obj B) at hm
  simpa only [tensorHom_id] using hm

private theorem projectionMateMap_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {A A' : DerivedCategory (Modules Λ X)} (f : A ⟶ A')
    (B : DerivedCategory (Modules Λ S)) :
    tensorHom ((moduleObjectDerivedPushforward Λ g).map f) (𝟙 B) ≫
        projectionMateMap Λ g A' B =
      projectionMateMap Λ g A B ≫ (moduleObjectDerivedPushforward Λ g).map
        (tensorHom f (𝟙 ((moduleObjectDerivedPullback Λ g).obj B))) :=
by
  unfold projectionMateMap
  exact normalized_mate_naturality Λ (projectionMate_existsUnique Λ).exists.choose
    (projectionMate_existsUnique Λ).exists.choose_spec g f B

private theorem twistProjectionMap_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ g).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    {A B : DerivedCategory (Modules Λ X)} (f : A ⟶ B) :
    (twist Λ S LS).map ((moduleObjectDerivedPushforward Λ g).map f) ≫
        twistProjectionMap Λ g LS LX e B =
      twistProjectionMap Λ g LS LX e A ≫ (moduleObjectDerivedPushforward Λ g).map
        ((twist Λ X LX).map f) := by
  have h₁ := inverse_iso_square
    (tensorShiftIso Λ S LS ((moduleObjectDerivedPushforward Λ g).obj A))
    (tensorShiftIso Λ S LS ((moduleObjectDerivedPushforward Λ g).obj B))
    (tensorShiftIso_naturality Λ S LS ((moduleObjectDerivedPushforward Λ g).map f))
  have h₂ := projectionMateMap_naturality Λ g f
    (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧)
  have h₃ := map_square (moduleObjectDerivedPushforward Λ g)
    (compose_square (tensor_square f e.hom) (tensorShiftIso_naturality Λ X LX f))
  unfold twistProjectionMap
  exact compose_square h₁ (compose_square h₂ h₃)

private theorem diagonalClassMap_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    {M N : DerivedCategory (Modules Λ (ProjectiveLine Y))} (f : M ⟶ N) :
    (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).map f ≫
        diagonalClassMap Λ Y L d N =
      diagonalClassMap Λ Y L d M ≫
        (twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).map
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).map f) := by
  exact compose_square (diagonalTensorIso_naturality Λ Y f)
    (compose_square (tensor_square
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).map f)
      ((supportedUnitIso Λ Y).hom ≫ d.delta))
      (tensorShiftIso_naturality Λ _ _ _))

private theorem unitComponent_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    {M N : DerivedCategory (Modules Λ (ProjectiveLine Y))} (f : M ⟶ N)
    (hM : IsIso ((condensedAmbientExchange Λ (square Y)).app M) ∧
      IsIso (twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    (hN : IsIso ((condensedAmbientExchange Λ (square Y)).app N) ∧
      IsIso (twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj N))) :
    f ≫ unitComponent Λ Y L d e N hN.1 hN.2 =
      unitComponent Λ Y L d e M hM.1 hM.2 ≫
        (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
            ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map f)) := by
  have := hM.1
  have := hM.2
  have := hN.1
  have := hN.2
  have h₁ := (pushSectionIso Λ Y).hom.naturality f
  have h₂ := map_square (moduleObjectDerivedPushforward Λ (secondProjection Y))
    (diagonalClassMap_naturality Λ Y L d f)
  have h₃ := inverse_square (twistProjectionMap_naturality Λ (secondProjection Y)
    (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).map f))
  have h₄ := map_square (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y)))
    (inverse_square ((condensedAmbientExchange Λ (square Y)).naturality f))
  unfold unitComponent
  exact compose_square h₁ (compose_square h₂ (compose_square h₃ h₄))

private theorem counitComponent_naturality (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    {K K' : DerivedCategory (Modules Λ Y)} (f : K ⟶ K')
    (hK : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hK' : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K'
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map f)) ≫
        counitComponent Λ Y L d K' hK' = counitComponent Λ Y L d K hK ≫ f := by
  have := hK
  have := hK'
  have h₁ := map_square (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y))
    (inverse_iso_square
      (tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))
      (tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K'))
      (tensorShiftIso_naturality Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map f)))
  have h₂ := inverse_square (projectionMap_naturality Λ (ProjectiveLine Y ↘ Y) f
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
  have h₃ := tensor_square f (trace Λ Y L d)
  have h₄ := tensor_square f (singleUnitIso Λ Y).hom
  have h₅ : tensorHom f (𝟙 _) ≫ (ρ_ K').hom = (ρ_ K).hom ≫ f := by
    simpa only [tensorHom_id] using rightUnitor_naturality f
  unfold counitComponent
  exact compose_square h₁ (compose_square h₂ (compose_square h₃ (compose_square h₄ h₅)))

-- Restrict the ambient paste before specializing any coefficient or line data.
private theorem restrictedUnit_exists (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (P : ObjectProperty (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (Q : ObjectProperty (DerivedCategory (Modules Λ Y)))
    (hF : ∀ M : P.FullSubcategory,
      Q ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M.obj))
    (hG : ∀ K : Q.FullSubcategory,
      P ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
        twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj K.obj))
    (hI : ∀ M : P.FullSubcategory, UnitInversionCondition Λ Y L e M.obj) :
    let F := Q.lift (P.ι ⋙ moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)) hF
    let G := P.lift (Q.ι ⋙ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))) hG
    ∃ η : 𝟭 _ ⟶ F ⋙ G, ∀ M : P.FullSubcategory,
      UnitComponentNormalized Λ Y L d e M.obj (η.app M).hom := by
  let F := Q.lift (P.ι ⋙ moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)) hF
  let G := P.lift (Q.ι ⋙ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
    twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))) hG
  let η : 𝟭 _ ⟶ F ⋙ G :=
    { app M := ObjectProperty.homMk (unitComponent Λ Y L d e M.obj (hI M).1 (hI M).2)
      naturality M N f := by
        apply ObjectProperty.hom_ext
        exact unitComponent_naturality Λ Y L d e f.hom (hI M) (hI N) }
  refine ⟨η, ?_⟩
  intro M
  exact ⟨(hI M).1, (hI M).2, HEq.rfl⟩

-- The inversion witnesses are proofs; their choices do not change the fixed formula.
private theorem unit_normalization_unique (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) {α : Type (u + 1)}
    (f g : α) (hf : UnitComponentNormalized Λ Y L d e M f)
    (hg : UnitComponentNormalized Λ Y L d e M g) : f = g := by
  obtain ⟨hb, hp, h⟩ := hf
  obtain ⟨hb', hp', h'⟩ := hg
  exact eq_of_heq (h.trans h'.symm)

private theorem counit_normalization_unique (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (K : DerivedCategory (Modules Λ Y)) {α : Type (u + 1)}
    (f g : α) (hf : CounitComponentNormalized Λ Y L d K f)
    (hg : CounitComponentNormalized Λ Y L d K g) : f = g := by
  obtain ⟨hp, h⟩ := hf
  obtain ⟨hp', h'⟩ := hg
  exact eq_of_heq (h.trans h'.symm)

-- Keeping the entire construction parametric also keeps kernel checking small.
private theorem restrictedUnitCounit_existsUnique (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (P : ObjectProperty (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (Q : ObjectProperty (DerivedCategory (Modules Λ Y)))
    (hF : ∀ M : P.FullSubcategory,
      Q ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M.obj))
    (hG : ∀ K : Q.FullSubcategory,
      P ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
        twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj K.obj))
    (hI : ∀ M : P.FullSubcategory, UnitInversionCondition Λ Y L e M.obj)
    (hJ : ∀ K : Q.FullSubcategory, CounitInversionCondition Λ Y L K.obj)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory)
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (hF_eq : F = Q.lift (P.ι ⋙ moduleObjectDerivedPushforward Λ
      (ProjectiveLine Y ↘ Y)) hF)
    (hG_eq : G = P.lift (Q.ι ⋙ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))) hG) :
    ∃! a : (𝟭 P.FullSubcategory ⟶ F ⋙ G) × (G ⋙ F ⟶ 𝟭 Q.FullSubcategory),
      (∀ M : P.FullSubcategory, UnitComponentNormalized Λ Y L d e M.obj (a.1.app M).hom) ∧
      (∀ K : Q.FullSubcategory, CounitComponentNormalized Λ Y L d K.obj (a.2.app K).hom) := by
  subst F
  subst G
  let F := Q.lift (P.ι ⋙ moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)) hF
  let G := P.lift (Q.ι ⋙ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
    twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))) hG
  obtain ⟨η, hη⟩ := restrictedUnit_exists Λ Y L d e P Q hF hG hI
  let ε : G ⋙ F ⟶ 𝟭 _ :=
    { app K := ObjectProperty.homMk (counitComponent Λ Y L d K.obj (hJ K))
      naturality K K' f := by
        apply ObjectProperty.hom_ext
        exact counitComponent_naturality Λ Y L d f.hom (hJ K) (hJ K') }
  have hε : ∀ K : Q.FullSubcategory,
      CounitComponentNormalized Λ Y L d K.obj (ε.app K).hom := by
    intro K
    exact ⟨hJ K, HEq.rfl⟩
  refine ⟨(η, ε), ⟨hη, hε⟩, ?_⟩
  intro a ha
  apply Prod.ext
  · apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    exact unit_normalization_unique Λ Y L d e M.obj _ _ (ha.1 M) (hη M)
  · apply NatTrans.ext
    funext K
    apply ObjectProperty.hom_ext
    exact counit_normalization_unique Λ Y L d K.obj _ _ (ha.2 K) (hε K)

/-- Exactness of a specified restriction, bundled before specializing its ambient categories.
This is only the existing shift-commutation structure and Mathlib triangulated-functor
predicate; no new notion of distinguished triangle or exactness is introduced.
Source: blueprint rational projective-line unit/counit, exact restricted functors
(blueprint: lem-sfb-projective-normalized-unit-counit-restriction). -/
def RestrictionExact
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsTriangulated] [Q.IsTriangulated]
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) : Prop :=
  ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated

/-- The canonical diagonal comparison is a natural isomorphism on the entire unbounded
category, and the fixed ambient formulas uniquely define the restricted unit/counit pair.
`F` and `G` name precisely the indicated full-subcategory lifts, as required by their
specified equalities. Normalization is heterogeneous equality to the fixed formulas.

Source: blueprint rational projective-line unit/counit proof, Well-definedness (1)--(3)
(blueprint: lem-sfb-projective-normalized-unit-counit-restriction).

Proof plan:
1. Apply `lem-sfb-noncommutative-ringed-open-closed` to the diagonal and complementary
open, transporting along the pulled-back coefficient identifications. Exact inverse images
and the open/closed short exact sequence detect zero cohomology in every integer degree.
By `lem-sf-exact-functor-derived-triangulated` and `sk-def-sfb-derived-categories` the
termwise functors descend to the unbounded derived categories. Apply detection to cones to
obtain joint conservativity there, with invertible derived closed counit.
2. Transpose the fixed `diagonalTensorMap` under the derived pullback/pushforward adjunction
of `sk-def-sfb-module-derived-pushpull`. The mate description in
`def-sfb-proetale-projection-exchange-maps` identifies its transpose with tensor-pullback,
the prescribed section comparison, the closed counit, and the coefficient unitor. All are
invertible, so its diagonal restriction is invertible.
3. Its complementary restriction has zero source and target, by open/closed vanishing
and the closed tensor structure of `sk-def-sfb-derived-tensor-hom`. Joint conservativity
makes the actual map invertible. Naturality follows from left-projection naturality
`lem-sfb-rational-p1-left-projection-naturality`, section naturality and unitor naturality.
4. The inverse of `pushSectionIso` from `def-sfb-projective-diagonal-composition` gives
the claimed pushforward-composition isomorphism. The same definition identifies the
supported degree-zero coefficient source with the derived closed pushforward of the unit.
5. Tensor the specified diagonal class from `def-sfb-diagonal-coefficient-category` and
apply the second pushforward. Follow by the inverses of the fixed twisted projection and
exchange, using `def-sfb-rational-p1-unit-inversion-condition`. This is exactly
`unitComponent` of `def-sfb-projective-ambient-unit-counit-composites`.
6. Tensor bifunctoriality, `lem-sfb-rational-p1-tensor-shift-naturality`, section naturality
and diagonal comparison naturality give naturality before these inverses. The exchange
is natural by its mate definition in `def-weil-pbc-ambient-ringed-exchange`. The twisted
projection is natural in the pushed variable by the unit/tensor-comparison/counit
construction of `def-sfb-proetale-rational-localizing-projection-helpers`, followed by
tensoring the specified line comparison. Invert these naturality squares and compose.
7. Use `def-sfb-rational-p1-counit-inversion-condition` to invert the fixed left projection.
Precede it by inverse tensor-shift and follow by identity tensor the specified trace,
the coefficient-unit identification and the right unitor. This is `counitComponent`.
Tensor-shift naturality, left-projection naturality, tensor bifunctoriality and unitor
naturality give its naturality square.
8. Preservation puts the endpoints in the full subcategories, so fullness lifts both
components and faithfulness proves naturality there. The endpoint functors are the given
exact lifts. Any other normalized pair is heterogeneously equal componentwise to the
same formulas; transitivity gives equality, and faithful inclusion plus natural
transformation extensionality gives equality of pairs. No triangle identities enter. -/
theorem projective_normalized_unit_counit_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) [IsClosedImmersion (diagonalImmersion Y)]
    (U : Scheme.{u}) (j : U ⟶ diagonalSurface Y) [IsOpenImmersion j] [QuasiCompact j]
    (hj : Set.range j.base = (Set.range (diagonalImmersion Y).base)ᶜ)
    [PreservesFiniteLimits (CondensedRing.upperStar Λ (diagonalImmersion Y))]
    [PreservesFiniteColimits (CondensedRing.upperStar Λ (diagonalImmersion Y))]
    [PreservesFiniteLimits (CondensedRing.upperStar Λ j)]
    [PreservesFiniteColimits (CondensedRing.upperStar Λ j)]
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (P : ObjectProperty (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (Q : ObjectProperty (DerivedCategory (Modules Λ Y)))
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]
    [P.IsTriangulated] [Q.IsTriangulated]
    (hF : ∀ M : P.FullSubcategory,
      Q ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M.obj))
    (hG : ∀ K : Q.FullSubcategory,
      P ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
        twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj K.obj))
    (F : P.FullSubcategory ⥤ Q.FullSubcategory)
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (hF_eq : F = Q.lift (P.ι ⋙ moduleObjectDerivedPushforward Λ
      (ProjectiveLine Y ↘ Y)) hF)
    (hG_eq : G = P.lift (Q.ι ⋙ moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))) hG)
    (hF_exact : RestrictionExact P Q F) (hG_exact : RestrictionExact Q P G)
    (hI : ∀ M : P.FullSubcategory, UnitInversionCondition Λ Y L e M.obj)
    (hJ : ∀ K : Q.FullSubcategory, CounitInversionCondition Λ Y L K.obj) :
    (∃ a : moduleObjectDerivedPullback Λ (firstProjection Y) ⋙
        tensorRight ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≅
        moduleObjectDerivedPushforward Λ (diagonalImmersion Y),
      ∀ M : DerivedCategory (Modules Λ (ProjectiveLine Y)),
        a.hom.app M = diagonalTensorMap Λ Y M) ∧
    Nonempty (moduleObjectDerivedPushforward Λ (diagonalImmersion Y) ⋙
      moduleObjectDerivedPushforward Λ (secondProjection Y) ≅
        𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y)))) ∧
    ∃! a : (𝟭 P.FullSubcategory ⟶ F ⋙ G) × (G ⋙ F ⟶ 𝟭 Q.FullSubcategory),
      (∀ M : P.FullSubcategory,
        UnitComponentNormalized Λ Y L d e M.obj (a.1.app M).hom) ∧
      (∀ K : Q.FullSubcategory,
        CounitComponentNormalized Λ Y L d K.obj (a.2.app K).hom) := by
  have _ := hj
  have _ := hF_exact
  have _ := hG_exact
  refine ⟨?_, ⟨(pushSectionIso Λ Y).symm⟩, ?_⟩
  · let a : moduleObjectDerivedPullback Λ (firstProjection Y) ⋙
        tensorRight ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
          (unit Λ (ProjectiveLine Y))) ≅
        moduleObjectDerivedPushforward Λ (diagonalImmersion Y) :=
      NatIso.ofComponents (fun M ↦ (diagonalTensorIso Λ Y M).symm) (by
        intro M N f
        simpa only [Functor.comp_map, tensorRight, Functor.flip_obj_map,
          curriedTensor_map_app, Iso.symm_hom, tensorHom_id] using
          inverse_iso_square (diagonalTensorIso Λ Y M) (diagonalTensorIso Λ Y N)
            (diagonalTensorIso_naturality Λ Y f))
    refine ⟨a, ?_⟩
    intro M
    have := diagonalTensorMap_isIso Λ Y M
    simp only [a, NatIso.ofComponents_hom_app, Iso.symm_hom, diagonalTensorIso,
      Iso.symm_inv, asIso_hom]
  · exact restrictedUnitCounit_existsUnique Λ Y L d e P Q hF hG hI hJ F G hF_eq hG_eq

end Naturality

end AlgebraicGeometry.ProEtale.RationalP1
