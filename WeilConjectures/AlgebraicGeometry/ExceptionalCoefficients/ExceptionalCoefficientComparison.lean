/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.FiniteReduction.System.FiniteReductionConstructibility
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarBaseChange
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.OrderedTensorCoefficientMate

/-! # Exceptional coefficient comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (2)--(3); Stacks 0GL6 and 0F7L
(blueprint: lem-pur-exceptional-coefficient-comparison).

All scalar functors are the published left adjoints to exact scalar restriction.
The scalar/pullback identification and the proper coefficient map are the recorded
`scalarPullbackIso` and `scalarMate` of lem-pur-etale-scalar-mate-projection.
The comparison for compact support is constructed from its open and proper parts.
The auxiliary tensor and pullback identifications are fixed by their ordinary
adjunctions and their computation on cochain representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u' v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ExceptionalCoefficients
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupport_isIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    IsIso (compactSupportMap φ c M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension φ c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  unfold compactSupportMap
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar transport of the dualizing complex, obtained by evaluating the exceptional
mate at the coefficient unit and then identifying that unit after extension of scalars.
Source: blueprint compatibilities (3)
(blueprint: def-pur-exceptional-coefficient-tensor-maps). -/
def dualizingScalarMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (scalarExtension φ X).obj (dualizingComplex A f) ⟶
      dualizingComplex B f :=
  mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
    (rightDerivedUpperShriek B f).map (unitIso φ Y).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem dualizingScalarMap_eq [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    dualizingScalarMap φ f = mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
      (rightDerivedUpperShriek B f).map (unitIso φ Y).hom := by
  rfl

attribute [irreducible] dualizingScalarMap

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar transport of the smooth tensor domain, using the canonical tensorator,
pullback balancing and c at the coefficient unit. Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorDomainMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex A f)) ⟶
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).obj (dualizingComplex B f) :=
  compactScalarProjectionTarget φ f K (dualizingComplex A f) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map
      (dualizingScalarMap φ f)

/-- The smooth tensor-map equation, including the actual scalar-domain transport.
Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorCompatibility [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ X).map
      (smoothTensorDualityMap A f
        (isIso_projectionMap_of_finite A f) K) ≫ mateMap φ f K =
    tensorDomainMap φ f K ≫
      smoothTensorDualityMap B f
        (isIso_projectionMap_of_finite B f) ((scalarExtension φ Y).obj K)

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The mixed square on the actual Cartesian pullback. Both paths have source
S_X' g'^* G_A K and target G'_B g^* S_Y K; beta is the recorded counit transpose.
Source: Stacks 0F7L and blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def BaseChangeCompatibility [Finite A] [Finite B] {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] (g : Y' ⟶ Y)
    (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ (pullback f g)).map (smoothExceptionalBaseChangeMap A f g K) ≫
      mateMap φ (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek B (pullback.snd f g)).map
        ((scalarPullbackIso φ g).inv.app K) =
    (scalarPullbackIso φ (pullback.fst f g)).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) (pullback.fst f g)).leftDerivedFunctor.map
        (mateMap φ f K) ≫
      smoothExceptionalBaseChangeMap B f g ((scalarExtension φ Y).obj K)

attribute [-instance] CategoryTheory.catToReflQuiver in
private def compactSupportIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  let (M : DerivedCategoryModule A X) : IsIso (compactSupportMap φ c M) :=
    compactSupport_isIso φ c M
  exact NatIso.ofComponents (fun M ↦ asIso (compactSupportMap φ c M))
    (fun h ↦ compactScalarMap_naturality φ c h)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupportIso_hom [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) : (compactSupportIso φ c).hom = compactScalarMap φ c := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupportIso_hom_app [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    (compactSupportIso φ c).hom.app M = compactSupportMap φ c M := by
  rfl

attribute [irreducible] compactSupportIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparisonInverse_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    comparisonInverse φ c M = (compactSupportIso φ c).inv.app M := by
  have := compactSupport_isIso φ c M
  simp only [comparisonInverse, dif_pos this]
  simpa only [compactSupportIso_hom_app] using
    (NatIso.inv_hom_app (compactSupportIso φ c) M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private def chosenCompactSupportIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ scalarExtension φ Y ≅
      scalarExtension φ X ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} B) f :=
  compactSupportIso φ (HasCompactification.compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem chosenCompactSupportIso_hom [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f] :
    (chosenCompactSupportIso φ f).hom = compactScalarChosenMap φ f := by
  exact compactSupportIso_hom φ (HasCompactification.compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparisonInverse_chosen_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) :
    comparisonInverse φ (HasCompactification.compactification f) M =
      (chosenCompactSupportIso φ f).inv.app M := by
  exact comparisonInverse_eq φ (HasCompactification.compactification f) M

attribute [irreducible] chosenCompactSupportIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateMap_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    mateMap φ f K =
      (mateEquiv (rightDerivedUpperShriekAdjunction A f)
        (rightDerivedUpperShriekAdjunction B f)
        (TwoSquare.mk _ _ _ _
          (compactSupportIso φ (HasCompactification.compactification f)).inv)).app K := by
  apply ((rightDerivedUpperShriekAdjunction
    B f).homEquiv _ _).symm.injective
  rw [mateMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit, mateEquiv_counit]
  rw [comparisonInverse_eq]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mate_cocycle_at
    {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Category C₃] [Category D₃]
    {P₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {P₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    {P₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₁ : P₁ ⊣ R₁) (a₂ : P₂ ⊣ R₂) (a₃ : P₃ ⊣ R₃)
    {S : C₁ ⥤ C₂} {T : D₁ ⥤ D₂} {U : C₂ ⥤ C₃} {V : D₂ ⥤ D₃}
    {W : C₁ ⥤ C₃} {Z : D₁ ⥤ D₃}
    (α : TwoSquare S P₁ P₂ T) (β : TwoSquare U P₂ P₃ V)
    (γ : TwoSquare W P₁ P₃ Z) (eX : S ⋙ U ≅ W) (eY : T ⋙ V ≅ Z)
    (K : D₁)
    (hc : P₃.map (eX.hom.app (R₁.obj K)) ≫ γ.app (R₁.obj K) =
      β.app (S.obj (R₁.obj K)) ≫ V.map (α.app (R₁.obj K)) ≫
        eY.hom.app (P₁.obj (R₁.obj K))) :
    U.map ((mateEquiv a₁ a₂ α).app K) ≫
        (mateEquiv a₂ a₃ β).app (T.obj K) ≫ R₃.map (eY.hom.app K) =
      eX.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).app K := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show P₃.map (R₃.map (eY.hom.app K)) ≫ a₃.counit.app _ =
    a₃.counit.app _ ≫ eY.hom.app K from a₃.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 => exact β.naturality _
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 => rw [← V.map_comp, mateEquiv_counit, V.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact eY.hom.naturality (a₁.counit.app K)
  slice_lhs 1 3 => exact hc.symm
  rw [mateEquiv_counit]
  exact Category.assoc _ _ _

private theorem compactScalarProjection_isIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    IsIso (compactScalarProjection R (HasCompactification.compactification f) K M) := by
  have := isIso_projectionMap_of_finite R f
  have : IsIso (((projectionMap (ModuleCat.{u + 1} R) f).app M).app K) := inferInstance
  dsimp only [projectionMap] at this
  unfold compactScalarProjection
  infer_instance

private theorem compactScalarProjection_naturality
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) {M N : DerivedCategoryModule R X} (h : M ⟶ N) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map h) ≫
        compactScalarProjection R (HasCompactification.compactification f) K N =
      compactScalarProjection R (HasCompactification.compactification f) K M ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj
            ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).map h) := by
  let P := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
    (HasCompactification.compactification f)
  let F := (upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor
  let sY := derivedTensorSymmetry (ModuleCat.{u + 1} R) Y
  let sX := derivedTensorSymmetry (ModuleCat.{u + 1} R) X
  have hY := (sY.hom.app K).naturality (P.map h)
  let p := projectionMapOfCompactification (ModuleCat.{u + 1} R)
    (HasCompactification.compactification f)
  have hP := NatTrans.congr_app (p.naturality h) K
  have hX := NatTrans.congr_app (sX.hom.naturality h) (F.obj K)
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app] at hY hX
  change ((derivedTensor (ModuleCat.{u + 1} R) Y).map (P.map h)).app K ≫
      (p.app N).app K =
    (p.app M).app K ≫
      P.map (((derivedTensor (ModuleCat.{u + 1} R) X).map h).app (F.obj K)) at hP
  dsimp only [rightDerivedLowerShriek]
  unfold compactScalarProjection
  simp only [Category.assoc]
  change _ ≫ (sY.hom.app K).app (P.obj N) ≫
      (p.app N).app K ≫
      P.map ((sX.hom.app N).app (F.obj K)) =
    (sY.hom.app K).app (P.obj M) ≫
      (p.app M).app K ≫
      P.map ((sX.hom.app M).app (F.obj K)) ≫ _
  rw [reassoc_of% hY, reassoc_of% hP, ← P.map_comp, ← P.map_comp]
  exact congrArg (fun z ↦ (sY.hom.app K).app (P.obj M) ≫
    (p.app M).app K ≫ P.map z) hX

private def orderedProjectionIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).obj M) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).obj M) := by
  let _ := compactScalarProjection_isIso R f K M
  exact asIso (compactScalarProjection R (HasCompactification.compactification f) K M)

private theorem orderedProjectionIso_hom
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    (orderedProjectionIso R f K M).hom =
      compactScalarProjection R (HasCompactification.compactification f) K M := by
  rfl

private theorem orderedProjectionIso_inv
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    (orderedProjectionIso R f K M).inv =
      @inv _ _ _ _ (compactScalarProjection R (HasCompactification.compactification f) K M)
        (compactScalarProjection_isIso R f K M) := by
  rfl

private theorem orderedProjectionIso_naturality
    (R : Type (u + 1)) [CommRing R] [Finite R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) {M N : DerivedCategoryModule R X} (h : M ⟶ N) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map h) ≫
        (orderedProjectionIso R f K N).hom =
      (orderedProjectionIso R f K M).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj
            ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).map h) := by
  simpa only [orderedProjectionIso_hom] using compactScalarProjection_naturality R f K h

private theorem ordered_projection_inverse
    {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {M N : C} {K L : D}
    (s : M ⟶ N) (s' : N ⟶ M) [IsIso s] (hs : s ≫ s' = 𝟙 M)
    (r : K ⟶ L) (r' : L ⟶ K) [IsIso r] (hr : r ≫ r' = 𝟙 K)
    (q : L ⟶ P.obj M) [IsIso q] :
    inv (r ≫ q ≫ P.map s) = P.map s' ≫ inv q ≫ r' := by
  rw [IsIso.inv_comp, IsIso.inv_comp, ← Functor.map_inv]
  rw [IsIso.inv_eq_of_hom_inv_id hs, IsIso.inv_eq_of_hom_inv_id hr]
  exact Category.assoc _ _ _

private theorem canonical_symmetry_hom
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (@BraidedCategory.braiding _ _ _ (smoothTensorCanonicalDerivedBraiding C) K M).hom := by
  rfl

private theorem smoothTensorDualityMap_expand
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (hPF : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    smoothTensorDualityMap Λ f hPF K =
      (rightDerivedUpperShriekAdjunction Λ f).homEquiv _ K
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).app
              (dualizingComplex Λ f)) ≫
          @inv _ _ _ _ (((projectionMap (ModuleCat.{u + 1} Λ) f).app (dualizingComplex Λ f)).app K)
            (by let _ := hPF; infer_instance) ≫
          ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj (dualizingComplex Λ f))).app K ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj K).map
            ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _)) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) S K).hom) := by
  simp only [smoothTensorDualityMap, derivedTensorSymmetry, canonical_symmetry_hom]

private theorem smoothTensorDualityMap_ordered_onSite
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (hPF : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f))
    (hX : ∀ M N, ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app M).app N ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app N).app M = 𝟙 _)
    (hY : ∀ M N, ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app M).app N ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app N).app M = 𝟙 _)
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    smoothTensorDualityMap Λ f hPF K =
      (rightDerivedUpperShriekAdjunction Λ f).homEquiv
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
            ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex Λ f)) K
        (@inv _ _ _ _
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app K).app
              ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj (dualizingComplex Λ f)) ≫
            ((projectionMap (ModuleCat.{u + 1} Λ) f).app (dualizingComplex Λ f)).app K ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
              (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app (dualizingComplex Λ f)).app
                ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)))
          (by let _ := hPF; infer_instance) ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj K).map
            ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _)) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) S K).hom) := by
  let P := rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
  let F := (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor
  let W := dualizingComplex Λ f
  let _ := hPF
  have hi : IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app W).app K) := inferInstance
  have hraw := ordered_projection_inverse P
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app W).app (F.obj K))
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app (F.obj K)).app W) (hX W (F.obj K))
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app K).app (P.obj W))
    (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) S).hom.app (P.obj W)).app K) (hY K (P.obj W))
    (((projectionMap (ModuleCat.{u + 1} Λ) f).app W).app K)
  have hc := congrArg (fun z ↦
    (rightDerivedUpperShriekAdjunction Λ f).homEquiv
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (F.obj K)).obj W) K
      (z ≫ ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj K).map
        ((rightDerivedUpperShriekAdjunction Λ f).counit.app (𝟙_ _)) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) S K).hom)) hraw.symm
  simpa only [smoothTensorDualityMap_expand, P, F, W, Category.assoc, Functor.flip_obj_obj] using hc

private theorem smoothTensorDualityMap_ordered
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) :
    smoothTensorDualityMap R f
        (isIso_projectionMap_of_finite R f) K =
      (rightDerivedUpperShriekAdjunction R f).homEquiv _ K
        ((orderedProjectionIso R f K (dualizingComplex R f)).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).map
            ((rightDerivedUpperShriekAdjunction R f).counit.app
              (𝟙_ _)) ≫ (derivedTensorRightUnitor (ModuleCat.{u + 1} R) Y K).hom) := by
  have h := smoothTensorDualityMap_ordered_onSite R f
    (isIso_projectionMap_of_finite R f)
    (derivedTensorSymmetry_involutive R X) (derivedTensorSymmetry_involutive R Y) K
  simpa only [orderedProjectionIso_inv, compactScalarProjection, projectionMap,
    rightDerivedLowerShriek,
    Functor.flip_obj_obj] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [irreducible] orderedProjectionIso

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateMap_counit [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map (mateMap φ f K) ≫
        (rightDerivedUpperShriekAdjunction B f).counit.app
          ((scalarExtension φ Y).obj K) =
      (chosenCompactSupportIso φ f).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K) := by
  rw [← comparisonInverse_chosen_eq]
  exact (rightDerivedUpperShriekAdjunction B f).homEquiv
    _ ((scalarExtension φ Y).obj K) |>.symm_apply_apply _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mate_unit_evaluation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P : C ⥤ D} {G : D ⥤ C} {P' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : P ⊣ G) (a' : P' ⊣ G') (S : C ⥤ C') (T : D ⥤ D')
    (b : P ⋙ T ≅ S ⋙ P') (c : ∀ K, S.obj (G.obj K) ⟶ G'.obj (T.obj K))
    (hc : ∀ K, P'.map (c K) ≫ a'.counit.app (T.obj K) =
      b.inv.app (G.obj K) ≫ T.map (a.counit.app K))
    {I : D} {I' : D'} (e : T.obj I ⟶ I') :
    b.hom.app (G.obj I) ≫ P'.map (c I ≫ G'.map e) ≫ a'.counit.app I' =
      T.map (a.counit.app I) ≫ e := by
  have hn := a'.counit.naturality e
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% (hc I)]
  exact Iso.hom_inv_id_app_assoc b _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_unit_counit [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] :
    (chosenCompactSupportIso φ f).hom.app
        (dualizingComplex A f) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (dualizingScalarMap φ f) ≫
      (rightDerivedUpperShriekAdjunction B f).counit.app
        (𝟙_ (DerivedCategoryModule B Y)) =
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ (DerivedCategoryModule A Y))) ≫ (unitIso φ Y).hom := by
  rw [dualizingScalarMap_eq]
  exact mate_unit_evaluation
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction B f)
    (scalarExtension φ X) (scalarExtension φ Y)
    (chosenCompactSupportIso φ f)
    (mateMap φ f) (mateMap_counit φ f) (unitIso φ Y).hom

private theorem scalarMate_square_of_counit_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P : C ⥤ D} {G : D ⥤ C} {P' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : P ⊣ G) (a' : P' ⊣ G') (S : C ⥤ C') (T : D ⥤ D')
    (b : P ⋙ T ≅ S ⋙ P') (c : ∀ K, S.obj (G.obj K) ⟶ G'.obj (T.obj K))
    (hc : ∀ K, P'.map (c K) ≫ a'.counit.app (T.obj K) =
      b.inv.app (G.obj K) ≫ T.map (a.counit.app K))
    (L : C) (L' : C') (K : D) (q : P.obj L ⟶ K) (q' : P'.obj L' ⟶ T.obj K)
    (d : S.obj L ⟶ L') (t : L ⟶ G.obj K) (t' : L' ⟶ G'.obj (T.obj K))
    (ht : t = a.homEquiv _ _ q) (ht' : t' = a'.homEquiv _ _ q')
    (hsq : b.inv.app L ≫ T.map q = P'.map d ≫ q') :
    S.map t ≫ c K = d ≫ t' := by
  have ht₀ : P.map t ≫ a.counit.app K = q := by
    change (a.homEquiv _ _).symm t = q
    rw [ht]
    exact (a.homEquiv _ _).symm_apply_apply q
  have ht₁ : P'.map t' ≫ a'.counit.app (T.obj K) = q' := by
    change (a'.homEquiv _ _).symm t' = q'
    rw [ht']
    exact (a'.homEquiv _ _).symm_apply_apply q'
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hc]
  have hn := b.inv.naturality_assoc t (T.map (a.counit.app K))
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← T.map_comp, ht₀, ht₁]
  exact hsq

private theorem scalar_tensor_right_unit_component (Y : Scheme.{u})
    (K : DerivedCategoryModule A Y) :
    (tensorIso φ Y).hom.app (K, (𝟙_ (DerivedCategoryModule A Y))) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) Y).obj
          ((scalarExtension φ Y).obj K)).map (unitIso φ Y).hom ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y
          ((scalarExtension φ Y).obj K)).hom =
      (scalarExtension φ Y).map
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  exact SiteScalarRightUnitLaw.component
    (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) Y
    (scalarExtension φ Y) (tensorIso φ Y) (unitIso φ Y) (tensorIso_right_unit φ Y) K

private theorem scalar_projection_component [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((orderedProjectionIso A f K M).hom) ≫
        (chosenCompactSupportIso φ f).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
          (compactScalarProjectionTarget φ f K M) =
      (tensorIso φ Y).hom.app
          (K, (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) Y).obj
          ((scalarExtension φ Y).obj K)).map ((chosenCompactSupportIso φ f).hom.app M) ≫
        (orderedProjectionIso B f ((scalarExtension φ Y).obj K)
          ((scalarExtension φ X).obj M)).hom := by
  simpa only [orderedProjectionIso_hom, chosenCompactSupportIso_hom,
    compactScalarChosenMap, rightDerivedLowerShriek] using
    (etaleCompactScalarCoherence φ f (HasCompactification.compactification f)).2.1 K M

private theorem tensorDomainMap_compact [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) :
    tensorDomainMap φ f K =
      compactScalarProjectionTarget φ f K (dualizingComplex A f) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).obj
          ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
            ((scalarExtension φ Y).obj K))).map
          (dualizingScalarMap φ f) := by
  rfl

private theorem tensorCompatibility [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (K : DerivedCategoryModule A Y) : TensorCompatibility φ f K := by
  unfold TensorCompatibility
  let FA := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let FB := (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
  let SX := scalarExtension φ X
  let SY := scalarExtension φ Y
  let πA := orderedProjectionIso A f
  let πB := orderedProjectionIso B f
  have hδ (K : DerivedCategoryModule A Y) {L L' : DerivedCategoryModule A Y} (h : L ⟶ L') :
      SY.map (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map h) ≫
        (tensorIso φ Y).hom.app (K, L') =
        (tensorIso φ Y).hom.app (K, L) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) Y).obj (SY.obj K)).map (SY.map h) := by
    have hn := (tensorIso φ Y).hom.naturality
      (show (K, L) ⟶ (K, L') from (𝟙 K, h))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at hn
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_obj,
      Functor.uncurry_obj_obj, Functor.prod_obj, NatTrans.id_app, Category.id_comp,
      SY] using hn
  let a := rightDerivedUpperShriekAdjunction A f
  let a' := rightDerivedUpperShriekAdjunction B f
  let PA := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let PB := rightDerivedLowerShriek (ModuleCat.{u + 1} B) f
  let L := ((derivedTensor (ModuleCat.{u + 1} A) X).obj (FA.obj K)).obj
    (dualizingComplex A f)
  let L' := ((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).obj
    (dualizingComplex B f)
  let q : PA.obj L ⟶ K :=
    (πA K (dualizingComplex A f)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        (a.counit.app (𝟙_ (DerivedCategoryModule A Y))) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom
  let q' : PB.obj L' ⟶ SY.obj K :=
    (πB (SY.obj K) (dualizingComplex B f)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Y).obj (SY.obj K)).map
        (a'.counit.app (𝟙_ (DerivedCategoryModule B Y))) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y (SY.obj K)).hom
  have hu := tensor_unit_counit φ f
  have hq := Adjunction.orderedTensor_coefficient_arrow_square
    PA PB SX SY
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K)
    ((derivedTensor (ModuleCat.{u + 1} B) Y).obj (SY.obj K))
    (chosenCompactSupportIso φ f)
    (dualizingComplex A f) L
    (dualizingComplex B f) L'
    (((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).obj
      (SX.obj (dualizingComplex A f)))
    (𝟙_ (DerivedCategoryModule A Y)) K (𝟙_ (DerivedCategoryModule B Y))
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y (SY.obj K)).hom
    (πA K _) (πB (SY.obj K) (SX.obj (dualizingComplex A f))).hom
    (πB (SY.obj K) _)
    (a.counit.app (𝟙_ (DerivedCategoryModule A Y)))
    (a'.counit.app (𝟙_ (DerivedCategoryModule B Y)))
    (dualizingScalarMap φ f)
    (compactScalarProjectionTarget φ f K (dualizingComplex A f))
    (((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).map
      (dualizingScalarMap φ f))
    ((tensorIso φ Y).hom.app (K, PA.obj (dualizingComplex A f)))
    ((tensorIso φ Y).hom.app (K, (𝟙_ (DerivedCategoryModule A Y)))) (unitIso φ Y).hom
    (orderedProjectionIso_naturality B f (SY.obj K) _) (hδ K _)
    (scalar_projection_component φ f K _)
    (scalar_tensor_right_unit_component φ Y K)
    hu (tensorDomainMap φ f K) (tensorDomainMap_compact φ f K)
  exact scalarMate_square_of_counit_square a a' SX SY (chosenCompactSupportIso φ f)
    (mateMap φ f) (mateMap_counit φ f) L L' K q q' (tensorDomainMap φ f K)
    (smoothTensorDualityMap A f
      (isIso_projectionMap_of_finite A f) K)
    (smoothTensorDualityMap B f
      (isIso_projectionMap_of_finite B f) (SY.obj K))
    (smoothTensorDualityMap_ordered A f K)
    (smoothTensorDualityMap_ordered B f (SY.obj K)) hq

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] tensorDomainMap in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compact_scalar_exchange_left [Finite A] [Finite B]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQM : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ X).obj M.obj) :
    (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        ((compactScalarChosenMap φ f).app M.obj) ≫
      (rightDerivedLowerShriekBaseChangeMap B sq).app ((scalarExtension φ X).obj M.obj) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((scalarPullbackIso φ h).hom.app M.obj) =
      (scalarPullbackIso φ g).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M.obj) ≫
      (scalarExtension φ Y').map ((rightDerivedLowerShriekBaseChangeMap A sq).app M.obj) ≫
      (compactScalarChosenMap φ f').app
        ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj M.obj) := by
  have hh := etaleCompactScalarBaseChange φ sq M hQM
  simp only [properOpenCoefficientPullbackIso, unboundedEtaleCompactSupportBaseChange,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] at hh
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.naturality
    ((compactScalarChosenMap φ f).app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hh hn ⊢
  erw [reassoc_of% hn] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  have hb := (compactScalarChosenMap φ f').naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hb
  simp only [Functor.map_comp, Category.assoc] at hh
  erw [hb] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc] at hh
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.app _)).1
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
    ((scalarExtension φ X').map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M.obj)))).1
  simpa only [Category.assoc, rightDerivedLowerShriek,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exactFaithful_reflects_plus
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    [Category D] [Abelian D] [HasDerivedCategory.{w} D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] (M : _root_.DerivedCategory C)
    (hM : _root_.DerivedCategory.TStructure.t.plus (U.mapDerivedCategory.obj M)) :
    _root_.DerivedCategory.TStructure.t.plus M := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, (_root_.DerivedCategory.isGE_iff _ n).mpr (fun i hi ↦ ?_)⟩
  have hz := (_root_.DerivedCategory.isGE_iff _ n).mp hn i hi
  have hz' : IsZero (U.obj ((_root_.DerivedCategory.homologyFunctor C i).obj M)) :=
    hz.of_iso ((U.mapDerivedCategoryHomologyFunctorIso i).app M)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply U.map_injective
  exact hz'.eq_of_src _ _

private theorem finiteTor_tensor_plus_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C))
    (hM : DerivedCategory.finiteTorAmplitude C T M)
    (N : Sheaf T.smallEtaleTopology C) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensor C T).obj M).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj N)) := by
  obtain ⟨a, b, htor⟩ := hM
  exact ⟨a, (htor N).1⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalar_extension_plus_of_finiteTor
    (T : Scheme.{u}) (M : DerivedCategoryModule A T)
    (hM : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T M) :
    _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ T).obj M) := by
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  have ht := finiteTor_tensor_plus_onSite (ModuleCat.{u + 1} A) T M hM
    (scalarCoefficientSheaf φ T)
  have hres : _root_.DerivedCategory.TStructure.t.plus
      (U.mapDerivedCategory.obj ((scalarExtension φ T).obj M)) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((scalarTensorIso φ T).app M).symm ht
  exact exactFaithful_reflects_plus U _ hres

attribute [-instance] CategoryTheory.catToReflQuiver in
end ExceptionalCoefficients

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.Etale
