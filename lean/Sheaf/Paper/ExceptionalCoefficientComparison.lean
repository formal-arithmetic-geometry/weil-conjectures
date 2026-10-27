/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.FiniteReductionConstructibility
public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Sheaf.Paper.EtaleCompactScalarCoherence
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import all Sheaf.Paper.ExceptionalCoefficientUnitCoherence
import Sheaf.Paper.EtaleCompactScalarBaseChange
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import Sheaf.CategoryTheory.OrderedTensorCoefficientMate
import Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive

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
/-- Invertibility of the specified b on its bounded constructible finite-Tor domain.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the proper map c.g has Noetherian source: it is of finite type over the
Noetherian target and is quasi-compact. Apply properFiniteCoefficientExtension
to the quotient homomorphism and the open extension of M; its first conclusion
says that the specified scalarMate component is invertible. The open comparison
is an isomorphism by construction, and proper direct image preserves it. The
definition of compactSupportMap is the composite of these two invertible maps.
This argument works on every input; no flatness of the quotient is used. -/
theorem compactSupportMap_isIso
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (_hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (_hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (M : DerivedCategoryModule (FiniteReduction.Coeff l r) X)
    (hM : DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X M) :
    IsIso (compactSupportMap (FiniteReduction.quotient l hmr) c M) := by
  have _ := hM
  exact compactSupport_isIso (FiniteReduction.quotient l hmr) c M

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Tensor associator for actual consecutive quotient maps, with scalar-adjunction
normalization. Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def quotientAssociator (T : Scheme.{u}) (l : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :=
  ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
    (FiniteReduction.quotient.{u} l hmr) (FiniteReduction.quotient l hnm)
    (FiniteReduction.quotient l (hnm.trans hmr))
    (RingHom.ext (fun x ↦
      congrArg (fun y : ZMod (l ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} l n))
        (DFunLike.congr_fun
          (Subsingleton.elim
            (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
            ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
              (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down)))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The quotient cocycle assumed for b, with both canonical associators displayed.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def CompactSupportCocycle (l : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : Prop :=
  ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m) (_hn : 1 ≤ n)
    (M : DerivedCategoryModule (FiniteReduction.Coeff l r) X),
    DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X M →
    (quotientAssociator Y l hmr hnm).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj M) ≫
      compactSupportMap (FiniteReduction.quotient l (hnm.trans hmr))
        (HasCompactification.compactification f) M =
    (scalarExtension (FiniteReduction.quotient l hnm) Y).map
        (compactSupportMap (FiniteReduction.quotient l hmr)
          (HasCompactification.compactification f) M) ≫
      compactSupportMap (FiniteReduction.quotient l hnm)
        (HasCompactification.compactification f)
        ((scalarExtension (FiniteReduction.quotient l hmr) X).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
        ((quotientAssociator X l hmr hnm).hom.app M)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar transport of the dualizing complex, obtained by evaluating the exceptional
mate at the coefficient unit and then identifying that unit after extension of scalars.
Source: blueprint compatibilities (3)
(blueprint: def-pur-exceptional-coefficient-tensor-maps). -/
def dualizingScalarMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (scalarExtension φ X).obj (dualizingComplex (ModuleCat.{u + 1} A) f) ⟶
      dualizingComplex (ModuleCat.{u + 1} B) f :=
  mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
    (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).map (unitIso φ Y).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem dualizingScalarMap_eq [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    dualizingScalarMap φ f = mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).map (unitIso φ Y).hom := by
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
          (dualizingComplex (ModuleCat.{u + 1} A) f)) ⟶
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).obj (dualizingComplex (ModuleCat.{u + 1} B) f) :=
  compactScalarProjectionTarget φ f K (dualizingComplex (ModuleCat.{u + 1} A) f) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map
      (dualizingScalarMap φ f)


attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The smooth tensor-map equation, including the actual scalar-domain transport.
Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorCompatibility [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ X).map
      (smoothTensorDualityMap (ModuleCat.{u + 1} A) f
        (isIso_projectionMap_of_finite A f) K) ≫ mateMap φ f K =
    tensorDomainMap φ f K ≫
      smoothTensorDualityMap (ModuleCat.{u + 1} B) f
        (isIso_projectionMap_of_finite B f) ((scalarExtension φ Y).obj K)

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
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) (pullback.snd f g)).map
        ((scalarPullbackIso φ g).inv.app K) =
    (scalarPullbackIso φ (pullback.fst f g)).inv.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
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
      (mateEquiv (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f)
        (TwoSquare.mk _ _ _ _
          (compactSupportIso φ (HasCompactification.compactification f)).inv)).app K := by
  apply ((rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} B) f).homEquiv _ _).symm.injective
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem orderedProjectionIso_hom
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    (orderedProjectionIso R f K M).hom =
      compactScalarProjection R (HasCompactification.compactification f) K M := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem orderedProjectionIso_inv
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    (orderedProjectionIso R f K M).inv =
      @inv _ _ _ _ (compactScalarProjection R (HasCompactification.compactification f) K M)
        (compactScalarProjection_isIso R f K M) := by
  rfl

attribute [irreducible] orderedProjectionIso

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem canonical_symmetry_hom
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (@BraidedCategory.braiding _ _ _ (smoothTensorCanonicalDerivedBraiding C) K M).hom := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem smoothTensorDualityMap_expand
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint]
    (hPF : IsIso (projectionMap A f))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    smoothTensorDualityMap A f hPF K =
      (rightDerivedUpperShriekAdjunction A f).homEquiv _ K
        ((rightDerivedLowerShriek A f).map
          (((derivedTensorSymmetry A X).hom.app
            ((upperStar A f).leftDerivedFunctor.obj K)).app (dualizingComplex A f)) ≫
          @inv _ _ _ _ (((projectionMap A f).app (dualizingComplex A f)).app K)
            (by let _ := hPF; infer_instance) ≫
          ((derivedTensorSymmetry A S).hom.app
            ((rightDerivedLowerShriek A f).obj (dualizingComplex A f))).app K ≫
          ((derivedTensor A S).obj K).map
            ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
          (derivedTensorRightUnitor A S K).hom) := by
  simp only [smoothTensorDualityMap, derivedTensorSymmetry, canonical_symmetry_hom]


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem smoothTensorDualityMap_ordered_onSite
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {FC : A → A → Type w} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [(rightDerivedLowerShriek A f).IsLeftAdjoint]
    (hPF : IsIso (projectionMap A f))
    (hX : ∀ M N, ((derivedTensorSymmetry A X).hom.app M).app N ≫
      ((derivedTensorSymmetry A X).hom.app N).app M = 𝟙 _)
    (hY : ∀ M N, ((derivedTensorSymmetry A S).hom.app M).app N ≫
      ((derivedTensorSymmetry A S).hom.app N).app M = 𝟙 _)
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    smoothTensorDualityMap A f hPF K =
      (rightDerivedUpperShriekAdjunction A f).homEquiv
        (((derivedTensor A X).obj ((upperStar A f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex A f)) K
        (@inv _ _ _ _
          (((derivedTensorSymmetry A S).hom.app K).app
              ((rightDerivedLowerShriek A f).obj (dualizingComplex A f)) ≫
            ((projectionMap A f).app (dualizingComplex A f)).app K ≫
            (rightDerivedLowerShriek A f).map
              (((derivedTensorSymmetry A X).hom.app (dualizingComplex A f)).app
                ((upperStar A f).leftDerivedFunctor.obj K)))
          (by let _ := hPF; infer_instance) ≫
          ((derivedTensor A S).obj K).map
            ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
          (derivedTensorRightUnitor A S K).hom) := by
  let P := rightDerivedLowerShriek A f
  let F := (upperStar A f).leftDerivedFunctor
  let W := dualizingComplex A f
  let _ := hPF
  have hi : IsIso (((projectionMap A f).app W).app K) := inferInstance
  have hraw := ordered_projection_inverse P
    (((derivedTensorSymmetry A X).hom.app W).app (F.obj K))
    (((derivedTensorSymmetry A X).hom.app (F.obj K)).app W) (hX W (F.obj K))
    (((derivedTensorSymmetry A S).hom.app K).app (P.obj W))
    (((derivedTensorSymmetry A S).hom.app (P.obj W)).app K) (hY K (P.obj W))
    (((projectionMap A f).app W).app K)
  have hc := congrArg (fun z ↦
    (rightDerivedUpperShriekAdjunction A f).homEquiv
      (((derivedTensor A X).obj (F.obj K)).obj W) K
      (z ≫ ((derivedTensor A S).obj K).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
        (derivedTensorRightUnitor A S K).hom)) hraw.symm
  simpa only [smoothTensorDualityMap_expand, P, F, W, Category.assoc, Functor.flip_obj_obj] using hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem smoothTensorDualityMap_ordered
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule R Y) :
    smoothTensorDualityMap (ModuleCat.{u + 1} R) f
        (isIso_projectionMap_of_finite R f) K =
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) f).homEquiv _ K
        ((orderedProjectionIso R f K (dualizingComplex (ModuleCat.{u + 1} R) f)).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).map
            ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) f).counit.app
              (𝟙_ _)) ≫ (derivedTensorRightUnitor (ModuleCat.{u + 1} R) Y K).hom) := by
  have h := smoothTensorDualityMap_ordered_onSite (ModuleCat.{u + 1} R) f
    (isIso_projectionMap_of_finite R f)
    (derivedTensorSymmetry_involutive R X) (derivedTensorSymmetry_involutive R Y) K
  simpa only [orderedProjectionIso_inv, compactScalarProjection, projectionMap,
    rightDerivedLowerShriek,
    Functor.flip_obj_obj] using h


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateMap_counit [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map (mateMap φ f K) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((scalarExtension φ Y).obj K) =
      (chosenCompactSupportIso φ f).inv.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K) := by
  rw [← comparisonInverse_chosen_eq]
  exact (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).homEquiv
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
        (dualizingComplex (ModuleCat.{u + 1} A) f) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (dualizingScalarMap φ f) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).counit.app
        (𝟙_ (DerivedCategoryModule B Y)) =
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app
        (𝟙_ (DerivedCategoryModule A Y))) ≫ (unitIso φ Y).hom := by
  rw [dualizingScalarMap_eq]
  exact mate_unit_evaluation
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f)
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


attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensorDomainMap_compact [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) :
    tensorDomainMap φ f K =
      compactScalarProjectionTarget φ f K (dualizingComplex (ModuleCat.{u + 1} A) f) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).obj
          ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
            ((scalarExtension φ Y).obj K))).map
          (dualizingScalarMap φ f) := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] tensorDomainMap in
attribute [-instance] CategoryTheory.catToReflQuiver in
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
  let a := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f
  let a' := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f
  let PA := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let PB := rightDerivedLowerShriek (ModuleCat.{u + 1} B) f
  let L := ((derivedTensor (ModuleCat.{u + 1} A) X).obj (FA.obj K)).obj
    (dualizingComplex (ModuleCat.{u + 1} A) f)
  let L' := ((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).obj
    (dualizingComplex (ModuleCat.{u + 1} B) f)
  let q : PA.obj L ⟶ K :=
    (πA K (dualizingComplex (ModuleCat.{u + 1} A) f)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        (a.counit.app (𝟙_ (DerivedCategoryModule A Y))) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom
  let q' : PB.obj L' ⟶ SY.obj K :=
    (πB (SY.obj K) (dualizingComplex (ModuleCat.{u + 1} B) f)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Y).obj (SY.obj K)).map
        (a'.counit.app (𝟙_ (DerivedCategoryModule B Y))) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y (SY.obj K)).hom
  have hu := tensor_unit_counit φ f
  have hq := Adjunction.orderedTensor_coefficient_arrow_square
    PA PB SX SY
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K)
    ((derivedTensor (ModuleCat.{u + 1} B) Y).obj (SY.obj K))
    (chosenCompactSupportIso φ f)
    (dualizingComplex (ModuleCat.{u + 1} A) f) L
    (dualizingComplex (ModuleCat.{u + 1} B) f) L'
    (((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).obj
      (SX.obj (dualizingComplex (ModuleCat.{u + 1} A) f)))
    (𝟙_ (DerivedCategoryModule A Y)) K (𝟙_ (DerivedCategoryModule B Y))
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} B) Y (SY.obj K)).hom
    (πA K _) (πB (SY.obj K) (SX.obj (dualizingComplex (ModuleCat.{u + 1} A) f))).hom
    (πB (SY.obj K) _)
    (a.counit.app (𝟙_ (DerivedCategoryModule A Y)))
    (a'.counit.app (𝟙_ (DerivedCategoryModule B Y)))
    (dualizingScalarMap φ f)
    (compactScalarProjectionTarget φ f K (dualizingComplex (ModuleCat.{u + 1} A) f))
    (((derivedTensor (ModuleCat.{u + 1} B) X).obj (FB.obj (SY.obj K))).map
      (dualizingScalarMap φ f))
    ((tensorIso φ Y).hom.app (K, PA.obj (dualizingComplex (ModuleCat.{u + 1} A) f)))
    ((tensorIso φ Y).hom.app (K, (𝟙_ (DerivedCategoryModule A Y)))) (unitIso φ Y).hom
    (orderedProjectionIso_naturality B f (SY.obj K) _) (hδ K _)
    (scalar_projection_component φ f K _)
    (scalar_tensor_right_unit_component φ Y K)
    hu (tensorDomainMap φ f K) (tensorDomainMap_compact φ f K)
  exact scalarMate_square_of_counit_square a a' SX SY (chosenCompactSupportIso φ f)
    (mateMap φ f) (mateMap_counit φ f) L L' K q q' (tensorDomainMap φ f K)
    (smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K)
    (smoothTensorDualityMap (ModuleCat.{u + 1} B) f
      (isIso_projectionMap_of_finite B f) (SY.obj K))
    (smoothTensorDualityMap_ordered A f K)
    (smoothTensorDualityMap_ordered B f (SY.obj K)) hq


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
private theorem baseChangeCompatibility [Finite A] [Finite B]
    {X Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (g : Y' ⟶ Y) (K : DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K))
    (hSM : _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ X).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K))) :
    BaseChangeCompatibility φ f g K := by
  let sq := IsPullback.of_hasPullback f g
  let f' := pullback.snd f g
  let h := pullback.fst f g
  have : IsNoetherian (pullback f g) := ⟨⟩
  let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let := isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let eA := asIso (rightDerivedLowerShriekBaseChangeMap A sq)
  let eB := asIso (rightDerivedLowerShriekBaseChangeMap B sq)
  let a := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f
  let b := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f'
  let ae := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f
  let be := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f'
  let αU := chosenCompactSupportIso φ f
  let αV := chosenCompactSupportIso φ f'
  have hfwd := compact_scalar_exchange_left φ sq ⟨_, hM⟩ ⟨⟨_, hSM⟩, rfl⟩
  rw [← chosenCompactSupportIso_hom φ f, ← chosenCompactSupportIso_hom φ f'] at hfwd
  have hcube : Adjunction.coefficientPullbackSquare eA.inv eB.inv αU αV
      (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) := by
    unfold Adjunction.coefficientPullbackSquare
    change (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app _) ≫ eB.hom.app _ ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
            ((scalarPullbackIso φ h).hom.app _) =
      (scalarPullbackIso φ g).hom.app _ ≫
        (scalarExtension φ Y').map (eA.hom.app _) ≫ αV.hom.app _ at hfwd
    have hi := IsIso.inv_eq_inv.mpr hfwd
    have hh := congrArg (fun z ↦ αV.hom.app
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K)) ≫
      z ≫ (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        (αU.hom.app ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K))) hi
    dsimp only [h, f'] at hh ⊢
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using hh.symm
  have hβ (R : Type (u + 1)) [CommRing R] [Finite R]
      [IsIso (rightDerivedLowerShriekBaseChangeMap R sq)]
      (L : DerivedCategoryModule R Y) :
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f').map
          (smoothExceptionalBaseChangeMap R f g L) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) f').counit.app
          ((upperStar (ModuleCat.{u + 1} R) g).leftDerivedFunctor.obj L) =
        inv ((rightDerivedLowerShriekBaseChangeMap R sq).app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} R) f).obj L)) ≫
        (upperStar (ModuleCat.{u + 1} R) g).leftDerivedFunctor.map
          ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) f).counit.app L) := by
    let := isIso_rightDerivedLowerShriekBaseChangeMap R sq
    exact ((rightDerivedUpperShriekAdjunction
      (ModuleCat.{u + 1} R) f').homEquiv _ _).symm_apply_apply _
  have hh := Adjunction.coefficient_exchange_of_counit_at a b ae be eA.inv eB.inv K
    (smoothExceptionalBaseChangeMap A f g K)
    (smoothExceptionalBaseChangeMap B f g ((scalarExtension φ Y).obj K))
    (by simpa only [a, b, eA, asIso, NatIso.isIso_inv_app] using hβ A K)
    (by simpa only [ae, be, eB, asIso, NatIso.isIso_inv_app]
      using hβ B ((scalarExtension φ Y).obj K))
    αU αV (scalarPullbackIso φ h).inv (scalarPullbackIso φ g).inv
    (mateMap φ f K)
    (mateMap φ f' ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (mateMap_counit φ f K) (mateMap_counit φ f' _) hcube
  exact hh.symm

end ExceptionalCoefficients


attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Domain preservation, invertibility, and the counit equation for exceptional coefficients.
Source: blueprint compatibility steps 1 and 4.
Proof: the domain is obtained from finite-reduction constructibility and smooth tensor
transport; the coefficient map is invertible by proper finite coefficient extension and
its counit equation follows by transposing the defining mate.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_domain_and_counit
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      IsIso (ExceptionalCoefficients.compactSupportMap (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        (rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).counit.app
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) =
      ExceptionalCoefficients.comparisonInverse (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        (scalarExtension (FiniteReduction.quotient l hmr) Y).map
          ((rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).counit.app K)) := by
  have _ := hb
  have hUnit : IsUnit (l : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hInvertible y
  have hCoeff : ((l ^ r : ℕ) : FiniteReduction.Coeff.{u} l r) = 0 := by
    apply ULift.ext
    apply ULift.ext
    exact ZMod.natCast_self (l ^ r)
  have : HasInvertibleExponent (FiniteReduction.Coeff.{u} l r) Y :=
    ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r, hCoeff, by
      simpa only [Nat.cast_pow] using hUnit.pow r⟩
  have hDomain (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y)
      (hK : DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K) :
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) := by
    obtain ⟨a, b, ht⟩ := hK.2
    have h := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
      (FiniteReduction.Coeff l r) f d a b
      ⟨⟨hK.1, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht⟩, ht⟩
    exact ⟨h.1.1, _, _, h.2⟩
  refine ⟨hDomain, ?_⟩
  intro K hK
  refine ⟨ExceptionalCoefficients.compactSupportMap_isIso l r m d hmr hm hInvertible
    (HasCompactification.compactification f) _ (hDomain K hK), ?_⟩
  unfold ExceptionalCoefficients.mateMap
  exact ((rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).homEquiv _ _).symm_apply_apply _


attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Naturality and the successive quotient cocycle for exceptional coefficient mates.
Source: blueprint compatibility steps 4--5.
Proof: transpose both sides under the exceptional adjunction; naturality of the mate
and the counit gives the first equality, and vertical mate pasting plus the assumed
compact-support cocycle gives the successive quotient equality.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_naturality_and_cocycle
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K K' : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K' →
      ∀ h : K ⟶ K',
        (scalarExtension (FiniteReduction.quotient l hmr) X).map
            ((rightDerivedUpperShriek
              (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).map h) ≫
          ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K' =
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K ≫
          (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).map h)) ∧
    (∀ (n : ℕ) (hnm : n ≤ m) (_hn : 1 ≤ n)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      (scalarExtension (FiniteReduction.quotient l hnm) X).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hnm) f
          ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
          ((ExceptionalCoefficients.quotientAssociator Y l hmr hnm).hom.app K) =
      (ExceptionalCoefficients.quotientAssociator X l hmr hnm).hom.app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l (hnm.trans hmr)) f K) := by
  constructor
  · intro K K' hK hK' h
    have _ := hK
    have _ := hK'
    simp only [ExceptionalCoefficients.mateMap_eq]
    exact (mateEquiv
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f)
      (TwoSquare.mk _ _ _ _ (ExceptionalCoefficients.compactSupportIso
        (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)).inv)).naturality h
  · intro n hnm hn K hK
    let c := HasCompactification.compactification f
    let S := scalarExtension (FiniteReduction.quotient l hmr) X
    let T := scalarExtension (FiniteReduction.quotient l hmr) Y
    let U := scalarExtension (FiniteReduction.quotient l hnm) X
    let V := scalarExtension (FiniteReduction.quotient l hnm) Y
    let W := scalarExtension (FiniteReduction.quotient l (hnm.trans hmr)) X
    let Z := scalarExtension (FiniteReduction.quotient l (hnm.trans hmr)) Y
    let P₁ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f
    let P₂ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f
    let P₃ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f
    let R₁ := rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f
    let i₁₂ := ExceptionalCoefficients.compactSupportIso (FiniteReduction.quotient l hmr) c
    let i₂₃ := ExceptionalCoefficients.compactSupportIso (FiniteReduction.quotient l hnm) c
    let i₁₃ := ExceptionalCoefficients.compactSupportIso
      (FiniteReduction.quotient l (hnm.trans hmr)) c
    let eX := ExceptionalCoefficients.quotientAssociator X l hmr hnm
    let eY := ExceptionalCoefficients.quotientAssociator Y l hmr hnm
    let M := R₁.obj K
    have hM := (exceptional_domain_and_counit l r m d hmr hm f hInvertible hb).1 K hK
    have hcomp := hb r m n hmr hnm hn M hM
    simp only [← ExceptionalCoefficients.compactSupportIso_hom_app] at hcomp
    change eY.hom.app (P₁.obj M) ≫ i₁₃.hom.app M =
      V.map (i₁₂.hom.app M) ≫ i₂₃.hom.app (S.obj M) ≫ P₃.map (eX.hom.app M) at hcomp
    have hc : P₃.map (eX.hom.app M) ≫ i₁₃.inv.app M =
        i₂₃.inv.app (S.obj M) ≫ V.map (i₁₂.inv.app M) ≫ eY.hom.app (P₁.obj M) := by
      apply (cancel_epi (V.map (i₁₂.hom.app M) ≫ i₂₃.hom.app (S.obj M))).1
      calc
        _ = (eY.hom.app (P₁.obj M) ≫ i₁₃.hom.app M) ≫ i₁₃.inv.app M := by
          rw [hcomp]
          simp only [Category.assoc]
        _ = eY.hom.app (P₁.obj M) := by
          simp only [Category.assoc, Iso.hom_inv_id_app]
          exact Category.comp_id _
        _ = _ := by
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
            ← V.map_comp_assoc, Iso.hom_inv_id_app, V.map_id, Category.id_comp]
    have h := ExceptionalCoefficients.mate_cocycle_at
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f)
      (TwoSquare.mk S P₁ P₂ T i₁₂.inv) (TwoSquare.mk U P₂ P₃ V i₂₃.inv)
      (TwoSquare.mk W P₁ P₃ Z i₁₃.inv) eX eY K hc
    simpa only [ExceptionalCoefficients.mateMap_eq] using h


attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Tensor and Cartesian base-change compatibilities for exceptional coefficient mates.
Source: blueprint compatibility steps 6--10.
Proof: express the smooth tensor map as the ordered projection counit transpose.
Compact-scalar projection coherence and the normalized right-unit law give its
coefficient square by the generic mate calculation. Paste the proper coefficient
exchange square with the open square proved from units, transfer to the chosen
compactifications on the bounded-below inputs, and apply coefficient exchange for
mates. Finite Tor amplitude supplies the scalar-extension lower bound.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_tensor_and_base_change
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.TensorCompatibility (FiniteReduction.quotient l hmr) f K) ∧
    (∀ (Y' : Scheme.{u}) [IsNoetherian Y'] (g : Y' ⟶ Y)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.BaseChangeCompatibility (FiniteReduction.quotient l hmr) f g K) := by
  constructor
  · intro K _hK
    exact ExceptionalCoefficients.tensorCompatibility (FiniteReduction.quotient l hmr) f K
  · intro Y' _ g K hK
    have hM := (exceptional_domain_and_counit l r m d hmr hm f hInvertible hb).1 K hK
    exact ExceptionalCoefficients.baseChangeCompatibility (FiniteReduction.quotient l hmr)
      f g K hM.1.1.1
      (ExceptionalCoefficients.scalar_extension_plus_of_finiteTor
        (FiniteReduction.quotient l hmr) X _ hM.2)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Exceptional comparison for consecutive finite quotient coefficients, including
its domain, counit identity, naturality, quotient cocycle, tensor and Cartesian
base-change compatibilities. Source: blueprint main-20261015, sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md (2)--(3);
Stacks 0GL6 and 0F7L (blueprint: lem-pur-exceptional-coefficient-comparison).

Proof:
1. Use the finite-ring origin equivalence and the Noetherian Tor comparison solely
to check domains. Finite reduction on bounded flat models preserves bounded
constructibility and finite Tor amplitude; quotient maps need not be flat.
2. Smooth tensor duality writes G_A K as f^*K tensor L[2d], with L locally free
of rank one. Pullback preserves flat K-flat models. Thus a model in [a,b]
becomes one in [a-2d,b-2d]; the flat-model Tor criterion applies.
3. Exact inverse image preserves constructible cohomology. Trivialize L on a
finite affine etale cover and descend constructibility along its qcqs surjection.
This proves the domain conclusion and hence invertibility of b at G_A K.
4. Transpose the defining mateMap under P_B adjoint G_B. Its transpose is
b inverse followed by scalar extension of the A-counit. Naturality of b and
of the counits makes the two transposes of the naturality equation equal.
5. For r -> m -> n transpose the two-step c under P_n adjoint G_n. Move c_r,m
past b_m,n by naturality, substitute both counit identities and apply the
assumed b cocycle. The normalized tensor associators give the displayed equation.
6. Proper projection and coefficient change commute by the ringed exchange/tensor
identity. For the open constituent both composites are the same balancing map on
the open and zero outside. Compose these statements on the compactification.
7. At M=omega, transpose the tensor equation. Substitute the c counit identity
at the coefficient unit. The inverse of Step 6's projection identity gives equal
transposes. The normalized unit comparison identifies S(A_Y) with B_Y.
8. In a Cartesian square, proper exchange and coefficient change are mates of
the same pulled-back proper counit. Pullback/scalar balancing agrees in both orders.
9. Open base change and coefficient change commute before deriving: on the
pulled-back open they are identity and balancing; off it both are zero. Combining
with Step 8 yields the mixed compact-support exchange square.
10. Transpose the two paths of BaseChangeCompatibility through P'_B adjoint G'_B.
Naturality and the defining identities of c and beta reduce them to the inverse
of Step 9's square followed by the same scalar/pullback A-counit. Injectivity
of the adjunction bijection proves equality. No inverse of c is used.
-/
theorem exceptional_coefficient_comparison
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      IsIso (ExceptionalCoefficients.compactSupportMap (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        (rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).counit.app
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) =
      ExceptionalCoefficients.comparisonInverse (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        (scalarExtension (FiniteReduction.quotient l hmr) Y).map
          ((rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).counit.app K)) ∧
    (∀ (K K' : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K' →
      ∀ h : K ⟶ K',
        (scalarExtension (FiniteReduction.quotient l hmr) X).map
            ((rightDerivedUpperShriek
              (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).map h) ≫
          ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K' =
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K ≫
          (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).map h)) ∧
    (∀ (n : ℕ) (hnm : n ≤ m) (_hn : 1 ≤ n)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      (scalarExtension (FiniteReduction.quotient l hnm) X).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hnm) f
          ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
          ((ExceptionalCoefficients.quotientAssociator Y l hmr hnm).hom.app K) =
      (ExceptionalCoefficients.quotientAssociator X l hmr hnm).hom.app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l (hnm.trans hmr)) f K) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.TensorCompatibility (FiniteReduction.quotient l hmr) f K) ∧
    (∀ (Y' : Scheme.{u}) [IsNoetherian Y'] (g : Y' ⟶ Y)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.BaseChangeCompatibility (FiniteReduction.quotient l hmr) f g K) := by
  obtain ⟨h₁, h₂⟩ := exceptional_domain_and_counit l r m d hmr hm f hInvertible hb
  obtain ⟨h₃, h₄⟩ := exceptional_naturality_and_cocycle l r m d hmr hm f hInvertible hb
  obtain ⟨h₅, h₆⟩ := exceptional_tensor_and_base_change l r m d hmr hm f hInvertible hb
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end AlgebraicGeometry.Etale

