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
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

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
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ExceptionalCoefficients

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar extension and open extension by zero are left adjoint to canonically
identified right adjoints; uniqueness gives the identity/zero comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def openIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).comp
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm

/-- The canonical compact-support coefficient arrow, on a fixed compactification: the
recorded proper coefficient mate `scalarMate` at the open extension, followed by
proper direct image of the open comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def compactSupportMap {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) :=
  (scalarMate φ c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((openIso φ c.i).hom.app M)

/-- Inverse of the canonical comparison on its isomorphism domain, extended by zero.
This extension only makes the term total; every theorem use is on the domain where
b is an isomorphism. Source: Stacks 0GL6
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def comparisonInverse {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) ⟶
      (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) :=
  open Classical in
  if h : IsIso (compactSupportMap φ c M) then
    @inv _ _ _ _ (compactSupportMap φ c M) h
  else 0

/-- A total extension of the counit-transpose construction; its zero fallback is
irrelevant on the stated domain, where the theorem proves invertibility of b.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def mateMap [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).obj ((scalarExtension φ Y).obj K) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _
    (comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K))

/-- The ordinary extension has its actual scalar-restriction adjunction.
Source: Stacks 06YY (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryIsLeftAdjoint (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint

/-- The ordinary tensorator is the sheafified scalar balancing map.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryOplax (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- Representative normalization for a scalar tensor comparison, with monoidal data
kept shared in both categories. Source: Stacks 07A4
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) : Prop :=
  ∀ P Q : CochainComplex C ℤ,
    δ.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) ≫
        (rep P ⊗ₘ rep Q) ≫ Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      E.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ rep (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

/-- Small-etale specialization of the shared tensor normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev TensorNormalization (T : Scheme.{u}) :=
  TensorNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

/-- The canonical scalar tensor isomorphism is determined by ordinary balancing.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: on flat-term K-flat pairs the counits and the localization tensorators
are invertible. Ordinary balancing therefore defines δ by the displayed equation.
It commutes with resolutions and differentials. Localize in both variables to obtain
a natural isomorphism. Every pair admits such resolutions, proving uniqueness;
naturality with respect to a resolution proves the equation for all complexes. -/
theorem tensorIso_existsUnique (T : Scheme.{u}) :
    ∃! δ, TensorNormalization φ T δ := by
  sorry

/-- The same normalized tensor comparison, expressed using the site's tensor functor.
The heterogeneous equality asserts equality of the very same natural isomorphism,
including its endpoints, rather than choosing an unrelated comparison.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: unfold derivedTensor, which is curriedTensor of the canonical derived
monoidal structure. The normalized isomorphism from tensorIso_existsUnique
therefore has exactly this type. Reflexive heterogeneous equality supplies the
witness, and heterogeneous equality to that fixed witness implies uniqueness.
Keeping the transport opaque prevents expansion of the full monoidal structure. -/
theorem siteTensorIso_existsUnique (T : Scheme.{u}) :
    ∃! e : Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙
        scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T),
      HEq e (tensorIso_existsUnique φ T).choose := by
  sorry

/-- The site's tensor comparison, uniquely equal to the representative-normalized one.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorIso (T : Scheme.{u}) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙ scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T) :=
  (siteTensorIso_existsUnique φ T).choose

/-- Unit normalization using shared monoidal data for the ordinary scalar functor.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def UnitNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    e.hom ≫ Functor.LaxMonoidal.ε _root_.DerivedCategory.Q

/-- Specialization of scalar-unit normalization to the ordinary small-etale site.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev UnitNormalization (T : Scheme.{u}) :=
  UnitNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

/-- The scalar unit comparison is uniquely normalized by multiplication B tensor_A A -> B.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the unit complex is flat and K-flat. Its derived counit, the localization
unit comparison and ordinary scalar unit are invertible. Solve the normalization
equation for e; cancellation gives uniqueness. -/
theorem unitIso_existsUnique (T : Scheme.{u}) :
    ∃! e, UnitNormalization φ T e := by
  sorry

/-- Canonical scalar unit identification, selected by its unique normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def unitIso (T : Scheme.{u}) :
    (scalarExtension φ T).obj (𝟙_ (DerivedCategoryModule A T)) ≅
      𝟙_ (DerivedCategoryModule B T) :=
  (unitIso_existsUnique φ T).choose

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
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension (FiniteReduction.quotient l hmr) c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r))
      c.i).mapDerivedCategory.obj M)
  unfold compactSupportMap
  infer_instance

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
  (tensorIso φ X).hom.app
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K,
      dualizingComplex (ModuleCat.{u + 1} A) f) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
      ((scalarPullbackIso φ f).inv.app K)).app
        ((scalarExtension φ X).obj (dualizingComplex (ModuleCat.{u + 1} A) f)) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map
      (mateMap φ f (constantComplex A Y) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).map ((unitIso φ Y).hom))

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

end ExceptionalCoefficients

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
  sorry

end AlgebraicGeometry.Etale
