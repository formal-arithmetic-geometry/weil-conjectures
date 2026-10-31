/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import Mathlib.CategoryTheory.Pi.Basic
/-! # Cyclic sheet coordinates for constructible coefficient hearts

Source: Deligne, Weil II, (1.1.7), (1.1.10) and the following paragraph, pp. 150--152
(blueprint: def-zl-constant-extension-sheet-heart-data).

The clause packages below retain the actual finite, integral, rational and common-stage
categories. The cyclic fixed-pair category uses the existing IsoAlgebra construction.
All component maps are the canonical semilinear sheet maps, without a k-linearity hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uC uB vC vB
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

/-- Exact product equivalence and its standard-heart restriction, with the same arrows.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetEquivalence
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    {I : Type} (F : I → (C ⥤ B)) (HC : ObjectProperty C) (HB : ObjectProperty B)
    (SC : Bool → ℤ → ObjectProperty C) (SB : Bool → ℤ → ObjectProperty B) where
  equivalence : (Functor.pi' F).IsEquivalence
  standard : ∀ (b : Bool) (n : ℤ) (K : C),
    SC b n K ↔ ∀ i : I, SB b n ((F i).obj K)
  heart : HC.FullSubcategory ⥤ (I → HB.FullSubcategory)
  heart_fac : heart ⋙ Functor.pi (fun _ : I ↦ HB.ι) = HC.ι ⋙ Functor.pi' F
  heart_equivalence : heart.IsEquivalence
  heart_limits : PreservesFiniteLimits heart
  heart_colimits : PreservesFiniteColimits heart
  component_limits : ∀ i : I, PreservesFiniteLimits (heart ⋙ Pi.eval _ i)
  component_colimits : ∀ i : I, PreservesFiniteColimits (heart ⋙ Pi.eval _ i)

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The algebra splitting, with every embedding and its prescribed tensor evaluation.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def ZlSheetTensorSplitting : Prop :=
  letI := (D.extensionEmbedding m hm).toAlgebra
  ∃ e : ((D.extensionSubfield m hm) ⊗[D.k₀] D.k) ≃+*
      (((D.extensionSubfield m hm) →ₐ[D.k₀] D.k) → D.k),
    (∀ (t : D.extensionSubfield m hm) (b : D.k)
      (σ : (D.extensionSubfield m hm) →ₐ[D.k₀] D.k), e (t ⊗ₜ[D.k₀] b) σ = σ t * b) ∧
    Nat.card ((D.extensionSubfield m hm) →ₐ[D.k₀] D.k) = m

/-- Clopen sheet factors and the cyclic identities, on the chosen geometric fibres.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetGeometry where
  tensor : ZlSheetTensorSplitting D m hm
  opens : Fin m → (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left.Opens
  closed : ∀ i : Fin m, IsClosed (opens i : Set
    (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left)
  disjoint : Pairwise (fun i j : Fin m ↦ Disjoint (opens i) (opens j))
  cover : (⨆ i : Fin m, opens i) = ⊤
  coordinate : ∀ i : Fin m, (D.geometricFiber X₀).left ≅ (opens i).toScheme
  factor : ∀ i : Fin m, (coordinate i).hom ≫ (opens i).ι =
    constantExtensionCyclicSheet D m hm X₀ i
  successor : ∀ (i : Fin m) (h : i.val + 1 < m),
    constantExtensionCyclicSheet D m hm X₀ i ≫
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom =
      constantExtensionCyclicSheet D m hm X₀ ⟨i.val + 1, h⟩
  return_map : ∀ (i : Fin m), ¬ i.val + 1 < m →
    constantExtensionCyclicSheet D m hm X₀ i ≫
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom =
      localPositivePower (D.geometricFrobenius X₀).hom (m - 1) ≫
        constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩
  new_frobenius :
    ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom ≫ (constantExtensionFiberIso D m hm X₀).hom =
    (constantExtensionFiberIso D m hm X₀).hom ≫
      localPositivePower (D.geometricFrobenius X₀).hom (m - 1)

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The recorded common-stage pullback for any map between the two actual fibres.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetFiberPull
    {A₀ B₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType A₀.hom] [QuasiCompact A₀.hom]
    [LocallyOfFiniteType B₀.hom] [QuasiCompact B₀.hom]
    (f : (D.geometricFiber A₀).left ⟶ (D.geometricFiber B₀).left) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ f
    (sfWeilPrimeInvertible D l hl A₀) (sfWeilPrimeInvertible D l hl B₀)

/-- The corresponding integral-normalized compositor on the actual fibres.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetFiberComp
    {A₀ B₀ C₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType A₀.hom] [QuasiCompact A₀.hom]
    [LocallyOfFiniteType B₀.hom] [QuasiCompact B₀.hom]
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (f : (D.geometricFiber A₀).left ⟶ (D.geometricFiber B₀).left)
    (g : (D.geometricFiber B₀).left ⟶ (D.geometricFiber C₀).left) :
    zlSheetFiberPull D l hl Ω (f ≫ g) ≅
      zlSheetFiberPull D l hl Ω g ⋙ zlSheetFiberPull D l hl Ω f :=
  letI := sfWeilPrimeInvertible D l hl A₀
  letI := sfWeilPrimeInvertible D l hl B₀
  letI := sfWeilPrimeInvertible D l hl C₀
  zlPullComp l Ω f g

/-- The prescribed positive iterate comparison, avoiding a choice of pullback unit.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetPositiveComparison (n : ℕ) :
    zlSheetFiberPull D l hl Ω
        (localPositivePower (D.geometricFrobenius X₀).hom n) ≅
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).iterate (n + 1) :=
  match n with
  | 0 => Iso.refl _
  | n + 1 =>
    zlSheetFiberComp D l hl Ω
      (localPositivePower (D.geometricFrobenius X₀).hom n)
      (D.geometricFrobenius X₀).hom ≪≫
    isoWhiskerLeft (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (zlSheetPositiveComparison n) ≪≫
    eqToIso (((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).iterate_add 1 (n + 1)).symm)
      ≪≫ eqToIso (congrArg
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).iterate (Nat.add_comm 1 (n + 1)))

/-- The cyclic endofunctor: successor evaluation, with P to the mth power at the return.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetCycle
    {C : Type uC} [Category.{vC} C] (P : C ⥤ C) : (Fin m → C) ⥤ (Fin m → C) :=
  Functor.pi' (fun i : Fin m ↦
    if h : i.val + 1 < m then Pi.eval _ ⟨i.val + 1, h⟩
    else Pi.eval _ ⟨0, hm⟩ ⋙ P.iterate m)

/-- Pullback on all sheets, retaining the actual morphisms.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetRestriction :=
  Functor.pi' (fun i : Fin m ↦ zlSheetFiberPull D l hl Ω
    (constantExtensionCyclicSheet D m hm X₀ i))

/-- The canonical successor comparison from the specified compositor and sheet equality.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetSuccessorComparison (G : ZlSheetGeometry D m hm X₀)
    (i : Fin m) (h : i.val + 1 < m) :
    zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ ⟨i.val + 1, h⟩) ≅
      sfCommonStageWeilFrobeniusPullback D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω ⋙
        zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i) :=
  (eqToIso (congrArg (zlSheetFiberPull D l hl Ω) (G.successor i h))).symm ≪≫
    zlSheetFiberComp D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i)
      (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom

/-- The return comparison retains the same positive iterated compositor.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetReturnComparison (G : ZlSheetGeometry D m hm X₀)
    (i : Fin m) (h : ¬ i.val + 1 < m) :
    zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩) ⋙
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).iterate m ≅
      sfCommonStageWeilFrobeniusPullback D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω ⋙
        zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i) :=
  isoWhiskerLeft
    (zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩))
    (eqToIso (congrArg (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).iterate
      (Nat.sub_add_cancel hm)).symm ≪≫ (zlSheetPositiveComparison D X₀ l hl Ω (m - 1)).symm)
    ≪≫ (zlSheetFiberComp D l hl Ω
      (localPositivePower (D.geometricFrobenius X₀).hom (m - 1))
      (constantExtensionCyclicSheet D m hm X₀ ⟨0, hm⟩)).symm ≪≫
    (eqToIso (congrArg (zlSheetFiberPull D l hl Ω) (G.return_map i h))).symm ≪≫
    zlSheetFiberComp D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i)
      (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom

/-- The componentwise heart condition on cyclic fixed pairs, with original Hom sets.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetCycleHeartProperty : ObjectProperty
    (IsoAlgebra (zlSheetCycle m hm
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω))) :=
  fun A ↦ ∀ i : Fin m, sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
    (A.carrier i)

/-- The full Weil-coordinate equivalence, pinned by the normalized successor and return maps.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetWeilCoordinates (G : ZlSheetGeometry D m hm X₀) where
  comparison : zlSheetRestriction D m hm X₀ l hl Ω ⋙
      zlSheetCycle m hm (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) ≅
    sfCommonStageWeilFrobeniusPullback D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω ⋙
        zlSheetRestriction D m hm X₀ l hl Ω
  successor_normalization : ∀ (N : generalAlgebraicallyClosedConstructibleCategory l Ω
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left)
      (i : Fin m) (h : i.val + 1 < m),
    HEq (comparison.hom.app N i)
      ((zlSheetSuccessorComparison D m hm X₀ l hl Ω G i h).hom.app N)
  return_normalization : ∀ (N : generalAlgebraicallyClosedConstructibleCategory l Ω
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left)
      (i : Fin m) (h : ¬ i.val + 1 < m),
    HEq (comparison.hom.app N i)
      ((zlSheetReturnComparison D m hm X₀ l hl Ω G i h).hom.app N)
  equivalence : sfCommonStageWeilSheaf D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω ≌
        (zlSheetCycleHeartProperty D m hm X₀ l hl Ω).FullSubcategory
  identification :
    equivalence.functor ⋙ (zlSheetCycleHeartProperty D m hm X₀ l hl Ω).ι ≅
      ((sfCommonStageHeartProperty l
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left Ω).inverseImage
          (sfCommonStageWeilForget D l hl (constantExtensionOriginalModel D m hm X₀) Ω)).ι ⋙
        IsoAlgebra.mapOfNatIso comparison
  exact_limits : PreservesFiniteLimits equivalence.functor
  exact_colimits : PreservesFiniteColimits equivalence.functor

section CoefficientStages
variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (h : Fin m → (X ⟶ Y))
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- All finite coefficient clauses on the intrinsic bounded constructible full subcategories.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetFiniteStage (n : ℕ) where
  pull : ∀ _i : Fin m,
    (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).FullSubcategory ⥤
      (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_pos n) X).FullSubcategory
  pull_fac : ∀ i : Fin m, pull i ⋙
      (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι =
    (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ⋙
      finiteDerivedPullback l E n (h i)
  clauses : ZlSheetEquivalence pull
    (fun K ↦ K.obj.IsLE 0 ∧ K.obj.IsGE 0)
    (fun K ↦ K.obj.IsLE 0 ∧ K.obj.IsGE 0)
    (fun b q K ↦ if b then K.obj.IsLE q else K.obj.IsGE q)
    (fun b q K ↦ if b then K.obj.IsLE q else K.obj.IsGE q)
  cohomology : ∀ (i : Fin m) (q : ℤ),
    (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ⋙
        constructibleTruncationCohomology DerivedCategory.TStructure.t q ⋙
          finiteDerivedPullback l E n (h i) ≅
      pull i ⋙
        (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
          constructibleTruncationCohomology DerivedCategory.TStructure.t q

/-- Integral and rational sheet equivalences, with reduction and cohomology comparisons.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetCoefficientStage where
  finite : ∀ n : ℕ, ZlSheetFiniteStage m l E h n
  integral : ZlSheetEquivalence (fun i ↦ constructibleIntegralPullback l E (h i))
    (sfIntegralStandardClass l E Y true 0 ⊓ sfIntegralStandardClass l E Y false 0)
    (sfIntegralStandardClass l E X true 0 ⊓ sfIntegralStandardClass l E X false 0)
    (sfIntegralStandardClass l E Y) (sfIntegralStandardClass l E X)
  rational : ZlSheetEquivalence (fun i ↦ rationalDerivedPullback l E (h i))
    (sfRationalHeartProperty l E Y) (sfRationalHeartProperty l E X)
    (sfRationalStandardClass l E Y) (sfRationalStandardClass l E X)
  integral_cohomology : ∀ (i : Fin m) (q : ℤ),
    (sfIntegralConstructible l E Y).ι ⋙
        constructibleTruncationCohomology DerivedCategory.TStructure.t q ⋙
          integralDerivedPullback l E (h i) ≅
      constructibleIntegralPullback l E (h i) ⋙ (sfIntegralConstructible l E X).ι ⋙
        constructibleTruncationCohomology DerivedCategory.TStructure.t q
  reduction : ∀ (i : Fin m) (n : ℕ),
    (sfIntegralConstructible l E Y).ι ⋙ scalarReductionDerivedExtension l E Y n ⋙
        finiteDerivedPullback l E n (h i) ≅
      constructibleIntegralPullback l E (h i) ⋙ (sfIntegralConstructible l E X).ι ⋙
        scalarReductionDerivedExtension l E X n
  quotient_reduction : ∀ (i : Fin m) (a b : ℕ) (hab : b ≤ a),
    coefficientFiniteQuotientDerived l E Y hab ⋙ finiteDerivedPullback l E b (h i) ≅
      finiteDerivedPullback l E a (h i) ⋙ coefficientFiniteQuotientDerived l E X hab
  rationalization : ∀ i : Fin m,
    constructibleIntegralPullback l E (h i) ⋙ sfRationalConstructibleLocalization l E X ≅
      sfRationalConstructibleLocalization l E Y ⋙ rationalDerivedPullback l E (h i)

/-- Scalar compatibility keeps the published integral comparison, including identity extensions.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetScalarCompatibility
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) where
  integral : ∀ i : Fin m,
    constructibleIntegralPullback l E (h i) ⋙
        sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ≅
      sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ⋙
        constructibleIntegralPullback l L (h i)
  integral_normalization : ∀ (i : Fin m) (K : sfIntegralConstructibleCategory l E Y),
    (integral i).app K = integralPullbackScalarComparison l E L ι (h i) K
  rational : ∀ i : Fin m,
    rationalDerivedPullback l E (h i) ⋙
        sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        rationalDerivedPullback l L (h i)
  rational_normalization : ∀ i : Fin m,
    rational i = rationalPullbackScalarComparison l E L ι (h i)

end CoefficientStages

/-- The actual standard t-structure on a geometric fibre, with inherited base data.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetStandard (A₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType A₀.hom] [QuasiCompact A₀.hom] :=
  letI : (D.geometricFiber A₀).left.Over (Spec (.of D.k)) := ⟨(D.geometricFiber A₀).hom⟩
  letI : LocallyOfFiniteType ((D.geometricFiber A₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd A₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact ((D.geometricFiber A₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd A₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  sfCommonStageStandardTStructure l (D.geometricFiber A₀).left Ω D hl

/-- The rational standard t-structure on the same geometric fibre.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def zlSheetRationalStandard (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (A₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType A₀.hom] [QuasiCompact A₀.hom] :=
  letI : (D.geometricFiber A₀).left.Over (Spec (.of D.k)) := ⟨(D.geometricFiber A₀).hom⟩
  letI : LocallyOfFiniteType ((D.geometricFiber A₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd A₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact ((D.geometricFiber A₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd A₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  sfRationalStandardTStructure l E (D.geometricFiber A₀).left D hl

/-- Restriction of an actual derived functor to full hearts, with exactness.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetHeartMap
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (F : C ⥤ B) (HC : ObjectProperty C) (HB : ObjectProperty B) where
  heart : HC.FullSubcategory ⥤ HB.FullSubcategory
  factor : heart ⋙ HB.ι = HC.ι ⋙ F
  limits : PreservesFiniteLimits heart
  colimits : PreservesFiniteColimits heart

/-- Coefficient-stage equivalences for these canonical sheets, with inherited residue units.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
def ZlSheetCoefficientClauses : Prop :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
    Nonempty (ZlSheetCoefficientStage m l E (constantExtensionCyclicSheet D m hm X₀))) ∧
  (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L), Nonempty
      (ZlSheetScalarCompatibility m l E (constantExtensionCyclicSheet D m hm X₀) L ι)) ∧
  (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : Fin m) (q : ℤ), Nonempty
      (constructibleTruncationCohomology
          (zlSheetRationalStandard D l hl E (constantExtensionOriginalModel D m hm X₀)) q ⋙
        rationalDerivedPullback l E (constantExtensionCyclicSheet D m hm X₀ i) ≅
      rationalDerivedPullback l E (constantExtensionCyclicSheet D m hm X₀ i) ⋙
        constructibleTruncationCohomology (zlSheetRationalStandard D l hl E X₀) q))

/-- The common-stage product equivalence, cohomology and exact semilinear coordinate factors.
Source: Deligne, Weil II, pp. 150--152, geometric splitting and coefficient enhancement
(blueprint: def-zl-constant-extension-sheet-heart-data). -/
structure ZlSheetCommonClauses (G : ZlSheetGeometry D m hm X₀) where
  product : ZlSheetEquivalence
    (fun i : Fin m ↦ zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i))
    (sfCommonStageHeartProperty l
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left Ω)
    (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω)
    (sfCommonStageStandardClass l
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left Ω)
    (sfCommonStageStandardClass l (D.geometricFiber X₀).left Ω)
  cohomology : ∀ (i : Fin m) (q : ℤ),
    constructibleTruncationCohomology
        (zlSheetStandard D l hl Ω (constantExtensionOriginalModel D m hm X₀)) q ⋙
      zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i) ≅
    zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i) ⋙
      constructibleTruncationCohomology (zlSheetStandard D l hl Ω X₀) q
  stage : ∀ (i : Fin m) (L : AlgebraicallyClosedCoefficients.Index l Ω),
    GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙
        zlSheetFiberPull D l hl Ω (constantExtensionCyclicSheet D m hm X₀ i) ≅
      @rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        _ _ _ _ _ (constantExtensionCyclicSheet D m hm X₀ i)
        (sfWeilPrimeInvertible D l hl X₀)
        (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion L
  stage_normalization : ∀ (i : Fin m) (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left L),
    HEq ((stage i L).hom.app K)
      (𝟙 (@commonStagePullbackObject l _ Ω _ _ _ _ _
        (constantExtensionCyclicSheet D m hm X₀ i)
        (sfWeilPrimeInvertible D l hl X₀)
        (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)))
  frobenius_equivalence : (zlHeartFrobenius D l hl Ω X₀).IsEquivalence
  frobenius_limits : PreservesFiniteLimits (zlHeartFrobenius D l hl Ω X₀)
  frobenius_colimits : PreservesFiniteColimits (zlHeartFrobenius D l hl Ω X₀)
  coordinate_factors : ∀ i : Fin m,
    ∃ units : ∀ z : (G.opens i).toScheme, Invertible (l : (G.opens i).toScheme.residueField z),
      (fun [iu : ∀ z : (G.opens i).toScheme,
          Invertible (l : (G.opens i).toScheme.residueField z)] ↦
        (fun [ix : ∀ x : (D.geometricFiber X₀).left,
            Invertible (l : (D.geometricFiber X₀).left.residueField x)]
          [iy : ∀ y : (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left,
            Invertible (l :
              (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left.residueField y)] ↦
          ∃ (r : ZlSheetHeartMap
              (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (G.coordinate i).hom ix iu)
              (sfCommonStageHeartProperty l (G.opens i).toScheme Ω)
              (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω))
            (j : ZlSheetHeartMap (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (G.opens i).ι iu iy)
              (sfCommonStageHeartProperty l
                (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left Ω)
              (sfCommonStageHeartProperty l (G.opens i).toScheme Ω)),
            r.heart.IsEquivalence ∧
            (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
              [FiniteDimensional (Padic l) E],
              Nonempty (@ZlSheetCoefficientStage 1 l _ E _ _ _ _ _
                (fun _ : Fin 1 ↦ (G.coordinate i).hom) ix iu)) ∧
            Nonempty (product.heart ⋙ Pi.eval _ i ≅ j.heart ⋙ r.heart) ∧
            (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (G.coordinate i).hom ix iu).IsEquivalence)
          (ix := sfWeilPrimeInvertible D l hl X₀)
          (iy := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)))
        (iu := units)

end WeilConjectures
