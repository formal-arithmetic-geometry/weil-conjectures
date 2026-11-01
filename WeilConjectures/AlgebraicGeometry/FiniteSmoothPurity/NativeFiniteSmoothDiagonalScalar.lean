/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothDiagonalScalar
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCompactScalarBaseChange
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import Mathlib.Topology.Separation.DisjointCover
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons

/-! # Native scalar compatibility of the diagonal factor

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation
(blueprint: lem-sp-finite-smooth-diagonal-scalar).

The legacy clause is the imported `finiteSmoothDiagonalScalar`. The native clause is
stated inside the exceptional-adjunction package of `reductionExceptional_coefficient_extension`.
Its objects are intrinsic Dctf objects, its scalar functor is `scalarExtensionFunctor`,
and its exceptional comparison is the uniquely counit-characterized c of that package.

## Main definitions

* `NativeDiagonalExceptionalData` packages the cited native exceptional interfaces.
* `nativeDiagonalExchangeData` uses the flipped self-product and `compactChosenExchange`.
* `nativeFiniteSmoothDiagonalFactor` is the native inverse-exchange mate pulled along Delta.
* `nativeDiagonalDualizingScalar` specializes the package's c at the coefficient unit.

## Main statement

* `nativeFiniteSmoothDiagonalScalar` supplies these packages and their diagonal identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The native coefficient unit, using the recorded normalized site realization.
Only the coefficient unit is realized here; no exceptional functor is transported.
Source: compatibility proof (3), unit specialization
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalUnit (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :
    proEtaleDerivedCategory T R :=
  (reductionSite R T).obj (𝟙_ (DerivedCategoryModule (ULift.{u + 1, u} R) T))

/-- The normalized intrinsic pullback-unit identification from the recorded site comparison.
Source: compatibility proof (3), unit specialization
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalPullUnit (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleConstantRingDerivedPullback R f).obj (nativeDiagonalUnit R Y) ≅
      nativeDiagonalUnit R X :=
  (reductionSitePullbackIso R f).app _ ≪≫
    (reductionSite R X).mapIso
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) f)

/-- The normalized scalar-unit identification in the intrinsic coefficient categories.
Source: compatibility proof (3), coefficient unit normalization
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalScalarUnit {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtensionFunctor φ T).obj (nativeDiagonalUnit A T) ≅ nativeDiagonalUnit B T :=
  (reductionSiteScalarIso φ T).app _ ≪≫
    (reductionSite B T).mapIso
      (ExceptionalCoefficients.unitIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) T)

/-- The exact existential data of the native exceptional coefficient theorem, with its
unique c retained as data and characterized by the actual native counits. The realization
fields retain the cited theorem's chart normalization; omega below is GA/GB applied to
the unit, rather than an exceptional functor on the etale presentation.
Source: det-sp-reduction-exceptional, conclusion
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
structure NativeDiagonalExceptionalData
    (ell : ℕ) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cpt : Compactification f) (d : ℕ) where
  hFA : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor Y A ((reductionCompactSupport A cpt.i cpt.g).obj M.obj)
  hFB : ∀ M : spFiniteConstructibleTorCategory X B,
    spFiniteConstructibleTor Y B ((reductionCompactSupport B cpt.i cpt.g).obj M.obj)
  hSX : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj)
  hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
    spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)
  GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A
  GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B
  adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA
  adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB
  RA : ReductionExceptionalRealization A cpt.i cpt.g hFA GA adjA
  RB : ReductionExceptionalRealization B cpt.i cpt.g hFB GB adjB
  hb : ∀ K : spFiniteConstructibleTorCategory Y A,
    IsIso ((reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj)
  c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB
  counit : ∀ K : spFiniteConstructibleTorCategory Y A,
    (reductionCompactSupport B cpt.i cpt.g).map (c.app K).hom ≫
        (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj)
        (hb K) ≫ (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom
  invertible : ∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)
  chart : ReductionExceptionalChartEquation ell φ cpt.i cpt.g d hFA hFB hSX hSY
    GA GB adjA adjB RA RB c
  unique : ∀ c' : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB,
    ((∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCompactSupport B cpt.i cpt.g).map (c'.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj)
          (hb K) ≫ (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
      (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c'.app K)) ∧
      ReductionExceptionalChartEquation ell φ cpt.i cpt.g d hFA hFB hSX hSY
        GA GB adjA adjB RA RB c') → c' = c

/-- The exceptional image of the coefficient unit under the actual native right adjoint.
Source: compatibility proof (3), omega = f! R_Y
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalOmega (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}}
    (G : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R)
    (hY : spFiniteConstructibleTor Y R (nativeDiagonalUnit R Y)) :
    spFiniteConstructibleTorCategory X R :=
  G.obj ⟨nativeDiagonalUnit R Y, hY⟩

/-- The flipped self-product square: its upper map is p2 and its primed map is p1.
Source: compatibility proof (3), self-product square
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ChosenCartesianSquare (pullback.snd f f) (pullback.fst f f) f f where
  w := pullback.condition.symm
  isoPullback := pullbackSymmetry f f
  hom_fst := by simp
  hom_snd := by simp

/-- The actual pullback object and the chosen compact-support exchange of the cited
native interface. The selected p1 compactification is the argument c1, independent of
coefficients; compactChosenExchange includes its canonical common-refinement comparison.
Source: lem-pur-compact-scalar-base-change, flipped self-product specialization
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalExchangeData
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : pchar ≠ ell)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (cpt : Compactification f)
    (c1 : Compactification (pullback.fst f f))
    (R : Type u) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, ∀ x : R, (ell ^ n) • x = 0)
    (M : spFiniteConstructibleTorCategory X R) :
    Σ N : spFiniteConstructibleTorCategory (pullback f f) R,
      ((proEtaleConstantRingDerivedPullback R f).obj
          ((reductionCompactSupport R cpt.i cpt.g).obj M.obj) ⟶
        (reductionCompactSupport R c1.i c1.g).obj N.obj) := by
  letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  letI : QuasiCompact f := inferInstance
  letI : IsSeparated f := by rw [cpt.comm]; infer_instance
  letI : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]; infer_instance
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  letI : (pullback f f).Over (Spec (.of k)) :=
    ⟨pullback.fst f f ≫ X ↘ Spec (.of k)⟩
  letI : (pullback.fst f f).IsOver (Spec (.of k)) := ⟨rfl⟩
  letI : (pullback.snd f f).IsOver (Spec (.of k)) := ⟨by
    change pullback.snd f f ≫ X ↘ Spec (.of k) =
      pullback.fst f f ≫ X ↘ Spec (.of k)
    rw [← comp_over f (Spec (.of k)), ← Category.assoc, ← Category.assoc,
      pullback.condition]⟩
  letI : LocallyOfFiniteType ((pullback f f) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst f f ≫ X ↘ Spec (.of k)))
  letI : QuasiCompact ((pullback f f) ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (pullback.fst f f ≫ X ↘ Spec (.of k)))
  letI : IsSeparated ((pullback f f) ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (pullback.fst f f ≫ X ↘ Spec (.of k)))
  letI : cpt.Z.Over (Spec (.of k)) := ⟨cpt.g ≫ Y ↘ Spec (.of k)⟩
  letI : cpt.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  letI : cpt.i.IsOver (Spec (.of k)) := ⟨by
    change cpt.i ≫ (cpt.g ≫ Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    rw [← Category.assoc, ← cpt.comm, comp_over]⟩
  letI : LocallyOfFiniteType (cpt.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (cpt.g ≫ Y ↘ Spec (.of k)))
  letI : QuasiCompact (cpt.Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (cpt.g ≫ Y ↘ Spec (.of k)))
  letI : IsSeparated (cpt.Z ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (cpt.g ≫ Y ↘ Spec (.of k)))
  exact ⟨compactExchangePullObject ell pchar hp hell k f cpt
      (pullback.snd f f) (pullback.fst f f) f (nativeDiagonalSquare f) R hR M,
    compactChosenExchange ell pchar hp hell k f cpt
      (pullback.snd f f) (pullback.fst f f) f (nativeDiagonalSquare f) R hR c1 M⟩

/-- Native compact-support transpose, directly in the intrinsic full subcategories.
Source: det-sp-reduction-exceptional, adjunction
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalTranspose (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (cpt : Compactification f)
    (hF : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R cpt.i cpt.g).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R)
    (adj : reductionCtfCompactSupport R cpt.i cpt.g hF ⊣ G)
    (M : spFiniteConstructibleTorCategory X R) (K : spFiniteConstructibleTorCategory Y R)
    (a : (reductionCompactSupport R cpt.i cpt.g).obj M.obj ⟶ K.obj) :
    M.obj ⟶ (G.obj K).obj :=
  ((adj.homEquiv M K) (ObjectProperty.homMk a)).hom

section Geometry
variable (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : pchar ≠ ell)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (cpt : Compactification f)
    (c1 : Compactification (pullback.fst f f))
    (R : Type u) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, ∀ x : R, (ell ^ n) • x = 0)
    (hF : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R cpt.i cpt.g).obj M.obj))
    (hF1 : ∀ M : spFiniteConstructibleTorCategory (pullback f f) R,
      spFiniteConstructibleTor X R ((reductionCompactSupport R c1.i c1.g).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R)
    (G1 : spFiniteConstructibleTorCategory X R ⥤
      spFiniteConstructibleTorCategory (pullback f f) R)
    (adj : reductionCtfCompactSupport R cpt.i cpt.g hF ⊣ G)
    (adj1 : reductionCtfCompactSupport R c1.i c1.g hF1 ⊣ G1)
    (hX : spFiniteConstructibleTor X R (nativeDiagonalUnit R X))
    (hY : spFiniteConstructibleTor Y R (nativeDiagonalUnit R Y))

/-- Native inverse section compositor, using the normalized intrinsic identity and
composition comparisons, in the direction id -> Delta* p2*.
Source: compatibility proof (3), section compositor
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalSection (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (proEtaleDerivedCategory X R) ≅
      proEtaleConstantRingDerivedPullback R (pullback.snd f f) ⋙
        proEtaleConstantRingDerivedPullback R (pullback.diagonal f) :=
  (proEtaleGlobalEvaluationPullbackId R X).symm ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback R)
      (pullback.diagonal_snd f).symm) ≪≫
    (proEtaleConstantRingPullbackComposition (pullback.diagonal f) (pullback.snd f f) R).symm

end Geometry

/-- Specialize exactly the native package's unique coefficient mate at R_Y and then
apply GB to the normalized scalar-unit identification. No framework coefficient map
or separately chosen exceptional functor occurs.
Source: det-sp-reduction-exceptional and compatibility proof (3), delta_f
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalDualizingScalar
    (ell : ℕ) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cpt : Compactification f) (d : ℕ) (E : NativeDiagonalExceptionalData ell φ f cpt d)
    (hYA : spFiniteConstructibleTor Y A (nativeDiagonalUnit A Y))
    (hYB : spFiniteConstructibleTor Y B (nativeDiagonalUnit B Y)) :
    (scalarExtensionFunctor φ X).obj (nativeDiagonalOmega A E.GA hYA).obj ⟶
      (nativeDiagonalOmega B E.GB hYB).obj :=
  (E.c.app ⟨nativeDiagonalUnit A Y, hYA⟩).hom ≫
    (E.GB.map (ObjectProperty.homMk (nativeDiagonalScalarUnit φ Y).hom)).hom

/-- q_(p1,Delta) uses the inverse of directImageScalarPullbackIso at Delta, followed
by intrinsic Delta* of the unit-normalized coefficient map of the selected p1 package.
Source: compatibility proof (3), q_(p1,Delta)
(blueprint: lem-sp-finite-smooth-diagonal-scalar). -/
def nativeDiagonalSectionScalar
    (ell : ℕ) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c1 : Compactification (pullback.fst f f)) (d : ℕ)
    (E1 : NativeDiagonalExceptionalData ell φ (pullback.fst f f) c1 d)
    (hXA : spFiniteConstructibleTor X A (nativeDiagonalUnit A X))
    (hXB : spFiniteConstructibleTor X B (nativeDiagonalUnit B X)) :
    (scalarExtensionFunctor φ X).obj
        ((proEtaleConstantRingDerivedPullback A (pullback.diagonal f)).obj
          (nativeDiagonalOmega A E1.GA hXA).obj) ⟶
      (proEtaleConstantRingDerivedPullback B (pullback.diagonal f)).obj
        (nativeDiagonalOmega B E1.GB hXB).obj :=
  (directImageScalarPullbackIso φ (pullback.diagonal f)).inv.app _ ≫
    (proEtaleConstantRingDerivedPullback B (pullback.diagonal f)).map
      (nativeDiagonalDualizingScalar ell φ (pullback.fst f f) c1 d E1 hXA hXB)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
