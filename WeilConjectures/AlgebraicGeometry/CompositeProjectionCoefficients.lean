/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SecSmoothPurity.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.CompositionComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtaleCtfPullbackDomains
public import WeilConjectures.AlgebraicGeometry.FiniteOrientationReduction
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositorRealization
public import WeilConjectures.AlgebraicGeometry.FiniteRingCompactSupportProjection
public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
public import WeilConjectures.CategoryTheory.SystemDerivedSubsequence
public import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
public import WeilConjectures.SixFunctors.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralCompactificationRealizationData
public import WeilConjectures.CategoryTheory.ArithmeticSystemRightAdjoint
import WeilConjectures.AlgebraicGeometry.CompactifiableOverField
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothLevelOfOrientation
import WeilConjectures.AlgebraicGeometry.UniformTowerTensorClosure

/-! # Projection coherence at finite and tower coefficients

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
sk-prop-sp-composition-factors.proof.md, (2)
(blueprint: lem-sp-composite-projection-coefficients).

All projections below are the actual proper-counit/open-extension composites.
Tower equations are equations in ordinary system derived categories, before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u vC vD uC uD
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients

/-- The four asserted projection laws, with all unit and associativity constraints explicit.
This is only a name for the conclusion; the applications supply the canonical projection
and pullback comparisons, not freely chosen maps.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def ProjectionLaws {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (U : D ⥤ C) (PC : ObjectProperty C) (PD : ObjectProperty D)
    (P : ∀ M L, F.obj M ⊗ L ⟶ F.obj (M ⊗ U.obj L))
    (pu : U.obj (𝟙_ D) ≅ 𝟙_ C)
    (pt : ∀ L L', U.obj (L ⊗ L') ≅ U.obj L ⊗ U.obj L') : Prop :=
  (∀ M L, PC M → PD L → IsIso (P M L)) ∧
  (∀ M M' L L', PC M → PC M' → PD L → PD L' →
    ∀ (a : M ⟶ M') (b : L ⟶ L'),
      (F.map a ⊗ₘ b) ≫ P M' L' = P M L ≫ F.map (a ⊗ₘ U.map b)) ∧
  (∀ M, PC M → P M (𝟙_ D) ≫
    F.map ((M ◁ pu.hom) ≫ (ρ_ M).hom) = (ρ_ (F.obj M)).hom) ∧
  (∀ M L L', PC M → PD L → PD L' →
    P M (L ⊗ L') ≫ F.map (M ◁ (pt L L').hom) ≫
      F.map (α_ M (U.obj L) (U.obj L')).inv =
    (α_ (F.obj M) L L').inv ≫ (P M L ▷ L') ≫ P (M ⊗ U.obj L) L')

/-- Canonical finite compactification projection, with finite-ring Noetherianity supplied
internally. Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def finiteProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.FiniteSmoothPurity.proCategory A X)
    (L : Etale.FiniteSmoothPurity.proCategory A Y) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app L

/-- Canonical monoidal pullback tensor comparison, with finite-ring Noetherianity supplied.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def finitePullTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L L' : Etale.FiniteSmoothPurity.proCategory A Y) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f L L'

/-- The canonical pullback unit comparison, with finite-ring Noetherianity internal.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def finitePullUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f

section Geometry
variable (D : FiniteFieldDatum.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))] [hXft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [hXqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [hYsep : IsSeparated (Y ↘ Spec (.of D.k))] [hYft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hYqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [hZsep : IsSeparated (Z ↘ Spec (.of D.k))] [hZft : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [hZqc : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [hfOver : f.IsOver (Spec (.of D.k))] [hgOver : g.IsOver (Spec (.of D.k))]
  [hfSep : IsSeparated f] [hgSep : IsSeparated g]
  (d e : ℕ) [hfSmooth : SmoothOfRelativeDimension d f] [hgSmooth : SmoothOfRelativeDimension e g]

include hXsep hXft hXqc hYsep hYft hYqc hZsep hZft hZqc
  hfOver hgOver hfSep hgSep hfSmooth hgSmooth

set_option linter.unusedSectionVars false in
/-- Noetherian schemes, compactifiability of all three maps, and additive relative dimension.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: finite type over a field gives Noetherianity. The standing compactification setting
supplies compactifications with separated finite-type middle schemes. Smooth relative
dimensions add, including empty sources (lem-sbc-smooth-relative-dimension-permanence). -/
theorem geometry : IsNoetherian X ∧ IsNoetherian Y ∧ IsNoetherian Z ∧
    HasCompactification f ∧ HasCompactification g ∧ HasCompactification (f ≫ g) ∧
    SmoothOfRelativeDimension (d + e) (f ≫ g) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (Z ↘ Spec (.of D.k))
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact ⟨inferInstance, inferInstance, inferInstance,
    hasCompactification_of_finiteType_over_field D.k X Y f,
    hasCompactification_of_finiteType_over_field D.k Y Z g,
    hasCompactification_of_finiteType_over_field D.k X Z (f ≫ g), inferInstance⟩

set_option linter.unusedSectionVars false in
/-- The three displayed finite-coefficient objects have the required intrinsic domains.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: finiteGeneralRingSmoothPurity identifies each dualizing object with its shifted
Tate line and identifies G_g K with g^*K(e)[2e]. Pullback preserves constructibility and
finite Tor amplitude (lem-sp-proetale-ctf-pullback-domains). Tate lines are locally free
of rank one, so their pulled-back tensor product is again constructible of finite Tor
amplitude. No DVR presentation of the finite coefficient ring is used. -/
theorem finite_domains (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    [HasCompactification f] [HasCompactification g]
    (K : Etale.FiniteSmoothPurity.proCategory A Z)
    (_hK : Etale.FiniteSmoothPurity.IsCtf A Z K) :
    Etale.FiniteSmoothPurity.IsCtf A Y
      ((Etale.FiniteSmoothPurity.exceptional A g).obj (finiteGeneralRingUnit A Z)) ∧
    Etale.FiniteSmoothPurity.IsCtf A Y ((Etale.FiniteSmoothPurity.exceptional A g).obj K) ∧
    Etale.FiniteSmoothPurity.IsCtf A X
      ((Etale.FiniteSmoothPurity.proPullback A f).obj
        ((Etale.FiniteSmoothPurity.exceptional A g).obj (finiteGeneralRingUnit A Z)) ⊗
        (Etale.FiniteSmoothPurity.exceptional A f).obj (finiteGeneralRingUnit A Y)) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (Z ↘ Spec (.of D.k))
  obtain ⟨n, hn, hAn⟩ := _hA
  let P := finiteGeneralRingPrimeSetting D ell _hne n hn
  have hZ : IsUnit ((ell ^ n : ℕ) : Γ(Z, ⊤)) := by
    simpa only [P, PurityFiniteSetting.diagonalExponent, finiteGeneralRingPrimeSetting]
      using P.diagonalExponent_isUnit (Z ↘ Spec (.of D.k))
  let : HasInvertibleExponent A Z :=
    ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n, hAn, hZ⟩
  have hunit : Etale.FiniteSmoothPurity.IsCtf A Z (finiteGeneralRingUnit A Z) :=
    Etale.FiniteSmoothPurity.isCtfOfIso A Z
      ((Etale.FiniteSmoothPurity.comparison A Z).mapIso
        (PurityFiniteSetting.smoothPurityUnitIso A Z)).symm
      (Etale.FiniteSmoothPurity.comparisonCtf A Z _
        (Etale.FiniteSmoothPurity.ordinaryUnitCtf A Z))
  have exceptional_mem (N : Etale.FiniteSmoothPurity.proCategory A Z)
      (hN : Etale.FiniteSmoothPurity.IsCtf A Z N) :
      Etale.FiniteSmoothPurity.IsCtf A Y ((Etale.FiniteSmoothPurity.exceptional A g).obj N) :=
    Etale.FiniteSmoothPurity.comparisonCtf A Y _
      (Etale.FiniteSmoothPurity.ordinaryExceptionalCtf A g e _
        (Etale.FiniteSmoothPurity.actualOriginCtf A Z N hN))
  have hOmega := exceptional_mem _ hunit
  refine ⟨hOmega, exceptional_mem K _hK, ?_⟩
  have : IsSeparated (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change IsSeparated (X ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (X ↘ Spec (.of D.k))
    infer_instance
  have : IsSeparated (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change IsSeparated (Y ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of D.k))
    infer_instance
  let fOver : Over.mk (X ↘ Spec (.of D.k)) ⟶ Over.mk (Y ↘ Spec (.of D.k)) :=
    Over.homMk f (by simp)
  have : IsSeparated fOver.left := by
    change IsSeparated f
    infer_instance
  have : SmoothOfRelativeDimension d fOver.left := by
    change SmoothOfRelativeDimension d f
    infer_instance
  have : HasCompactification fOver.left := by
    change HasCompactification f
    infer_instance
  exact CtfPullbackDomains.finite_smooth_tensor_ctf D ell _hne A ⟨n, hn, hAn⟩
    (Over.mk (X ↘ Spec (.of D.k))) (Over.mk (Y ↘ Spec (.of D.k)))
    fOver d _ hOmega

/-- The composition identity for the fixed proper/open compositor, in the finite derived
category. The existential witnesses are proof fields that the two inputs have etale origin;
they choose no object or map. Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: choose bounded constructible etale origins using the finite-ring origin theorem.
The site tensor-transpose theorem preserves projection and counit; finiteCompactSiteCoherence
preserves this same compositor. Apply compactification-projection-composition on a compatible
triangle. Common refinements and refinement-projection-counit extend it to the three retained
compactifications. The witnesses affect no underlying derived object. -/
theorem finite_composition (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (M : Etale.FiniteSmoothPurity.proCategory A X)
    (L : Etale.FiniteSmoothPurity.proCategory A Z)
    (_hM : Etale.FiniteSmoothPurity.IsCtf A X M)
    (_hL : Etale.FiniteSmoothPurity.IsCtf A Z L) :
    ∃ hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M,
    ∃ hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (M ⊗ (Etale.FiniteSmoothPurity.proPullback A f).obj
        ((Etale.FiniteSmoothPurity.proPullback A g).obj L)),
      ((SpTowerCalculus.finiteCanonicalComposition A f g cf cg ch).hom.app ⟨M, hM⟩ ▷ L) ≫
          finiteProjection A ch M L ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch).map
            (M ◁ (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app L) =
        finiteProjection A cg
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) L ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
            (finiteProjection A cf M ((Etale.FiniteSmoothPurity.proPullback A g).obj L)) ≫
          (SpTowerCalculus.finiteCanonicalComposition A f g cf cg ch).hom.app ⟨_, hT⟩ := by
  sorry

/-- Invertibility, joint naturality, unit normalization and tensor associativity of the
canonical finite projection, on exactly the intrinsic constructible finite-Tor objects.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: finite constructible origins transport the proper projection theorem through the
fixed site comparison. Open extension has its canonical tensor isomorphism; composing
these gives invertibility. Naturality is that of the two actual transformations. The
proper counit projection at the unit transposes to the adjunction counit and hence is
the scalar unitor. The open equation follows after fully faithful restriction. For two
tensor variables use proper counit naturality and the monoidal pullback associator;
the open identity again follows by restriction. Reassociate the proper/open factors,
retaining the signed derived associators. No DVR presentation is used. -/
theorem finite_projection_laws (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (cf : Compactification f) :
    ProjectionLaws
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf)
      (Etale.FiniteSmoothPurity.proPullback A f)
      (Etale.FiniteSmoothPurity.IsCtf A X) (Etale.FiniteSmoothPurity.IsCtf A Y)
      (finiteProjection A cf) (finitePullUnit A f) (finitePullTensor A f) := by
  sorry

/-- Smooth dualizing objects and the precise Tor-interval effect of the Tate line.
The line is the published ordered positive Tate line, shifted by the negative even
shift to give its degree-zero form; this introduces no new coefficient object.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: finiteGeneralRingSmoothPurity identifies omega with the comparison image of
A(d)[2d]. Each Tate line is locally free of rank one in degree zero. A trivializing
cover therefore identifies its tensor with the identity functor, preserving every Tor
interval. Derived cohomological shifts by 2d subtract 2d from both bounds. This holds
for the zero coefficient ring and empty schemes without a nonvanishing assumption. -/
theorem finite_orientation_and_tor (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (_hn : 0 < n)
    (hA : ((ell ^ n : ℕ) : A) = 0) [HasCompactification f] :
    Nonempty ((Etale.FiniteSmoothPurity.exceptional A f).obj (finiteGeneralRingUnit A Y) ≅
      (Etale.FiniteSmoothPurity.comparison A X).obj
        (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)) ∧
    ∀ (K : Etale.FiniteSmoothPurity.proCategory A X) (a b : ℤ), a ≤ b →
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b K →
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b
        (K ⊗ ((Etale.FiniteSmoothPurity.comparison A X).obj
          (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d))⟦-(2 * (d : ℤ))⟧) ∧
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X
        (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))
        (K ⊗ (Etale.FiniteSmoothPurity.comparison A X).obj
          (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)) := by
  sorry

/-- Finite site transport intertwines the same two compactification projection maps.
The comparison is the fixed proper counit mate followed by exact open extension;
its inverse is inserted at the retained bounded-below witnesses.
Source: blueprint composition-factors proof (2), finite site comparison
(blueprint: lem-sp-composite-projection-coefficients).
Proof: bounded constructible finite-Tor inputs have bounded-below etale origins, and
pullback and tensor preserve that domain. Transpose the proper square using the
canonical inverse-image adjunction: its two sides are the counit tensored with identity.
For the open square, restrict to the open and use the unit normalization; full
faithfulness identifies the maps. The K-flat tensor and pullback comparisons preserve
these equalities. Paste the proper and open squares. The resulting comparison is
compactSupportSiteComparison, the one used in finiteCanonicalComposition; hence the
transport preserves that same compositor and its counit-normalized right companion. -/
theorem finite_site_projection (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (cf : Compactification f) :
    letI : IsNoetherianRing A := isNoetherian_of_finite A A
    ∀ (M : Etale.DerivedCategoryModule A X) (L : Etale.DerivedCategoryModule A Y),
      Etale.FiniteSmoothPurity.IsCtf A X
        ((Etale.FiniteSmoothPurity.comparison A X).obj M) →
      Etale.FiniteSmoothPurity.IsCtf A Y
        ((Etale.FiniteSmoothPurity.comparison A Y).obj L) →
      ∃ hM : _root_.DerivedCategory.TStructure.t.plus M,
      ∃ hT : _root_.DerivedCategory.TStructure.t.plus
        (M ⊗ (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj L),
        (Etale.FiniteSmoothPurity.comparison A Y).map
            (finiteRingEtalePF (ModuleCat.{u + 1} A) cf M L) ≫
          (compactSupportSiteComparison A cf).inv.app ⟨_, hT⟩ ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
            (finiteRingTensorPullbackComparison
              (Etale.FiniteSmoothPurity.comparison A X)
              (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
              (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
              (Etale.FiniteSmoothPurity.comparison A Y)
              (finiteRingSiteTensor (ModuleCat.{u + 1} A) X)
              (finiteRingSitePullback (ModuleCat.{u + 1} A) f
                (unboundedDirectImagePullbackIso A f)) M L).hom =
        (finiteRingSiteTensor (ModuleCat.{u + 1} A) Y
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} A) cf).obj M) L).hom ≫
          ((compactSupportSiteComparison A cf).inv.app ⟨M, hM⟩ ⊗ₘ 𝟙 _) ≫
          finiteProjection A cf ((Etale.FiniteSmoothPurity.comparison A X).obj M)
            ((Etale.FiniteSmoothPurity.comparison A Y).obj L) := by
  sorry

end Geometry
/-- The unit isomorphism of a specified coherent monoidal pullback.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def monoidalPullUnit {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [MonoidalCategory C] [MonoidalCategory D]
    (U : D ⥤ C) (m : U.Monoidal) : U.obj (𝟙_ D) ≅ 𝟙_ C :=
  letI := m
  (Functor.Monoidal.εIso U).symm

/-- The tensor isomorphism with the pullback direction used in the displayed laws.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def monoidalPullTensor {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [MonoidalCategory C] [MonoidalCategory D]
    (U : D ⥤ C) (m : U.Monoidal) (L L' : D) :
    U.obj (L ⊗ L') ≅ U.obj L ⊗ U.obj L' :=
  letI := m
  (Functor.Monoidal.μIso U L L').symm

section Towers
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The existing uniform constructible finite-Tor property in section coordinates.
There is no normalization conjunct. Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerCtf (b : SpTowerShriek.Base ell E) (q : SpTowerCalculus.Coordinates ell E b)
    (T : Scheme.{u}) : ObjectProperty (SpTowerShriek.D ell E T) :=
  fun K ↦ spConstructibleTorTowers ell E T (q.abelian T)
    ((SpTowerCalculus.realization ell E b T (q.abelian T)).inverse.obj K)

/-- One common Tor interval at all actual quotient levels n+1.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerTorIn (T : Scheme.{u}) (K : SpTowerShriek.D ell E T) (a b : ℤ) : Prop :=
  a ≤ b ∧ ∀ n : ℕ, Scheme.HasProEtaleTorAmplitude T (SpTowerShriek.R ell E n)
    ((SpTowerShriek.Ev ell E T n).obj K) a b

/-- One common cohomological interval at every actual quotient level n+1.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerCohIn (T : Scheme.{u}) (K : SpTowerShriek.D ell E T) (a b : ℤ) : Prop :=
  a ≤ b ∧ ∀ n : ℕ,
    DerivedCategory.IsGE ((SpTowerShriek.Ev ell E T n).obj K) a ∧
    DerivedCategory.IsLE ((SpTowerShriek.Ev ell E T n).obj K) b

/-- The projection laws in the ordinary system derived category. The coherent pullback
unit is determined by its fixed pure-tensor comparison, not supplied as an assumption.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerProjectionLaws (b : SpTowerShriek.Base ell E)
    (o : SpTowerShriek.Operations ell E b) (q : SpTowerCalculus.Coordinates ell E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  letI := (b.calculus X).closed.monoidal
  letI := (b.calculus Y).closed.monoidal
  ∃ m : (SpTowerShriek.pull ell E b (o.geometry f)).Monoidal,
    (∀ L L', monoidalPullTensor (SpTowerShriek.pull ell E b (o.geometry f)) m L L' =
      (o.geometry f).tensorPullback.app (L, L')) ∧
    ProjectionLaws (SpTowerShriek.F ell E b o c)
      (SpTowerShriek.pull ell E b (o.geometry f))
      (towerCtf ell E b q X) (towerCtf ell E b q Y)
      (SpTowerShriek.projection ell E b o c)
      (monoidalPullUnit (SpTowerShriek.pull ell E b (o.geometry f)) m)
      (monoidalPullTensor (SpTowerShriek.pull ell E b (o.geometry f)) m)

/-- Canonical projection laws on every uniform constructible finite-Tor tower, before
finite evaluation; the ring transitions are those of the recorded sequence site.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: the system inverse-image tensorator comes from exact inverse image on module
sheaves and signed K-flat total tensors. Scalar multiplication gives its unit and
monoidal coherence. The actual system projection is the proper counit transpose
followed by the ordinary open-extension comparison. The common bounds and finite
constructible origins make its evaluated projections invertible; evaluation is
conservative on the ordinary derived category. Unit normalization and two-input
tensor associativity follow by the same counit calculation in the ringed sequence
topos itself. Thus the equations are not inferred merely from finite evaluations.
The section realization fixes all actual quotient-transition maps. -/
theorem tower_projection_laws (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
    (q : SpTowerCalculus.Coordinates ell E b)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f) :
    towerProjectionLaws ell E b o q c := by
  sorry

section TowerComposition
variable (D : FiniteFieldDatum.{u})
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b) (z : SpTowerCalculus.FiniteCoordinates ell E)
  (hP : SpTowerCalculus.Preservation ell E D.k b o q)
  (cal : SpTowerCalculus.Calculus ell E D.k b o q z hP)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [IsSeparated g] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
  [QuasiCompact f] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))

/-- The recorded proper/open compositor in section coordinates. Only the fixed
realization counits are inserted; its component is not chosen from finite evaluations.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerCompositor (K : SpTowerShriek.D ell E X) (hK : towerCtf ell E b q X K) :
    (SpTowerShriek.F ell E b o cg).obj ((SpTowerShriek.F ell E b o cf).obj K) ⟶
      (SpTowerShriek.F ell E b o ch).obj K :=
  (SpTowerShriek.F ell E b o cg).map
      ((SpTowerShriek.F ell E b o cf).map
        ((SpTowerCalculus.realization ell E b X (q.abelian X)).counitIso.inv.app K)) ≫
    (SpTowerShriek.F ell E b o cg).map
      ((SpCoordinateAdjunction.supportRealization ell E b o q cf).inv.app
        ((SpTowerCalculus.realization ell E b X (q.abelian X)).inverse.obj K)) ≫
    (SpCoordinateAdjunction.supportRealization ell E b o q cg).inv.app
      ((SpTowerCalculus.F ell E b o q cf).obj
        ((SpTowerCalculus.realization ell E b X (q.abelian X)).inverse.obj K)) ≫
    (SpTowerCalculus.realization ell E b Z (q.abelian Z)).functor.map
      ((cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom.app ⟨_, hK⟩) ≫
    (SpCoordinateAdjunction.supportRealization ell E b o q ch).hom.app
      ((SpTowerCalculus.realization ell E b X (q.abelian X)).inverse.obj K) ≫
    (SpTowerShriek.F ell E b o ch).map
      ((SpTowerCalculus.realization ell E b X (q.abelian X)).counitIso.hom.app K)

/-- The displayed composition equation with the actual tower compositor. Its last
pullback comparison is explicit, and all morphisms belong to ordinary system D.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients). -/
def towerCompositionLaw : Prop :=
  letI := (b.calculus X).closed.monoidal
  letI := (b.calculus Z).closed.monoidal
  ∀ (M : SpTowerShriek.D ell E X) (L : SpTowerShriek.D ell E Z)
    (hM : towerCtf ell E b q X M), towerCtf ell E b q Z L →
    ∃ hT : towerCtf ell E b q X
      ((SpTowerShriek.tensor ell E b X).obj
        (M, (SpTowerShriek.pull ell E b (o.geometry f)).obj
          ((SpTowerShriek.pull ell E b (o.geometry g)).obj L))),
      (towerCompositor ell E D b o q z hP cal f g cf cg ch M hM ▷ L) ≫
          SpTowerShriek.projection ell E b o ch M L ≫
          (SpTowerShriek.F ell E b o ch).map
            (M ◁ (o.comp f g).inv.app L) =
        SpTowerShriek.projection ell E b o cg
            ((SpTowerShriek.F ell E b o cf).obj M) L ≫
          (SpTowerShriek.F ell E b o cg).map
            (SpTowerShriek.projection ell E b o cf M
              ((SpTowerShriek.pull ell E b (o.geometry g)).obj L)) ≫
          towerCompositor ell E D b o q z hP cal f g cf cg ch _ hT

/-- Composition coherence in the system category, for arbitrary retained compactifications.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: pullback and tensor closure give the tensor-source witness with common bounds.
On a compatible proper/open triangle, expand the system projection as its proper
counit transpose and open projection. Proper counit naturality and the open unit
contraction give the identity with the normalized proper/open alpha. Common refinement
extends this to the three retained compactifications, using the refinement-projection
counit equations. The recorded calculus coherence identifies that alpha with the
compositor in this statement. Conjugation by the fixed realization counits gives
exactly the displayed formula. Every calculation occurs on the ringed sequence site;
finite evaluation and its actual quotient transitions preserve the resulting identity. -/
theorem tower_composition (_hne : ell ≠ D.p) (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    towerCompositionLaw ell E D b o q z hP cal f g cf cg ch := by
  sorry

set_option linter.unusedSectionVars false in
/-- All three displayed exceptional/tensor objects belong to the uniform domain.
The supplied pairs are the actual restricted adjunctions with counit-normalized levels.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: the actual coefficient unit has uniform intervals [0,0]. Smooth tower purity
identifies each omega with its shifted finite locally free Tate tower and identifies
G_g K with twisted shifted pullback. The pullback-domain theorem retains the same
finite constructible origins and both uniform intervals. Uniform tensor closure
then proves membership of the displayed composite source. This argument is independent
of normalization and of nonvanishing of any level. -/
theorem tower_domains (_hne : ell ≠ D.p) (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (Pf : TowerAdjointCompositor.Pair ell E b o q cf)
    (Pg : TowerAdjointCompositor.Pair ell E b o q cg)
    (K : SpTowerCalculus.C ell E b q Z) :
    towerCtf ell E b q Y ((SpTowerGamma.exceptional ell E b q Pg.right).obj
        ⟨SpTowerGamma.originalUnit ell E b q Z, SpFiniteOrientation.unit_tower_mem ell E b q Z⟩) ∧
    towerCtf ell E b q Y ((SpTowerGamma.exceptional ell E b q Pg.right).obj K) ∧
    towerCtf ell E b q X
      ((SpTowerShriek.tensor ell E b X).obj
        ((SpTowerShriek.pull ell E b (o.geometry f)).obj
          ((SpTowerGamma.exceptional ell E b q Pg.right).obj
            ⟨SpTowerGamma.originalUnit ell E b q Z,
              SpFiniteOrientation.unit_tower_mem ell E b q Z⟩),
        (SpTowerGamma.exceptional ell E b q Pf.right).obj
          ⟨SpTowerGamma.originalUnit ell E b q Y,
            SpFiniteOrientation.unit_tower_mem ell E b q Y⟩)) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let FX := SpTowerCalculus.realization ell E b X (q.abelian X)
  let FY := SpTowerCalculus.realization ell E b Y (q.abelian Y)
  let UY : SpTowerCalculus.C ell E b q Y :=
    ⟨SpTowerGamma.originalUnit ell E b q Y, SpFiniteOrientation.unit_tower_mem ell E b q Y⟩
  let UZ : SpTowerCalculus.C ell E b q Z :=
    ⟨SpTowerGamma.originalUnit ell E b q Z, SpFiniteOrientation.unit_tower_mem ell E b q Z⟩
  have exceptional_mem (N : SpTowerCalculus.C ell E b q Z) :
      towerCtf ell E b q Y ((SpTowerGamma.exceptional ell E b q Pg.right).obj N) :=
    CtfPullbackDomains.tower_ctf_iso ell E b q Y
      (FY.unitIso.app (Pg.right.obj N).obj) (Pg.right.obj N).property
  refine ⟨exceptional_mem UZ, exceptional_mem K, ?_⟩
  let P := (SpTowerShriek.pull ell E b (o.geometry f)).obj
    ((SpTowerGamma.exceptional ell E b q Pg.right).obj UZ)
  let N := Pf.right.obj UY
  have : IsSeparated (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change IsSeparated (Y ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of D.k))
    infer_instance
  have : IsSeparated (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change IsSeparated (X ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (X ↘ Spec (.of D.k))
    infer_instance
  have hP : spConstructibleTorTowers ell E X (q.abelian X) (FX.inverse.obj P) :=
    CtfPullbackDomains.tower_pullback_mem ell E b o q D _hne
      (Over.mk (Y ↘ Spec (.of D.k))) (Over.mk (X ↘ Spec (.of D.k)))
      (Over.homMk f (by simp)) (Pg.right.obj UZ).obj (Pg.right.obj UZ).property
  have h := UniformTowerTensorClosure.tensor_mem ell E b q X
    (FX.inverse.obj P) N.obj hP N.property
  exact CtfPullbackDomains.tower_ctf_iso ell E b q X
    (FX.inverse.mapIso ((SpTowerShriek.tensor ell E b X).mapIso
      ((FX.counitIso.app P).prod (Iso.refl _)))) h

/-- The precise common intervals for the actual strict Tate line and its even shift.
Source: blueprint composition-factors proof (2)
(blueprint: lem-sp-composite-projection-coefficients).
Proof: tower_gamma supplies the ordered orientation. The normalized products of the
strict Tate towers identify its ordered tensor with the degree-d line shifted by 2d;
these are actual sheaf morphisms compatible with quotient transitions. At each level
the unshifted line is locally free of rank one, so its tensor preserves every Tor
interval and every cohomological interval. Even shift subtracts 2d from their endpoints.
The same intervals work at every positive coefficient level. This proof works with
the zero complex and empty schemes; it does not claim nonzero cohomology in degree -2d. -/
theorem tower_orientation_and_intervals (_hne : ell ≠ D.p) (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (Pf : TowerAdjointCompositor.Pair ell E b o q cf)
    (w : SpChartAdmissibility.Twists ell E X) :
    Nonempty ((SpTowerGamma.exceptional ell E b q Pf.right).obj
        ⟨SpTowerGamma.originalUnit ell E b q Y, SpFiniteOrientation.unit_tower_mem ell E b q Y⟩ ≅
      (SpCoordinateAdjunction.line ell E w d)⟦(2 * (d : ℤ))⟧) ∧
    ∀ (K : SpTowerShriek.D ell E X) (a b' : ℤ),
      (towerTorIn ell E X K a b' →
        towerTorIn ell E X ((SpTowerShriek.tensor ell E b X).obj
          (K, SpCoordinateAdjunction.line ell E w d)) a b' ∧
        towerTorIn ell E X ((SpTowerShriek.tensor ell E b X).obj
          (K, (SpCoordinateAdjunction.line ell E w d)⟦(2 * (d : ℤ))⟧))
          (a - 2 * (d : ℤ)) (b' - 2 * (d : ℤ))) ∧
      (towerCohIn ell E X K a b' →
        towerCohIn ell E X ((SpTowerShriek.tensor ell E b X).obj
          (K, SpCoordinateAdjunction.line ell E w d)) a b' ∧
        towerCohIn ell E X ((SpTowerShriek.tensor ell E b X).obj
          (K, (SpCoordinateAdjunction.line ell E w d)⟦(2 * (d : ℤ))⟧))
          (a - 2 * (d : ℤ)) (b' - 2 * (d : ℤ))) := by
  sorry

end TowerComposition
/-- The actual arithmetic selection in ordinary section coordinates. The four
normalizations fix every module and morphism on the sequence site; in particular
this is not a family of unrelated finite-level comparisons.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
structure ArithmeticRestriction (b : SpTowerShriek.Base ell E) where
  index : ℕ ↪o ℕ
  index_eq : ∀ n : ℕ, index n = b.ramification * (n + 1) - 1
  ordinary : ∀ T : Scheme.{u}, coefficientSequenceModules ell E T ⥤ SpTowerShriek.S ell E T
  [additive : ∀ T : Scheme.{u}, (ordinary T).Additive]
  [limits : ∀ T : Scheme.{u}, PreservesFiniteLimits (ordinary T)]
  [colimits : ∀ T : Scheme.{u}, PreservesFiniteColimits (ordinary T)]
  sections : ∀ (T : Scheme.{u}) (M : coefficientSequenceModules ell E T)
    (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq (((ordinary T).obj M).val.obj (Opposite.op (n, U.unop)))
      (M.val.obj (Opposite.op (index n, U.unop)))
  restrictions : ∀ (T : Scheme.{u}) (M : coefficientSequenceModules ell E T)
    {V W : (ℕ × T.ProEt)ᵒᵖ} (a : V ⟶ W),
    HEq (((ordinary T).obj M).val.map a)
      (M.val.map ((index.toOrderHom.toFunctor.prod (𝟭 T.ProEt)).op.map a))
  maps : ∀ (T : Scheme.{u}) {M N : coefficientSequenceModules ell E T} (a : M ⟶ N)
    (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq (((ordinary T).map a).val.app (Opposite.op (n, U.unop)))
      (a.val.app (Opposite.op (index n, U.unop)))

attribute [instance] ArithmeticRestriction.additive ArithmeticRestriction.limits
  ArithmeticRestriction.colimits

/-- Exact termwise localization of the normalized arithmetic restriction.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def ArithmeticRestriction.derived {b : SpTowerShriek.Base ell E}
    (a : ArithmeticRestriction ell E b) (T : Scheme.{u}) :=
  (a.ordinary T).mapDerivedCategory

/-- The canonical exact-localization word for a comparison of exact ordinary functors.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def deriveExactSquare {C₁ C₂ D₁ D₂ : Type uC}
    [Category.{vC} C₁] [Category.{vC} C₂] [Category.{vC} D₁] [Category.{vC} D₂]
    [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory.{uD} C₁] [HasDerivedCategory.{uD} C₂]
    [HasDerivedCategory.{uD} D₁] [HasDerivedCategory.{uD} D₂]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ D₂) (H : C₁ ⥤ D₁) (I : D₁ ⥤ D₂)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteLimits H] [PreservesFiniteLimits I]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    [PreservesFiniteColimits H] [PreservesFiniteColimits I]
    (a : F ⋙ G ≅ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso H I

/-- Repackage the fixed uniformizer K-flat model at the coefficient universe used by
ell-power systems. All underlying coefficient, site and localization sizes agree;
only the redundant record universe differs. No tensor or representative map changes.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def uniformizerTensorModel (T : Scheme.{u}) :
    SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T)) (coefficientSequenceCommRingSheaf ell E T)
      (IntegralSystemRealization.calculus ell E T).systemClosed :=
  CoefficientTensorModels.mk.{u + 1, u + 1, u, u + 2}
    (comparison := CoefficientTensorModels.comparison.{u, u + 1, u, u + 2}
    (IntegralSystemRealization.calculus ell E T).systemTensorModel
    ) (uncurry_model := CoefficientTensorModels.uncurry_model.{u, u + 1, u, u + 2}
      (IntegralSystemRealization.calculus ell E T).systemTensorModel)

/-- Normalized arithmetic pullback, proper direct-image and open-extension comparisons.
Direct-image normalization is the identity on actual selected sections; inverse image
is its adjunction mate, and the derived proper comparison is the corresponding counit
mate. Open extension is fixed by its adjunction mate. Tensor uses the recorded signed
K-flat representative model with the ordinary identity-on-pure-tensors normalization.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
structure ArithmeticComparisons (b : SpTowerShriek.Base ell E)
    (o : SpTowerShriek.Operations ell E b)
    (v : IntegralSystemRealization.Operations ell E)
    (a : ArithmeticRestriction ell E b) where
  ordinaryDirect : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pullbackTensorSequenceDirect ell E f ⋙ a.ordinary Y ≅
      a.ordinary X ⋙ (o.geometry f).push
  ordinaryDirect_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficientSequenceModules ell E X) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : (((a.ordinary Y).obj ((pullbackTensorSequenceDirect ell E f).obj M)).val.obj
      (Opposite.op (n, U.unop)))),
    HEq (((ordinaryDirect f).hom.app M).val.app (Opposite.op (n, U.unop)) x) x
  ordinaryPull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pullbackTensorSequenceInverse ell E f ⋙ a.ordinary X ≅
      a.ordinary Y ⋙ (o.geometry f).pull
  ordinaryPull_mate : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (ordinaryPull f).inv =
      ((mateEquiv (pullbackTensorSequenceAdjunction ell E f)
        (o.geometry f).ordinaryAdjunction).symm
          (TwoSquare.mk _ _ _ _ (ordinaryDirect f).hom)).natTrans
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IntegralSystemRealization.pull ell E f ⋙ a.derived ell E X ≅
      a.derived ell E Y ⋙ SpTowerShriek.pull ell E b (o.geometry f)
  pull_localization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pull f = deriveExactSquare _ _ _ _ (ordinaryPull f)
  direct : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
    IntegralSystemRealization.Operations.push ell E v f ⋙ a.derived ell E Y ≅
      a.derived ell E X ⋙ SpTowerShriek.push ell E b (o.geometry f)
  direct_mate : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
    (direct f).hom =
      (mateEquiv (v.direct f).adj (SpTowerShriek.adjunction ell E b (o.geometry f))
        (TwoSquare.mk _ _ _ _ (pull f).inv)).natTrans
  openComp : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    IntegralSystemRealization.Operations.shriek ell E v j ⋙ a.derived ell E Y ≅
      a.derived ell E X ⋙ SpTowerShriek.openD ell E b (o.openOp j)
  open_mate : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j],
    (openComp j).inv =
      ((mateEquiv (v.extension j).adj
        (o.openOp j).derivedAdjunction).symm
          (TwoSquare.mk _ _ _ _ (pull j).hom)).natTrans
  tensor : ∀ T : Scheme.{u},
    (IntegralSystemRealization.calculus ell E T).systemClosed.tensor ⋙ a.derived ell E T ≅
      ((a.derived ell E T).prod (a.derived ell E T)) ⋙ SpTowerShriek.tensor ell E b T
  tensorModel : ∀ T : Scheme.{u},
    SemilinearSections.TensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (coefficientSequenceTopology (ProEt.topology T))
      (coefficientSequenceCommRingSheaf ell E T) (SpTowerClasses.systemRing ell E T)
      (a.ordinary T) (IntegralSystemRealization.calculus ell E T).systemClosed
      (b.calculus T).closed (uniformizerTensorModel ell E T)
      (b.calculus T).tensorModels (tensor T)
  tensor_pure : ∀ (T : Scheme.{u}) (M N : coefficientSequenceModules ell E T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj (Opposite.op (a.index n, U.unop)))
    (y : N.val.obj (Opposite.op (a.index n, U.unop)))
    (x' : (((a.ordinary T).obj M).val.obj (Opposite.op (n, U.unop))))
    (y' : (((a.ordinary T).obj N).val.obj (Opposite.op (n, U.unop))))
    (z : (((a.ordinary T).obj
      (SemilinearSections.ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (coefficientSequenceCommRingSheaf ell E T) M N)).val.obj
          (Opposite.op (n, U.unop)))),
    HEq x x' → HEq y y' →
    HEq z (SemilinearSections.tensorSection.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (coefficientSequenceCommRingSheaf ell E T) M N
      (Opposite.op (a.index n, U.unop)) x y) →
    (SemilinearSections.TensorComparisonModel.ordinary.{u + 1, u, u + 1}
      (tensorModel T) M N).hom.val.app (Opposite.op (n, U.unop)) z =
      SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing ell E T)
        ((a.ordinary T).obj M) ((a.ordinary T).obj N) (Opposite.op (n, U.unop)) x' y'

/-- Arithmetic compact-support comparison, assembled from its counit-normalized proper
and unit-normalized open comparisons in the specified order.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def ArithmeticComparisons.support {b : SpTowerShriek.Base ell E}
    {o : SpTowerShriek.Operations ell E b} {v : IntegralSystemRealization.Operations ell E}
    {a : ArithmeticRestriction ell E b} (t : ArithmeticComparisons ell E b o v a)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (IntegralSystemRealization.Operations.shriek ell E v c.i ⋙
      IntegralSystemRealization.Operations.push ell E v c.g) ⋙ a.derived ell E Y ≅
    a.derived ell E X ⋙ SpTowerShriek.F ell E b o c :=
  (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _ (t.direct c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (t.openComp c.i) _ ≪≫ Functor.associator _ _ _

/-- Uniform constructible finite-Tor objects in the original uniformizer system.
Both intervals are common to every positive level, without normalization.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def uniformizerCtf (T : Scheme.{u})
    (M : IntegralSystemRealization.System ell E T) : Prop :=
  (∀ n : ℕ,
    letI : Finite (Padic.coefficientExtensionRing ell E (n + 1)) :=
      Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.le_add_left 1 n)
    spFiniteConstructibleTor T (Padic.coefficientExtensionRing ell E (n + 1))
      ((coefficientSequenceDerivedEvaluation ell E T n).obj M)) ∧
  ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
    (DerivedCategory.IsGE ((coefficientSequenceDerivedEvaluation ell E T n).obj M) a ∧
      DerivedCategory.IsLE ((coefficientSequenceDerivedEvaluation ell E T n).obj M) b) ∧
    Scheme.HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing ell E (n + 1))
      ((coefficientSequenceDerivedEvaluation ell E T n).obj M) c d

/-- Arithmetic restriction retains the two common intervals and constructible levels.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients).
Proof: exact restriction and its localized evaluation identify level n with level
r(n+1)-1 of the original system, by the equality of quotient ideals. Thus each selected
level is constructible finite-Tor, and the original two intervals apply unchanged.
The fixed realization identifies this property with spConstructibleTorTowers. -/
theorem arithmetic_restriction_ctf (b : SpTowerShriek.Base ell E)
    (q : SpTowerCalculus.Coordinates ell E b) (a : ArithmeticRestriction ell E b)
    (T : Scheme.{u}) (M : IntegralSystemRealization.System ell E T)
    (_hM : uniformizerCtf ell E T M) :
    towerCtf ell E b q T ((a.derived ell E T).obj M) := by
  sorry

/-- The arithmetic restriction identifies the actual compactification projections.
All three endpoint comparisons are retained in this equation of system morphisms.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def ArithmeticComparisons.ProjectionLaw {b : SpTowerShriek.Base ell E}
    {o : SpTowerShriek.Operations ell E b} {v : IntegralSystemRealization.Operations ell E}
    {a : ArithmeticRestriction ell E b} (t : ArithmeticComparisons ell E b o v a)
    (D : FiniteFieldDatum.{u})
    (c : IntegralSystemRealization.Compositors ell E v)
    (x : IntegralSystemRealization.OpenComparisons ell E v c) : Prop :=
  ∀ {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (cf : Compactification f)
    (M : IntegralSystemRealization.System ell E X)
    (L : IntegralSystemRealization.System ell E Y),
    uniformizerCtf ell E X M → uniformizerCtf ell E Y L →
    (a.derived ell E Y).map
        (IntegralSystemRealization.compactificationProjection ell E v c x cf M L) ≫
      (t.support ell E cf).hom.app
        ((IntegralSystemRealization.calculus ell E X).systemClosed.tensor.obj
          (M, (IntegralSystemRealization.pull ell E f).obj L)) ≫
      (SpTowerShriek.F ell E b o cf).map
        ((t.tensor X).hom.app (M, (IntegralSystemRealization.pull ell E f).obj L)) ≫
      (SpTowerShriek.F ell E b o cf).map
        ((SpTowerShriek.tensor ell E b X).map
          (Prod.mkHom (𝟙 _) ((t.pull f).hom.app L))) =
    (t.tensor Y).hom.app
        ((IntegralSystemRealization.Operations.push ell E v cf.g).obj
          ((IntegralSystemRealization.Operations.shriek ell E v cf.i).obj M), L) ≫
      (SpTowerShriek.tensor ell E b Y).map
        (Prod.mkHom ((t.support ell E cf).hom.app M) (𝟙 _)) ≫
      SpTowerShriek.projection ell E b o cf
        ((a.derived ell E X).obj M) ((a.derived ell E Y).obj L)

/-- Arithmetic restriction with canonical ordinary, tensor, proper and open comparisons
exists and identifies the compactification projection transformations before evaluation.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients).
Proof: let e be the recorded ramification index and select level e(n+1)-1. The equality
of coefficient ideals identifies the actual selected quotient with the ell-power
quotient. Restrict every module and every sequence-site map by this selection and
quotient congruence; this gives the section, transition and morphism normalizations.
The floor right extension is zero below e and restricts scalars from the last selected
index otherwise. Its exactness and UJ=id prove that restriction preserves K-flat
complexes. The ordinary pure-tensor identity therefore descends through the specified
signed total-tensor models. Ordinary geometric direct image commutes with selection
on sections. Adjunction gives the fixed pullback comparison, its proper counit mate
and the open unit mate. Insert these comparisons in the proper/open projection word;
the adjunction triangles and tensor normalization give precisely ProjectionLaw.
No equality of maps is inferred from equality of finite evaluations. -/
theorem arithmetic_projection (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
    (v : IntegralSystemRealization.Operations ell E)
    (r : IntegralSystemRealization.Realizations ell E D v) :
    ∃ a : ArithmeticRestriction ell E b,
    ∃ t : ArithmeticComparisons ell E b o v a,
      t.ProjectionLaw ell E D r.compositors r.openComparisons := by
  sorry

section ArithmeticComposition
variable (D : FiniteFieldDatum.{u})
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b) (z : SpTowerCalculus.FiniteCoordinates ell E)
  (hP : SpTowerCalculus.Preservation ell E D.k b o q)
  (cal : SpTowerCalculus.Calculus ell E D.k b o q z hP)
  (v : IntegralSystemRealization.Operations ell E)
  (r : IntegralSystemRealization.Realizations ell E D v)
  (a : ArithmeticRestriction ell E b) (t : ArithmeticComparisons ell E b o v a)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [IsSeparated g] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
  [QuasiCompact f] [QuasiCompact g]

/-- Arithmetic restriction identifies the actual proper/open compositors. The
quasicompactness instances needed by the representative formula follow from the
standing finite-type setting; they are supplied internally, not assumed.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients). -/
def ArithmeticComparisons.CompositionLaw : Prop :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (Z ↘ Spec (.of D.k))
  ∀ T : Compactification.Triangle f g,
    letI : IsNoetherian T.cf.Z := isNoetherian_of_locallyOfFiniteType T.cf.g
    letI : IsNoetherian T.cfg.Z := isNoetherian_of_locallyOfFiniteType T.cfg.g
    letI : QuasiCompact T.cf.i := T.cf.quasiCompact_openImmersion inferInstance
    letI : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
    letI : QuasiCompact T.q := inferInstance
    let openCongr := eqToHom (congrArg
      (fun j : {j : X ⟶ T.cfg.Z // IsOpenImmersion j} ↦
        letI : IsOpenImmersion j.val := j.property
        IntegralSystemRealization.Operations.shriek ell E v j.val)
      (Subtype.ext T.i_q :
        (⟨T.cf.i ≫ T.q, inferInstance⟩ : {j : X ⟶ T.cfg.Z // IsOpenImmersion j}) =
          ⟨T.cfg.i, inferInstance⟩))
    let compositor :=
      Functor.whiskerLeft (IntegralSystemRealization.Operations.shriek ell E v T.cf.i)
        (Functor.whiskerRight
          (r.properOpen.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
          (IntegralSystemRealization.Operations.push ell E v T.cg.g)) ≫
      Functor.whiskerRight
        ((r.compositors.openComp ell E T.cf.i T.q).hom ≫ openCongr)
        (IntegralSystemRealization.Operations.push ell E v T.p ⋙
          IntegralSystemRealization.Operations.push ell E v T.cg.g) ≫
      Functor.whiskerLeft (IntegralSystemRealization.Operations.shriek ell E v T.cfg.i)
        ((r.compositors.pushComp ell E T.p T.cg.g).hom ≫
          eqToHom (congrArg (IntegralSystemRealization.Operations.push ell E v) T.p_g))
    ∀ (M : IntegralSystemRealization.System ell E X)
      (hM : uniformizerCtf ell E X M),
      (a.derived ell E Z).map
          (compositor.app M) ≫
        (t.support ell E T.cfg).hom.app M =
      (t.support ell E T.cg).hom.app
          ((IntegralSystemRealization.Operations.shriek ell E v T.cf.i ⋙
            IntegralSystemRealization.Operations.push ell E v T.cf.g).obj M) ≫
        (SpTowerShriek.F ell E b o T.cg).map ((t.support ell E T.cf).hom.app M) ≫
        towerCompositor ell E D b o q z hP cal f g T.cf T.cg T.cfg _
          (arithmetic_restriction_ctf ell E b q a X M hM)

/-- The arithmetic projection comparison uses the same normalized compositor as
ordinary ell-power systems, so it carries the composition equation to that system.
Source: blueprint composition-factors proof (2), arithmetic restriction
(blueprint: lem-sp-composite-projection-coefficients).
Proof: ordinary restriction is identity at selected sections and quotient transitions.
It commutes with ordinary proper and open composition. The inverse-image companion
and proper counit mate are fixed by the ordinary direct comparison; open extension
is fixed by its unit mate. Consequently restriction preserves the proper/open
interchange mate and then its two composition factors, as system transformations.
The calculus normalization identifies this with the ell-power compositor. Common
refinements extend the triangle statement to every retained compactification; the
projection comparison is compatible with these same proper-counit refinement maps.
This proves preservation of the composition identity before finite evaluation. -/
theorem arithmetic_composition (_hne : ell ≠ D.p) (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    ArithmeticComparisons.CompositionLaw ell E D b o q z hP cal v r a t f g := by
  sorry

end ArithmeticComposition
end Towers
end AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients
