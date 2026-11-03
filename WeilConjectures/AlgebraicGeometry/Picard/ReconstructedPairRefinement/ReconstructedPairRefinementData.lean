/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralRepresentingPair.PurIntegralRepresentingPair
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementData
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.RingedPresentationOnSites.RingedPullbackPresentationOnSitesSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
public import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
public import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementFiniteNormalization
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementFiniteFactors
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.ClopenComparisonTensorSquare.ClopenReverseModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SmoothPurity.ReconstructedPairRefinement.RefinementFiniteOriginEvaluation

/-! # Refinement coherence of reconstructed exceptional representing pairs

Source: current blueprint sk-prop-sp-unique-adjoint, categorical proof, Transposes,
Naturality and Uniqueness; sk-thm-purity-transport, Steps 2--4; Stacks 0F7B--0F7D,
0F7J and 0ATU (blueprint: lem-pur-reconstructed-pair-refinement-coherence).

All system maps below are defined before evaluation or total limit. Quotient
coordinates are the dependency's exact equivalence, and beta is its uniquely
section-, open-unit- and proper-derived-unit-normalized comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
attribute [local irreducible] WeilConjectures.PurIntegralSupportComparison.beta
  WeilConjectures.PurIntegralRepresentingPair.transpose
  WeilConjectures.PurIntegralRepresentingPair.supportPresentation

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison

namespace WeilConjectures.ReconstructedPairRefinement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

/-- The dependency's own reconstructed support, without a new choice of functor.
Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
abbrev support (c : Compactification f) :=
  integralSupport l E c (C.coefficient E).reduction
    ((C.coefficient E).atCompactification X Y f c).integral

/-- The forward refinement q_R is the inverse of the actual clopen-mate limit map.
Source: Stacks 0F7B; blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def comparison {c d : Compactification f} (w : c.Refinement d) :
    support l E k C X Y f c ≅ support l E k C X Y f d :=
  letI := (C.refinement E X Y f w).invertible
  (asIso (integralRefinement l E k (C.coefficient E) X Y f w)).symm

/-- Supplied normalized exceptional data are exactly those of the recorded
representing-pair theorem; its published family retains the actual alpha and traces.
Source: blueprint integral-adjunction Hom display and unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
structure At (c : Compactification f) where
  strict : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c
  brown : EtaleTowerBrownAdjunction strict
  finite : BrownTowerComparison.FiniteEvaluation strict brown
  transport : BrownTowerComparison.TransportData strict brown finite
  normalized : BrownTowerComparison.Transport strict brown finite transport
    (finite := transport.finite)
  pairs : PurIntegralRepresentingPair.PublishedFamily l E strict brown finite transport
    (C.coefficient E).reduction
    ((C.coefficient E).atCompactification X Y f c).integral normalized

variable {l E k C X Y f}

/-- The supplied system type is reused verbatim, including both recognition modes.
Source: blueprint integral-adjunction hypotheses
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
abbrev At.Supplied {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) :=
  PurIntegralRepresentingPair.Supplied l E
    ((C.coefficient E).reduction X.scheme) ((C.coefficient E).reduction Y.scheme)
    D.strict D.brown D.finite D.transport L

/-- The Brown output in ordinary derived-system coordinates.
Source: blueprint integral-adjunction Hom display
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
abbrev At.output {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) :=
  (PurIntegralRepresentingPair.brown l E D.strict D.brown D.finite D.transport).obj
    ((PurIntegralRepresentingPair.reduction l E Y.scheme
      ((C.coefficient E).reduction Y.scheme)).obj L.obj)

/-- The normalized representing pair supplied by the recorded family.
Source: blueprint integral-adjunction conclusion
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
abbrev At.pair {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) (A : D.Supplied L) :=
  D.pairs.coordinate.pair L A

/-- The actual transported Brown counit, with the dependency's bounds and origin proofs.
Source: blueprint integral-adjunction unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def At.counit {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) (A : D.Supplied L) :=
  D.transport.counit _ (D.pair L A).origin (D.pair L A).normalized
    (D.pair L A).finiteTor (D.pair L A).lowerBound

/-- Component of coordinate conjugation, with all five factors explicit.
Source: node proof Step 1
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
@[irreducible] def conjugateComponent
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G : B ⥤ D) (F' G' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (t : F' ⟶ G') (K : B) : F.obj K ⟶ G.obj K :=
  F.map (e.counitIso.inv.app K) ≫ a.hom.app (e.inverse.obj K) ≫
    v.map (t.app (e.inverse.obj K)) ≫ b.inv.app (e.inverse.obj K) ≫
    G.map (e.counitIso.hom.app K)

/-- Conjugation of a natural transformation by coordinate and comparison isomorphisms.
Source: the coordinate-conjugation formula of node proof Step 1
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
@[irreducible] def conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G : B ⥤ D) (F' G' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (t : F' ⟶ G') : F ⟶ G where
  app K := conjugateComponent e v F G F' G' a b t K
  naturality K L m := by
    unfold conjugateComponent
    exact (Functor.whiskerRight e.counitIso.inv F ≫
      Functor.whiskerLeft e.inverse a.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft e.inverse t) v ≫
      Functor.whiskerLeft e.inverse b.inv ≫
      Functor.whiskerRight e.counitIso.hom G).naturality m

/-- The clopen-mate refinement d_w in the dependency's exact quotient coordinates.
The two outer factors are the actual coordinate-equivalence counit, and beta has
its recorded section and adjunction normalization. No evaluated arrows are lifted.
Source: Stacks 0F7B; node proof Steps 1 and 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def systemDown {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d) :
    D₂.transport.compact.functor ⟶ D₁.transport.compact.functor :=
  conjugate (coordinates l E X.scheme) (coordinates l E Y.scheme).functor
    D₂.transport.compact.functor D₁.transport.compact.functor
    (systemSupport l E d) (systemSupport l E c)
    (beta l E D₂.strict D₂.brown D₂.finite D₂.transport)
    (beta l E D₁.strict D₁.brown D₁.finite D₁.transport)
    (systemRefinement l E k X Y f w)

private theorem conjugate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G : B ⥤ D) (F' G' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (t : F' ⟶ G') (K : B) (ht : IsIso (t.app (e.inverse.obj K))) :
    IsIso ((conjugate e v F G F' G' a b t).app K) := by
  let := ht
  unfold conjugate
  dsimp only
  unfold conjugateComponent
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] systemRefinement coordinates in
private theorem intrinsic_isIso
    (R : CoefficientDerivedSystemCalculus.{u, u} l E Y.scheme)
    {c d : Compactification f} (w : c.Refinement d)
    (P : StrictEtaleEvaluation X.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site X.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : ∀ n : ℕ, ∃ H : DerivedCategory (strictEtaleLevel X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n),
      (∃ a : ℤ, H.IsGE a) ∧
        Nonempty ((V.comparison.evaluation.level n).inverse.obj H ≅
          (V.proEvaluation.evaluation n).obj B)) :
    IsIso ((systemRefinement l E k X Y f w).app
      ((coordinates l E X.scheme).inverse.obj B)) := by
  apply (R.isIso_iff_evaluations _).2
  intro n
  apply systemRefinementEvaluation_isIso l E k X Y f w P V _ n
  obtain ⟨H, hH, ⟨e⟩⟩ := hB n
  exact ⟨H, hH, ⟨e ≪≫ (V.proEvaluation.evaluation n).mapIso
    ((coordinates l E X.scheme).counitIso.app B).symm⟩⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] systemRefinement coordinates in
/-- Invertibility on bounded-below etale-origin systems; this detects invertibility,
not equality of unrelated system maps. Source: Stacks 0F7B; node proof Step 1
(blueprint: lem-pur-reconstructed-pair-refinement-coherence).
Proof: the uniquely normalized beta transports the intrinsic ringed-system clopen
mate and proper compositor. Its evaluations are the finite constant-ring normalized
proper/open comparisons. The coefficient rings are finite and the origin supplies
bounded-below etale inputs at every level. Strict-tower proper/open calculus makes
each evaluation invertible. Conservative system evaluations detect invertibility. -/
theorem systemDown_isIso {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (_hB : D₁.transport.siteX.Origin B) : IsIso ((systemDown D₁ D₂ w).app B) := by
  have h := intrinsic_isIso ((C.coefficient E).reduction Y.scheme) w D₁.strict.PX
    D₁.transport.siteX B _hB.2
  exact conjugate_isIso (coordinates l E X.scheme) (coordinates l E Y.scheme).functor
    D₂.transport.compact.functor D₁.transport.compact.functor
    (systemSupport l E d) (systemSupport l E c)
    (beta l E D₂.strict D₂.brown D₂.finite D₂.transport)
    (beta l E D₁.strict D₁.brown D₁.finite D₁.transport)
    (systemRefinement l E k X Y f w) B h

private def sameDerivedImage
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (G H : DerivedCategory A ⥤ DerivedCategory B)
    (g : DerivedCategory.Q ⋙ G ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (h : DerivedCategory.Q ⋙ H ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : G ≅ H :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (DerivedCategory.Q ⋙ G) (DerivedCategory.Q ⋙ H) G H (g ≪≫ h.symm)

private theorem exactImageBound
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (K : DerivedCategory A) (a : ℤ) [K.IsGE a] : (FD.obj K).IsGE a := by
  let e := sameDerivedImage F FD F.mapDerivedCategory fac F.mapDerivedCategoryFactors
  have := F.isGE_mapDerivedCategory_obj K a
  exact DerivedCategory.TStructure.t.isGE_of_iso (e.app K).symm a

private theorem siteOrigin_transfer
    {O : Type (u + 1)} [CommRing O] {t : O} {T : Scheme.{u}}
    {P Q : StrictEtaleEvaluation T O t}
    (V : BrownTowerComparison.Site T O t P) (W : BrownTowerComparison.Site T O t Q)
    (M : DerivedCategory (BrownTowerComparison.ProSystem T O t))
    (hM : W.Origin M) : V.Origin M := by
  refine ⟨hM.1, ?_⟩
  intro n
  obtain ⟨H, hH, ⟨e⟩⟩ := hM.2 n
  let ev := sameDerivedImage
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology T) n)
    (W.proEvaluation.evaluation n) (V.proEvaluation.evaluation n)
    (W.proEvaluation.evaluationFactors n) (V.proEvaluation.evaluationFactors n)
  let pro := sameDerivedImage
    (BrownTowerComparison.levelRealization (Scheme.ProEt.topology T) O t n)
    (V.realization n).derived (W.realization n).derived
    (V.realization n).factors (W.realization n).factors
  let et := sameDerivedImage
    (BrownTowerComparison.levelRealization T.smallEtaleTopology O t n)
    (V.etaleRealization n).derived (W.etaleRealization n).derived
    (V.etaleRealization n).factors (W.etaleRealization n).factors
  have := (V.realization n).equivalence
  let a : (V.realization n).derived.obj
        ((V.comparison.evaluation.level n).inverse.obj H) ≅
      (V.realization n).derived.obj ((W.comparison.evaluation.level n).inverse.obj H) :=
    (V.inverseLevel n).app H ≪≫
      (FiniteCoefficientAdjoints.nu (BrownTowerComparison.Ring O t n) T).mapIso
        (et.app H) ≪≫
      ((W.inverseLevel n).app H).symm ≪≫
      (pro.app ((W.comparison.evaluation.level n).inverse.obj H)).symm
  exact ⟨H, hH, ⟨(V.realization n).derived.preimageIso a ≪≫ e ≪≫ ev.app M⟩⟩

/-- The other Brown output lies in the same intrinsic bounded-below origin domain.
Source: blueprint integral-adjunction hypotheses; node proof Step 4
(blueprint: lem-pur-reconstructed-pair-refinement-coherence).
Proof: Brown transport bounds its output using the supplied interval and finite Tor
bounds. It is the exact site inverse image of that bounded-below etale output.
The two site packages express the same intrinsic etale-origin property: their
section-normalized site equivalences and adjunction counits transport this witness. -/
theorem output_origin {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (L : CondensedERealization.Integral l E Y.scheme) (A₂ : D₂.Supplied L) :
    D₁.transport.siteX.Origin (D₂.output L) := by
  apply siteOrigin_transfer D₁.transport.siteX D₂.transport.siteX
  have := D₂.transport.finite
  let N := D₂.brown.right.obj (D₂.transport.siteY.direct.obj
    ((PurIntegralRepresentingPair.reduction l E Y.scheme
      ((C.coefficient E).reduction Y.scheme)).obj L.obj))
  obtain ⟨a, ha⟩ := (D₂.pair L A₂).lowerBound
  have hb := D₂.normalized.bound _ (D₂.pair L A₂).origin
    (D₂.pair L A₂).normalized (D₂.pair L A₂).finiteTor a ha
  refine ⟨⟨a, hb.2.1⟩, ?_⟩
  intro n
  have hN : N.IsGE a := hb.1
  have := hN
  have := (SheafOfModules.coefficientEvaluation_exact
    (J := X.scheme.smallEtaleTopology) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).1
  have := (SheafOfModules.coefficientEvaluation_exact
    (J := X.scheme.smallEtaleTopology) (O := integralExceptionalIntegers l E)
    (ell := integralExceptionalUniformizer l E) n).2
  refine ⟨(D₂.strict.PX.evaluation n).obj N, ⟨a, ?_⟩, ?_⟩
  · exact exactImageBound _ _ (D₂.strict.PX.evaluationFactors n) N a
  · exact ⟨((D₂.transport.siteX.comparison.evaluation.inverseEvaluation n).app N).symm⟩

/-- The actual forward system refinement, inverted only on its stated origin domain.
Source: Stacks 0F7B; node proof Step 1
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def systemComparison {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₁.transport.siteX.Origin B) :=
  letI := systemDown_isIso D₁ D₂ w B hB
  (asIso ((systemDown D₁ D₂ w).app B)).symm

/-- Counit-preserving Brown mate, formed by the actual transported Brown Hom bijection.
Source: categorical uniqueness proof, Transposes; node proof Step 4
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def mate {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) : D₂.output L ⟶ D₁.output L :=
  (D₁.transport.hom _ (D₁.pair L A₁).origin (D₁.pair L A₁).normalized
    (D₁.pair L A₁).finiteTor (D₁.pair L A₁).lowerBound _
    (output_origin D₁ D₂ L A₂)).symm
      ((systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom ≫
        D₂.counit L A₂)

variable (l E k C X Y f)

variable {l E k C X Y f}

/-- Comparison through a supplied common refinement in the ordinary derived system
category. Both inverse maps are inverted on the intrinsic origin domain.
Source: Stacks 0ATU, 0F7J; node proof Step 2
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def systemCommon {c d e : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₀ : At l E k C X Y f e) (r : e.Refinement c) (s : e.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₀.transport.siteX.Origin B) :=
  (systemComparison D₀ D₁ r B hB).symm ≪≫ systemComparison D₀ D₂ s B hB

variable (l E k C X Y f)

/-- Comparison through an arbitrary dominating compactification, with no chosen
common refinement. Source: Stacks 0ATU and 0F7J; node proof Step 2
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def commonComparison {c d e : Compactification f}
    (r : e.Refinement c) (s : e.Refinement d) :
    support l E k C X Y f c ≅ support l E k C X Y f d :=
  (comparison l E k C X Y f r).symm ≪≫ comparison l E k C X Y f s

end WeilConjectures.ReconstructedPairRefinement
