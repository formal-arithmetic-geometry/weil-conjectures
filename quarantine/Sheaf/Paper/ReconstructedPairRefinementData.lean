/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.PurIntegralRepresentingPair
public import Sheaf.Paper.RingedRefinementCoefficientSquare
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.RefinementFiniteOriginEvaluation

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

/-- The reconstructed counit is the image of identity under the published Hom bijection.
Source: blueprint integral-adjunction unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def At.trace {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) (A : D.Supplied L) :
    (support l E k C X Y f c).obj A.object ⟶ L :=
  D.pairs.hom L A A.object (𝟙 A.object)

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

/-- The reconstruction of an actual supplied-system map is its actual total-limit map.
Source: blueprint integral-adjunction naturality; node proof Step 5
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def reconstructedMap {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (s : A₂.system ⟶ A₁.system) :
    A₂.object ⟶ A₁.object :=
  ObjectProperty.homMk ((PurIntegralRepresentingPair.totalLimit l E X.scheme).map s)


variable (l E k C X Y f)

/-- Realization of an integral object in the actual bounded condensed E category.
Source: blueprint sk-prop-sp-rational; node proof Step 8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def realize (T : CondensedERealization.Base k) :=
  pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
    ((C.coefficient E).realization.atObject T).realization.functor

/-- The original condensed proper/open composite restricted to bounded constructibles.
Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def fieldSupport (c : Compactification f) :
    CondensedERealization.Constructible E X.scheme ⥤
      CondensedERealization.Constructible E Y.scheme :=
  ObjectProperty.lift (boundedConstructible (CondensedERealization.Coefficient E Y.scheme))
    ((boundedConstructible (CondensedERealization.Coefficient E X.scheme)).ι ⋙
      ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousCoefficientRingObj E) c)
    (fun K ↦ ((C.coefficient E).atCompactification X Y f c).field_preserves K.obj K.property)

/-- The inverse of the dependency's normalized condensed refinement, on the same full
bounded constructible categories. Source: blueprint sk-thm-purity-transport Step 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def fieldComparison {c d : Compactification f} (w : c.Refinement d) :
    fieldSupport l E k C X Y f c ≅ fieldSupport l E k C X Y f d :=
  letI := (C.refinement E X Y f w).field_invertible
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((asIso (fieldRefinement (Profinite.continuousCoefficientRingObj E) w)).symm.app K))
    (fun v ↦ ObjectProperty.hom_ext _
      ((inv (fieldRefinement (Profinite.continuousCoefficientRingObj E) w)).naturality v))

/-- The actual E counit obtained by rationalization and the specified realization
comparison, using its inverse in the required direction.
Source: blueprint sk-prop-sp-rational; node proof Step 8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def fieldTrace (c : Compactification f)
    {M : CondensedERealization.Integral l E X.scheme}
    {L : CondensedERealization.Integral l E Y.scheme}
    (t : (support l E k C X Y f c).obj M ⟶ L) :
    (fieldSupport l E k C X Y f c).obj ((realize l E k C X).obj M) ⟶
      (realize l E k C Y).obj L :=
  ObjectProperty.homMk
    (((C.coefficient E).atCompactification X Y f c).realization.inv.app
      (ScalarLocalization.mk M) ≫ ((realize l E k C Y) ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).map t)

/-- Integral scalar extension of a trace with the prescribed compact-support tensor
comparison. It uses the actual completed scalar extension, including ramified extensions.
Source: blueprint coefficient transport; node proof Step 7
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def scalarTrace (H : Type u) [NormedField H] [NormedAlgebra ℚ_[l] H]
    [FiniteDimensional ℚ_[l] H] (i : E →ₐ[ℚ_[l]] H) (c : Compactification f)
    {M : CondensedERealization.Integral l E X.scheme}
    {L : CondensedERealization.Integral l E Y.scheme}
    (t : (support l E k C X Y f c).obj M ⟶ L) :
    (support l H k C X Y f c).obj ((integralScalar l E H i k X).obj M) ⟶
      (integralScalar l E H i k Y).obj L :=
  (C.finite E H i X Y f c).comparison.inv.app M ≫ (integralScalar l E H i k Y).map t

/-- The finite-extension-valued closure category and its original support functor.
Source: blueprint sk-thm-sp-qbar; filtered two-colimit theorem
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def omegaSupport (c : Compactification f) :
    ProEtale.PadicAlgClConstructible X.scheme l ⥤
      ProEtale.PadicAlgClConstructible Y.scheme l :=
  ObjectProperty.lift (boundedConstructible (ProEtale.padicAlgClRingObj Y.scheme l))
    ((boundedConstructible (ProEtale.padicAlgClRingObj X.scheme l)).ι ⋙
      ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj.{u} l) c)
    (fun K ↦ omegaSupport_preserves l k X Y f c K.obj K.property)

/-- The specified finite-valued closure scalar extension on bounded constructibles.
Source: blueprint sk-thm-sp-qbar; node proof Step 8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def toOmega (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (T : CondensedERealization.Base k) :
    CondensedERealization.Constructible E T.scheme ⥤
      ProEtale.PadicAlgClConstructible T.scheme l :=
  ObjectProperty.lift (boundedConstructible (ProEtale.padicAlgClRingObj T.scheme l))
    ((boundedConstructible (CondensedERealization.Coefficient E T.scheme)).ι ⋙
      omegaScalar l E a T.scheme)
    (fun K ↦ omegaScalar_preserves l E a T.scheme K)

/-- Forward closure refinement, the inverse of the intrinsic normalized map.
Source: blueprint sk-thm-sp-qbar and sk-thm-purity-transport Step 3
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def omegaComparison {c d : Compactification f} (w : c.Refinement d) :
    omegaSupport l k X Y f c ≅ omegaSupport l k X Y f d :=
  letI := omegaRefinement_isIso l k X Y f w
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((asIso (fieldRefinement (Profinite.padicAlgClRingObj.{u} l) w)).symm.app K))
    (fun v ↦ ObjectProperty.hom_ext _
      ((inv (fieldRefinement (Profinite.padicAlgClRingObj.{u} l) w)).naturality v))

/-- Scalar extension of a condensed E counit through the actual closure projection.
Source: blueprint sk-thm-sp-qbar; node proof Step 8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
def omegaTrace (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (c : Compactification f)
    {M : CondensedERealization.Constructible E X.scheme}
    {L : CondensedERealization.Constructible E Y.scheme}
    (t : (fieldSupport l E k C X Y f c).obj M ⟶ L) :
    (omegaSupport l k X Y f c).obj ((toOmega l E k a X).obj M) ⟶
      (toOmega l E k a Y).obj L :=
  letI := omegaProjection_isIso l E k a X Y f c M
  ObjectProperty.homMk
    (inv ((condensedProjection (omegaMap l E a) c).app M.obj) ≫
      (omegaScalar l E a Y.scheme).map t.hom)

variable {l E k C X Y f}

/-- All counit and Hom equations for one actual system isomorphism. The last clause
uses specified right adjoints of the original closure support functors; its maps are
adjunction transposes and the Mathlib counit-preserving conjugate mate.
Source: categorical uniqueness proof, Transposes/Naturality/Uniqueness; node Steps 4--8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
structure Equations {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (s : A₂.system ≅ A₁.system) : Prop where
  counit : (support l E k C X Y f c).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom) ≫
    D₁.trace L A₁ = (comparison l E k C X Y f w).hom.app A₂.object ≫ D₂.trace L A₂
  hom : ∀ (K : CondensedERealization.Integral l E X.scheme) (h : K ⟶ A₂.object),
    D₁.pairs.hom L A₁ K (h ≫ reconstructedMap D₁ D₂ L A₁ A₂ s.hom) =
      (comparison l E k C X Y f w).hom.app K ≫ D₂.pairs.hom L A₂ K h
  scalar : ∀ (H : Type u) [NormedField H] [NormedAlgebra ℚ_[l] H]
    [FiniteDimensional ℚ_[l] H] (i : E →ₐ[ℚ_[l]] H),
    (support l H k C X Y f c).map
        ((integralScalar l E H i k X).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      scalarTrace l E k C X Y f H i c (D₁.trace L A₁) =
    (comparison l H k C X Y f w).hom.app
        ((integralScalar l E H i k X).obj A₂.object) ≫
      scalarTrace l E k C X Y f H i d (D₂.trace L A₂)
  field : (fieldSupport l E k C X Y f c).map
      ((realize l E k C X).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      fieldTrace l E k C X Y f c (D₁.trace L A₁) =
    (fieldComparison l E k C X Y f w).hom.app ((realize l E k C X).obj A₂.object) ≫
      fieldTrace l E k C X Y f d (D₂.trace L A₂)
  field_hom : ∀ (K : CondensedERealization.Constructible E X.scheme)
    (h : K ⟶ (realize l E k C X).obj A₂.object),
    (fieldSupport l E k C X Y f c).map
        (h ≫ (realize l E k C X).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      fieldTrace l E k C X Y f c (D₁.trace L A₁) =
    (fieldComparison l E k C X Y f w).hom.app K ≫
      (fieldSupport l E k C X Y f d).map h ≫ fieldTrace l E k C X Y f d (D₂.trace L A₂)
  omega : ∀ a : E →ₐ[ℚ_[l]] PadicAlgCl l,
    (omegaSupport l k X Y f c).map
        (((realize l E k C X) ⋙ toOmega l E k a X).map
          (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      omegaTrace l E k C X Y f a c (fieldTrace l E k C X Y f c (D₁.trace L A₁)) =
    (omegaComparison l k X Y f w).hom.app
        (((realize l E k C X) ⋙ toOmega l E k a X).obj A₂.object) ≫
      omegaTrace l E k C X Y f a d (fieldTrace l E k C X Y f d (D₂.trace L A₂))
  omega_hom : ∀ (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (K : ProEtale.PadicAlgClConstructible X.scheme l)
    (h : K ⟶ ((realize l E k C X) ⋙ toOmega l E k a X).obj A₂.object),
    (omegaSupport l k X Y f c).map
        (h ≫ ((realize l E k C X) ⋙ toOmega l E k a X).map
          (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      omegaTrace l E k C X Y f a c (fieldTrace l E k C X Y f c (D₁.trace L A₁)) =
    (omegaComparison l k X Y f w).hom.app K ≫ (omegaSupport l k X Y f d).map h ≫
      omegaTrace l E k C X Y f a d (fieldTrace l E k C X Y f d (D₂.trace L A₂))
  transpose : ∀ (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (J₁ J₂ : ProEtale.PadicAlgClConstructible Y.scheme l ⥤
      ProEtale.PadicAlgClConstructible X.scheme l)
    (adj₁ : omegaSupport l k X Y f c ⊣ J₁) (adj₂ : omegaSupport l k X Y f d ⊣ J₂),
    (((realize l E k C X) ⋙ toOmega l E k a X).map
      (reconstructedMap D₁ D₂ L A₁ A₂ s.hom)) ≫
      adj₁.homEquiv _ _
        (omegaTrace l E k C X Y f a c (fieldTrace l E k C X Y f c (D₁.trace L A₁))) =
    adj₂.homEquiv _ _
        (omegaTrace l E k C X Y f a d (fieldTrace l E k C X Y f d (D₂.trace L A₂))) ≫
      (conjugateEquiv adj₂ adj₁ (omegaComparison l k X Y f w).hom).app
        (((realize l E k C Y) ⋙ toOmega l E k a Y).obj L)


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

/-- The complete coherence assertion. All its fields are conclusions: no counit,
Hom, mate, refinement, coefficient or realization equation is assumed.
Source: current blueprint categorical uniqueness proof and purity transport Steps 2--4;
Stacks 0F7B--0F7D, 0F7J, 0ATU; node proof Steps 1--8
(blueprint: lem-pur-reconstructed-pair-refinement-coherence). -/
structure Coherence : Prop where
  system_id : ∀ (c : Compactification f) (D : At l E k C X Y f c),
    systemDown D D (Compactification.Refinement.id c) = 𝟙 _
  system_comp : ∀ (c d e : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (D₃ : At l E k C X Y f e)
    (r : c.Refinement d) (s : d.Refinement e),
    systemDown D₁ D₃ (r.comp s) = systemDown D₂ D₃ s ≫ systemDown D₁ D₂ r
  system_common_independent : ∀ (c d e e' : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₀ : At l E k C X Y f e) (D₀' : At l E k C X Y f e')
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₀.transport.siteX.Origin B) (hB' : D₀'.transport.siteX.Origin B),
    systemCommon D₁ D₂ D₀ r s B hB = systemCommon D₁ D₂ D₀' r' s' B hB'
  system_cocycle : ∀ (c d e h : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₃ : At l E k C X Y f e) (D₀ : At l E k C X Y f h)
    (r₁ : h.Refinement c) (r₂ : h.Refinement d) (r₃ : h.Refinement e)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₀.transport.siteX.Origin B),
    systemCommon D₁ D₂ D₀ r₁ r₂ B hB ≪≫ systemCommon D₂ D₃ D₀ r₂ r₃ B hB =
      systemCommon D₁ D₃ D₀ r₁ r₃ B hB
  integral_id : ∀ c : Compactification f,
    comparison l E k C X Y f (Compactification.Refinement.id c) = Iso.refl _
  integral_comp : ∀ (c d e : Compactification f) (r : c.Refinement d) (s : d.Refinement e),
    comparison l E k C X Y f (r.comp s) =
      comparison l E k C X Y f r ≪≫ comparison l E k C X Y f s
  common_independent : ∀ (c d e e' : Compactification f)
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d),
    commonComparison l E k C X Y f r s = commonComparison l E k C X Y f r' s'
  cocycle : ∀ (c d e a b h : Compactification f)
    (r₁ : a.Refinement c) (r₂ : a.Refinement d)
    (s₂ : b.Refinement d) (s₃ : b.Refinement e)
    (t₁ : h.Refinement c) (t₃ : h.Refinement e),
    commonComparison l E k C X Y f r₁ r₂ ≪≫ commonComparison l E k C X Y f s₂ s₃ =
      commonComparison l E k C X Y f t₁ t₃
  reduction : ∀ (c d : Compactification f) (w : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme),
    (integralReduction l E k Y ((C.coefficient E).reduction Y.scheme)).map
        ((comparison l E k C X Y f w).hom.app K) ≫
      (alpha l E d (C.coefficient E).reduction
        ((C.coefficient E).atCompactification X Y f d).integral).app K ≫
      (systemRefinement l E k X Y f w).app
        ((integralReduction l E k X ((C.coefficient E).reduction X.scheme)).obj K) =
    (alpha l E c (C.coefficient E).reduction
      ((C.coefficient E).atCompactification X Y f c).integral).app K
  mate_counit : ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L),
    D₁.transport.compact.functor.map (mate D₁ D₂ w L A₁ A₂) ≫ D₁.counit L A₁ =
      (systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom ≫
        D₂.counit L A₂
  mate_iso : ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L), IsIso (mate D₁ D₂ w L A₁ A₂)
  mate_comp : ∀ (c d e : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (D₃ : At l E k C X Y f e)
    (r : c.Refinement d) (s : d.Refinement e)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (A₃ : D₃.Supplied L),
    mate D₁ D₃ (r.comp s) L A₁ A₃ = mate D₂ D₃ s L A₂ A₃ ≫ mate D₁ D₂ r L A₁ A₂
  pairs : ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (s : A₂.system ≅ A₁.system),
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂ →
    Equations D₁ D₂ w L A₁ A₂ s
  single_degree : ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (r : ℤ)
    (s : A₂.system ≅ A₁.system),
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsLE r) →
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsLE r) →
    (∀ n : ℕ, (D₁.transport.siteX.proEvaluation.evaluation n).map
        (s.hom ≫ (D₁.pair L A₁).theta.hom) =
      (D₁.transport.siteX.proEvaluation.evaluation n).map
        ((D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂)) →
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂
  common_pair_counit : ∀ (c d e : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₀ : At l E k C X Y f e) (r : e.Refinement c) (s : e.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (A₀ : D₀.Supplied L)
    (s₁ : A₁.system ≅ A₀.system) (s₂ : A₂.system ≅ A₀.system),
    s₁.hom ≫ (D₀.pair L A₀).theta.hom =
      (D₁.pair L A₁).theta.hom ≫ mate D₀ D₁ r L A₀ A₁ →
    s₂.hom ≫ (D₀.pair L A₀).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₀ D₂ s L A₀ A₂ →
    (support l E k C X Y f c).map
        (reconstructedMap D₁ D₂ L A₁ A₂ (s₂ ≪≫ s₁.symm).hom) ≫ D₁.trace L A₁ =
      (commonComparison l E k C X Y f r s).hom.app A₂.object ≫ D₂.trace L A₂
  scalar_identity : ∀ (c : Compactification f)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (t : (support l E k C X Y f c).obj M ⟶ L),
    (support l E k C X Y f c).map
        ((integralScalarId l E k X).hom.app M) ≫ t =
      scalarTrace l E k C X Y f E (AlgHom.id ℚ_[l] E) c t ≫
        (integralScalarId l E k Y).hom.app L
  scalar_transitive : ∀
    (H H' : Type u) [NormedField H] [NormedField H']
    [NormedAlgebra ℚ_[l] H] [NormedAlgebra ℚ_[l] H']
    [FiniteDimensional ℚ_[l] H] [FiniteDimensional ℚ_[l] H']
    (i : E →ₐ[ℚ_[l]] H) (j : H →ₐ[ℚ_[l]] H')
    (c : Compactification f)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (t : (support l E k C X Y f c).obj M ⟶ L),
    (support l H' k C X Y f c).map
        ((integralScalarComp l E H H' i j k X).hom.app M) ≫
      scalarTrace l E k C X Y f H' (j.comp i) c t =
    scalarTrace l H k C X Y f H' j c (scalarTrace l E k C X Y f H i c t) ≫
      (integralScalarComp l E H H' i j k Y).hom.app L

end WeilConjectures.ReconstructedPairRefinement
