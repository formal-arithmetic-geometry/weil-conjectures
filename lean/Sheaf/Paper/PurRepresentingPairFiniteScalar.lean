module

public import Sheaf.Paper.PurIntegralRepresentingPair
public import Sheaf.Paper.IntegralUniformCoefficient
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompactSupportCoefficientModels
public import Sheaf.Paper.ExceptionalProEtaleRealization
public import Sheaf.Paper.FiniteCoefficientAdjointComparisons
public import Sheaf.Paper.SfCompletedScalarComparisonData
import Sheaf.CategoryTheory.ConstantRingModuleSheaves

/-! # Rational and finite scalar extension of reconstructed representing pairs

Source: current blueprint sec-smooth-purity/sk-prop-sp-rational, localized Hom display,
and sk-thm-sp-qbar, field transitions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension).
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
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
open WeilConjectures.CompactSupportCondensedRealization
open WeilConjectures.PurIntegralRepresentingPair
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
attribute [local instance] base_noetherian
namespace WeilConjectures.PurRepresentingPairFiniteScalar

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))] (c : Compactification f)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reduction into constant quotient coefficients, normalized by actual adjunctions.
Source: blueprint finite-extension supplement Step 3
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteReductionChart (T : Scheme.{u})
    (R : CoefficientDerivedSystemCalculus l E T) (q : ℕ) :
    (purCoefficientModel l E T).functor ⋙ R.reduction ⋙
        coefficientSequenceDerivedEvaluation l E T q ≅
      (purCoefficientModel l E T).functor ⋙
        pbcDerivedExtend
          (PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T) := by
  have e0 : coefficientFiniteDerivedExtension l E T q ≅
      pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T q) :=
    Adjunction.leftAdjointUniq (coefficientFiniteAdjunction l E T q)
      (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T q))
  have hp : PurCompactSupport.projection l E (q+1) (Nat.succ_le_succ (Nat.zero_le q)) T =
      completedIntegralCommRingProjectionUnrestricted l E T q := by
    simp only [PurCompactSupport.projection]
    rfl
  rw [hp]
  exact Functor.isoWhiskerLeft (purCoefficientModel l E T).functor
    (R.reductionEvaluation q ≪≫ e0)

/-- The actual Brown and integral-pair data at one coefficient field.
Source: blueprint integral Hom display
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
structure Context (C : CoefficientData l E k) where
  strict : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c
  brown : EtaleTowerBrownAdjunction strict
  evaluation : BrownTowerComparison.FiniteEvaluation strict brown
  transport : BrownTowerComparison.TransportData strict brown evaluation
  transport_laws : BrownTowerComparison.Transport strict brown evaluation transport
    (finite := transport.finite)
  pairs : PublishedFamily l E strict brown evaluation transport C.reduction
    (C.atCompactification X Y f c).integral transport_laws

/-- Actual reduction into finite fixed-module coordinates; n denotes exponent n+1.
Source: blueprint integral Hom chain, ordinary-system refinement
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def levelX {C : CoefficientData l E k} (B : Context l E k X Y f c C) (n : ℕ) :
    PbcCompletedDerived X.scheme (pbcIntegralDatum l E) ⥤
      FiniteCoefficientAdjoints.D
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) X.scheme :=
  reduction l E X.scheme (C.reduction X.scheme) ⋙
    B.transport.siteX.proEvaluation.evaluation n ⋙ (B.transport.siteX.realization n).derived

/-- The target version of the same actual reduction.
Source: blueprint integral Hom chain
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def levelY {C : CoefficientData l E k} (B : Context l E k X Y f c C) (n : ℕ) :
    PbcCompletedDerived Y.scheme (pbcIntegralDatum l E) ⥤
      FiniteCoefficientAdjoints.D
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) Y.scheme :=
  reduction l E Y.scheme (C.reduction Y.scheme) ⋙
    B.transport.siteY.proEvaluation.evaluation n ⋙ (B.transport.siteY.realization n).derived

/-- Finite compact-support projection from the actual reduction/limit counit alpha.
The fixed coordinate beta and compact evaluation comparison determine every factor.
Source: blueprint unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def levelProjection {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (K : CondensedERealization.Integral l E X.scheme) (n : ℕ) :
    (levelY l E k X Y f c B n).obj
        ((integralSupport l E c C.reduction
          (C.atCompactification X Y f c).integral).obj K).obj ⟶
      (FiniteCoefficientAdjoints.lower
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) c).obj
        ((levelX l E k X Y f c B n).obj K.obj) :=
  (levelY l E k X Y f c B n).map
      ((supportPresentation l E (C.reduction X.scheme) B.strict B.brown B.evaluation
        B.transport (PurIntegralSupportComparison.beta l E B.strict B.brown B.evaluation
          B.transport)).inv.app K.obj) ≫
    (B.transport.siteY.realization n).derived.map
      ((B.transport.siteY.proEvaluation.evaluation n).map
        (PurIntegralRepresentingPair.alpha l E (C.reduction X.scheme) (C.reduction Y.scheme)
          B.strict B.brown B.evaluation B.transport K.obj)) ≫
    (B.transport.compactEvaluation n).hom.app
      ((reduction l E X.scheme (C.reduction X.scheme)).obj K.obj)

/-- The recorded finite adjunction at the actual quotient coefficient ring.
Source: blueprint finite coefficient adjunction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteAdjunction {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (q : ℕ) :=
  @FiniteCoefficientAdjoints.AdjointDatum X.scheme Y.scheme f
    (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) q) _ (B.transport.finite q) _ _ c

/-- Invertibility of the specified finite compact-support projection.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def IsLevelProjectionIso {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (K : CondensedERealization.Integral l E X.scheme) (q : ℕ) : Prop :=
  IsIso (levelProjection l E k X Y f c B K q)

/-- The finite constructible finite-Tor domain in the exact evaluation coordinates.
Source: blueprint finite coefficient domains
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteDomainX {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (K : CondensedERealization.Integral l E X.scheme) (q : ℕ) : Prop :=
  FiniteCoefficientAdjoints.ctf _ X.scheme ((levelX l E k X Y f c B q).obj K.obj)

/-- The corresponding finite constructible finite-Tor domain on the target.
Source: blueprint finite coefficient domains
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteDomainY {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (K : CondensedERealization.Integral l E Y.scheme) (q : ℕ) : Prop :=
  FiniteCoefficientAdjoints.ctf _ Y.scheme ((levelY l E k X Y f c B q).obj K.obj)

/-- The finite transpose is formed with the actual finite adjunction and inverse
of the canonical projection. The isomorphism proof supplies no extra map.
Source: blueprint finite-extension supplement, transpose of the extended counit
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteTranspose {C : CoefficientData l E k} (B : Context l E k X Y f c C)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L) (n : ℕ)
    (d : FiniteAdjunction l E k X Y f c B n)
    (hM : FiniteDomainX l E k X Y f c B M n)
    (hL : FiniteDomainY l E k X Y f c B L n)
    (hp : IsLevelProjectionIso l E k X Y f c B M n) :
    (levelX l E k X Y f c B n).obj M.obj ⟶
      (@FiniteCoefficientAdjoints.upper X.scheme Y.scheme f
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) _ (B.transport.finite n) _ _ c).obj
        ((levelY l E k X Y f c B n).obj L.obj) :=
  haveI := B.transport.finite n
  haveI : IsIso (levelProjection l E k X Y f c B M n) := hp
  (d.adjunction.homEquiv
    ⟨(levelX l E k X Y f c B n).obj M.obj, hM⟩
    ⟨(levelY l E k X Y f c B n).obj L.obj, hL⟩)
    (ObjectProperty.homMk
      (inv (levelProjection l E k X Y f c B M n) ≫
        (levelY l E k X Y f c B n).map tau.hom)) |>.hom

/-- The actual quotient inclusion in the fixed lifted Brown ring coordinates.
The middle map sends an integer residue to its image residue, for every ramified
factorization, including a nonflat further quotient.
Source: blueprint finite-extension supplement, cofinal and further quotients
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteMap (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n m : ℕ) (h : m + 1 ≤ e * (n + 1)) :=
  (integralExceptionalQuotient l F m).symm.toRingHom.comp
    ((compactSupportCoefficientQuotient l E F i e he (n + 1) (m + 1) h).ulift.comp
      (integralExceptionalQuotient l E n).toRingHom)

/-- A scalar-extended trace is the specified compact-support comparison inverse
followed by extension of the original integral trace.
Source: blueprint finite-extension supplement, definition of t_S
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def scalarTrace (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (C : ComparisonFamily l k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (C.coefficient E).reduction
      ((C.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L) :=
  (C.finite E F i X Y f c).comparison.inv.app M ≫
    (integralScalar l E F i k Y).map tau

/-- Realize the integral object by the specified scalar-extension equivalence.
Source: blueprint rational Hom display
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def object (C : CoefficientData l E k) (T : CondensedERealization.Base k)
    (K : CondensedERealization.Integral l E T.scheme) :
    CondensedERealization.Constructible E T.scheme :=
  (C.realization.atObject T).realization.functor.obj (ScalarLocalization.mk K)

/-- The realized counit, using the inverse of the specified compact-support comparison.
Source: blueprint rational unit/counit paragraph
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def counit (C : CoefficientData l E k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L) :
    (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.continuousCoefficientRingObj E) c).obj (object l E k C X M).obj ⟶
        (object l E k C Y L).obj :=
  (C.atCompactification X Y f c).realization.inv.app (ScalarLocalization.mk M) ≫
    ((C.realization.atObject Y).realization.functor.map
      ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map tau)).hom

attribute [local irreducible] object counit

/-- The representing bijections on every condensed test object, with their exact counit.
Source: blueprint rational Hom display and counit paragraph
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def RationalPair (C : CoefficientData l E k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L) :=
  (hom : ∀ K : CondensedERealization.Constructible E X.scheme,
    (K.obj ⟶ (object l E k C X M).obj) ≃
      ((AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousCoefficientRingObj E) c).obj K.obj ⟶
          (object l E k C Y L).obj)) ×'
  (_formula : ∀ K h, hom K h =
    (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.continuousCoefficientRingObj E) c).map h ≫ counit l E k X Y f c C M L tau) ×'
  (_natural : ∀ (K K' : CondensedERealization.Constructible E X.scheme)
    (b : K'.obj ⟶ K.obj) h,
    hom K' (b ≫ h) =
      (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousCoefficientRingObj E) c).map b ≫ hom K h) ×'
  (hom (object l E k C X M) (𝟙 _) = counit l E k X Y f c C M L tau)

attribute [local semireducible] object counit

section
variable {l E k X Y f c}

/-- The representing bijection component, retaining every condensed test object.
Source: blueprint rational Hom display
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev RationalPair.hom {C : CoefficientData l E k}
    {M : CondensedERealization.Integral l E X.scheme}
    {L : CondensedERealization.Integral l E Y.scheme}
    {tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L}
    (Q : RationalPair l E k X Y f c C M L tau) := Q.1

end

/-- Ordinary fixed-ring coordinates retain all underlying sections.
Source: blueprint finite coefficient reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteOrdinary (W : Scheme.{u}) (n : ℕ) :=
  integralExceptionalLevel l E W n ⋙
    BrownTowerComparison.levelRealization (Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n

private def scalarRestrictionCancel
    {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ R)
    (h : a ≫ b = 𝟙 R) :
    SheafOfModules.restrictScalars b ⋙ SheafOfModules.restrictScalars a ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Tᵒᵖ) : (b.hom.app U).hom.comp (a.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app U).hom (b.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem scalarRestrictionEquivalence
    {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} a.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} a.hom)
    (SheafOfModules.restrictScalars a.inv)
    (scalarRestrictionCancel a.inv a.hom a.inv_hom_id).symm
    (scalarRestrictionCancel a.hom a.inv a.hom_inv_id)).isEquivalence_functor

private theorem levelRealization_equivalence (W : Scheme.{u}) (n : ℕ) :
    (BrownTowerComparison.levelRealization (Scheme.ProEt.topology W)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n).IsEquivalence := by
  let J := Scheme.ProEt.topology W
  let A := BrownTowerComparison.Ring (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) n
  let := Scheme.purTwistForgetPreservesSheafification W
  let a := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of A)
  let R := SheafOfModules.restrictScalars.{u + 1} a.inv
  have : R.IsEquivalence := scalarRestrictionEquivalence a.symm
  obtain ⟨⟨e, he, _⟩, _⟩ := constant_ring_module_sheaves J A
  have : (constantRingModuleRestriction J A).IsEquivalence := he ▸ e.isEquivalence_functor
  have hu : Functor.whiskerRight
      (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat RingCat) ≫ a.hom.hom =
      toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A)) := by
    dsimp only [a, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp W.ProEtᵒᵖ (CommRingCat.of A)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  let F := BrownTowerComparison.levelRealization J
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n
  have hs (M : coefficientLevelModules (J := J) (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n) (U : W.ProEtᵒᵖ) (r : A)
      (x : M.val.obj U) :
      r • (show ((R ⋙ constantRingModuleRestriction J A).obj M).obj.obj U from x) =
        r • (show (F.obj M).obj.obj U from x) := by
    have h := congrArg (fun f ↦ f.app U r) hu
    have hi := congrArg (fun f ↦ f.hom.app U) a.hom_inv_id
    change a.inv.hom.app U
      ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A))).app U r) • x =
      ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of A))).app U r) • x
    erw [← h]
    exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)
  let h : R ⋙ constantRingModuleRestriction J A ≅ F :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦
        ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext x; exact (hs M U r x).symm))
        (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  exact Functor.isEquivalence_of_iso h

/-- Exact equivalence of the explicit finite coordinate realization.
Source: blueprint finite coefficient reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension).
Proof: restriction along the quotient-ring equivalence changes no sections.
Restriction along the constant sheafification unit is an equivalence, with inverse
extending the constant action to locally constant sections by sheafification.
These two exact additive equivalences give the assertions. -/
theorem finiteOrdinary_properties (W : Scheme.{u}) (n : ℕ) :
    (finiteOrdinary l E W n).IsEquivalence ∧
      (finiteOrdinary l E W n).Additive ∧
      PreservesFiniteLimits (finiteOrdinary l E W n) ∧
      PreservesFiniteColimits (finiteOrdinary l E W n) := by
  have := levelRealization_equivalence l E W n
  have hE : (finiteOrdinary l E W n).IsEquivalence := by
    unfold finiteOrdinary
    infer_instance
  have hA : (finiteOrdinary l E W n).Additive := by
    unfold finiteOrdinary
    infer_instance
  exact ⟨hE, hA, inferInstance, inferInstance⟩

/-- The additive structure of the specified ordinary coordinates.
Source: blueprint finite reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
instance finiteOrdinary_additive (W : Scheme.{u}) (n : ℕ) :
    (finiteOrdinary l E W n).Additive :=
  (finiteOrdinary_properties l E W n).2.1

/-- Exactness of finite coordinates on kernels.
Source: blueprint finite reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
instance finiteOrdinary_limits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (finiteOrdinary l E W n) :=
  (finiteOrdinary_properties l E W n).2.2.1

/-- Exactness of finite coordinates on cokernels.
Source: blueprint finite reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
instance finiteOrdinary_colimits (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (finiteOrdinary l E W n) :=
  (finiteOrdinary_properties l E W n).2.2.2

/-- The equivalence structure belongs to the explicit sectionwise functor.
Source: blueprint finite reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
instance finiteOrdinary_equivalence (W : Scheme.{u}) (n : ℕ) :
    (finiteOrdinary l E W n).IsEquivalence :=
  (finiteOrdinary_properties l E W n).1

/-- Exact localization of the actual sectionwise finite coordinate equivalence.
Source: blueprint finite reduction
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteRealization (W : Scheme.{u}) (n : ℕ) :=
  (finiteOrdinary l E W n).mapDerivedCategory.asEquivalence

variable (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
  (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
  (n m : ℕ) (h : m + 1 ≤ e * (n + 1)) (W : Scheme.{u})

private theorem constantMap_unit
    {T : Type (u + 1)} [Category.{u} T] (J : GrothendieckTopology T)
    [HasWeakSheafify J CommRingCat.{u + 1}]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (q : A →+* B)
    (U : Tᵒᵖ) (a : A) :
    (((constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q)).hom.app U)
      ((toSheafify J ((Functor.const Tᵒᵖ).obj (CommRingCat.of A))).app U a) =
      (toSheafify J ((Functor.const Tᵒᵖ).obj (CommRingCat.of B))).app U (q a) := by
  exact (congrArg (fun f ↦ f.app U a)
    (toSheafify_naturality J ((Functor.const Tᵒᵖ).map (CommRingCat.ofHom q)))).symm

private theorem finiteRestriction_scalar (U : W.ProEtᵒᵖ)
    (a : BrownTowerComparison.Ring (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) n) :
    ((compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W).hom.app U)
      (((integralExceptionalRingMap l E W n).hom.app U)
        ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
            (integralExceptionalUniformizer l E) n)))).app U a)) =
    ((integralExceptionalRingMap l F W m).hom.app U)
      ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l F)
          (integralExceptionalUniformizer l F) m)))).app U
            (finiteMap l E F i e he n m h a)) := by
  change (((constantSheaf (Scheme.ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom
        (compactSupportCoefficientQuotient l E F i e he (n+1) (m+1) h).ulift)).hom.app U)
    ((((constantSheaf (Scheme.ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (integralExceptionalQuotient l E n).toRingHom)).hom.app U)
        ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
              (integralExceptionalUniformizer l E) n)))).app U a)) =
    (((constantSheaf (Scheme.ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (integralExceptionalQuotient l F m).toRingHom)).hom.app U)
        ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l F)
            (integralExceptionalUniformizer l F) m)))).app U
          (finiteMap l E F i e he n m h a))
  rw [constantMap_unit, constantMap_unit, constantMap_unit]
  congr 1
  exact ((integralExceptionalQuotient l F m).apply_symm_apply _).symm

/-- Identity on underlying additive sections uniquely determines the finite
restriction square. It rules out an automorphism twist of tensor balancing.
Source: blueprint finite-extension argument, actual quotient projections
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension).
Proof: the quotient map sends each integer residue to its image residue. The
quotient-coordinate equivalences and sheafification units commute with this map.
Both restricted actions on each section therefore agree. Identity on sections is
linear and natural, is its own inverse, and uniquely specifies the comparison. -/
theorem restrictionSquare_existsUnique :
    ∃! a : pbcRestrict
        (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W) ⋙
          finiteOrdinary l E W n ≅
        finiteOrdinary l F W m ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology W)
          (finiteMap l E F i e he n m h),
      ∀ (M : normalizedDVRModules l F W m) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        HEq ((a.hom.app M).hom.app U x) x := by
  let A := pbcRestrict
    (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W) ⋙
      finiteOrdinary l E W n
  let B := finiteOrdinary l F W m ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology W)
    (finiteMap l E F i e he n m h)
  have hs (M : normalizedDVRModules l F W m) (U : W.ProEtᵒᵖ)
      (r : BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) (x : M.val.obj U) :
      r • (show (A.obj M).obj.obj U from x) =
        r • (show (B.obj M).obj.obj U from x) := by
    change ((compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W).hom.app U)
        (((integralExceptionalRingMap l E W n).hom.app U)
          ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
              (integralExceptionalUniformizer l E) n)))).app U r)) • x =
      ((integralExceptionalRingMap l F W m).hom.app U)
        ((toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (BrownTowerComparison.Ring (integralExceptionalIntegers l F)
            (integralExceptionalUniformizer l F) m)))).app U
          (finiteMap l E F i e he n m h r)) • x
    exact congrArg (fun r ↦ r • x) (finiteRestriction_scalar l E F i e he n m h W U r)
  let a : A ≅ B := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦
      ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext x; exact (hs M U r x).symm))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  refine ⟨a, ?_, ?_⟩
  · intro M U x
    rfl
  · intro b hb
    apply Iso.ext
    ext M U x
    exact eq_of_heq (hb M U x)

/-- The unique identity-on-sections restriction square.
Source: blueprint actual quotient projections
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def restrictionSquare :=
  (restrictionSquare_existsUnique l E F i e he n m h W).choose

/-- Its exact localization, with all units inherited from ordinary restriction.
Source: blueprint finite-extension argument
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def derivedRestrictionSquare :
    pbcDerivedRestrict
        (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W) ⋙
          (finiteRealization l E W n).functor ≅
        (finiteRealization l F W m).functor ⋙
          Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W)
            (finiteMap l E F i e he n m h) := by
  letI := finiteOrdinary_additive l E W n
  letI := finiteOrdinary_additive l F W m
  letI := finiteOrdinary_limits l E W n
  letI := finiteOrdinary_limits l F W m
  letI := finiteOrdinary_colimits l E W n
  letI := finiteOrdinary_colimits l F W m
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionSquare l E F i e he n m h W) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Canonical tensor balancing in fixed finite coefficients: the left-adjoint
mate of the identity-on-sections scalar-restriction square.
Source: blueprint finite extension and quotient transposes
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def finiteScalarComparison :
    (finiteRealization l E W n).functor ⋙
        FiniteCoefficientAdjoints.tensor (finiteMap l E F i e he n m h) W ≅
      pbcDerivedExtend
        (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W) ⋙
          (finiteRealization l F W m).functor :=
  (conjugateIsoEquiv
    ((pbcDerivedScalarAdjunction
      (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W)).comp
      (finiteRealization l F W m).toAdjunction)
    ((finiteRealization l E W n).toAdjunction.comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        (Scheme.ProEt.topology W) (finiteMap l E F i e he n m h))))).symm
    (Functor.isoWhiskerLeft (finiteRealization l F W m).inverse
      (Functor.isoWhiskerLeft
        (pbcDerivedRestrict
          (compactSupportCoefficientQuotientSheaf l E F i e he (n+1) (m+1) h W))
          (finiteRealization l E W n).unitIso) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (finiteRealization l F W m).inverse
          (derivedRestrictionSquare l E F i e he n m h W))
        (finiteRealization l E W n).inverse ≪≫
      Functor.isoWhiskerRight (finiteRealization l F W m).counitIso
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W)
          (finiteMap l E F i e he n m h) ⋙ (finiteRealization l E W n).inverse))

attribute [local irreducible] finiteScalarComparison
  pbcDerivedScalarAdjunction coefficientFiniteAdjunction scalarReductionDerivedExtension
  PurCompactSupport.projection

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The ordinary coordinate comparison, fixed by equality of finite evaluation.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def coordinateOrdinaryComparison (T : Scheme.{u}) (q : ℕ) :=
  Functor.isoWhiskerRight
    (eqToIso (integralExceptionalCoordinatesEvaluation l E T q)).symm
    (BrownTowerComparison.levelRealization (Scheme.ProEt.topology T)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) q)

/-- The common ordinary complex in both finite-coordinate factorization charts.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def coordinateComplexTarget (T : Scheme.{u}) (q : ℕ)
    (Z : CochainComplex (coefficientSequenceModules l E T) ℤ) :=
  DerivedCategory.Q.obj
    ((Functor.mapHomologicalComplex
      (BrownTowerComparison.levelRealization (Scheme.ProEt.topology T)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) q) (.up ℤ)).obj
      (((coefficientEvaluation (J := Scheme.ProEt.topology T)
        (O := integralExceptionalIntegers l E)
        (ell := integralExceptionalUniformizer l E) q).mapHomologicalComplex (.up ℤ)).obj
          (((integralExceptionalCoordinates l E T).mapHomologicalComplex (.up ℤ)).obj Z)))

/-- The fixed finite-coordinate localization factor on a complex.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
@[no_expose] def coordinateLeftFactor (T : Scheme.{u}) (q : ℕ)
    (Z : CochainComplex (coefficientSequenceModules l E T) ℤ) :
    (finiteRealization l E T q).functor.obj
        ((coefficientSequenceDerivedEvaluation l E T q).obj (DerivedCategory.Q.obj Z)) ≅
      coordinateComplexTarget l E T q Z :=
  (finiteRealization l E T q).functor.mapIso
    ((coefficientSequenceEvaluation l E T q).mapDerivedCategoryFactors.app Z) ≪≫
  (finiteOrdinary l E T q).mapDerivedCategoryFactors.app
    (((coefficientSequenceEvaluation l E T q).mapHomologicalComplex (.up ℤ)).obj Z) ≪≫
  DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex
      (coordinateOrdinaryComparison l E T q) (.up ℤ)).app Z)

/-- The Brown-coordinate localization factor on the same complex.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
@[no_expose] def coordinateRightFactor (T : Scheme.{u})
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P) (q : ℕ)
    (Z : CochainComplex (coefficientSequenceModules l E T) ℤ) :=
  (V.realization q).derived.map ((V.proEvaluation.evaluation q).map
          ((integralExceptionalCoordinates l E T).mapDerivedCategoryFactors.hom.app Z)) ≫
        (V.realization q).derived.map
          ((V.proEvaluation.evaluationFactors q).hom.app
            (((integralExceptionalCoordinates l E T).mapHomologicalComplex (.up ℤ)).obj Z)) ≫
        (V.realization q).factors.hom.app
          (((coefficientEvaluation (J := Scheme.ProEt.topology T)
            (O := integralExceptionalIntegers l E)
            (ell := integralExceptionalUniformizer l E) q).mapHomologicalComplex (.up ℤ)).obj
              (((integralExceptionalCoordinates l E T).mapHomologicalComplex (.up ℤ)).obj Z))

attribute [local irreducible] finiteRealization

/-- Normalization of finite evaluation on every ordinary complex representative.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def IsCoordinateEvaluation (T : Scheme.{u})
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P) (q : ℕ)
    (a : (PurIntegralSupportComparison.coordinates l E T).functor ⋙
        V.proEvaluation.evaluation q ⋙ (V.realization q).derived ≅
      coefficientSequenceDerivedEvaluation l E T q ⋙ (finiteRealization l E T q).functor) :
    Prop :=
  ∀ Z : CochainComplex (coefficientSequenceModules l E T) ℤ,
    HEq (a.hom.app (DerivedCategory.Q.obj Z) ≫ (coordinateLeftFactor l E T q Z).hom)
      (coordinateRightFactor l E T P V q Z)

/-- Identity-on-sections evaluation descends uniquely to derived coordinates.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension).
Proof: the ordinary composite evaluates the sequence module and then restricts
its action, identically on all sections. Paste its localization factors on both
sides. Full faithfulness of precomposition with Q gives the unique isomorphism. -/
theorem coordinateEvaluation_existsUnique (T : Scheme.{u})
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P) (q : ℕ) :
    ∃! a : (PurIntegralSupportComparison.coordinates l E T).functor ⋙
        V.proEvaluation.evaluation q ⋙ (V.realization q).derived ≅
      coefficientSequenceDerivedEvaluation l E T q ⋙ (finiteRealization l E T q).functor,
      IsCoordinateEvaluation l E T P V q a := by
  sorry

/-- The uniquely normalized evaluation isomorphism.
Source: blueprint finite reductions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def coordinateEvaluation (T : Scheme.{u})
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P) (q : ℕ) :
    (PurIntegralSupportComparison.coordinates l E T).functor ⋙
        V.proEvaluation.evaluation q ⋙ (V.realization q).derived ≅
      coefficientSequenceDerivedEvaluation l E T q ⋙ (finiteRealization l E T q).functor :=
  (coordinateEvaluation_existsUnique l E T P V q).exists.choose

attribute [local irreducible] coordinateEvaluation finiteReductionChart

/-- Actual finite evaluation in its scalar-tensor chart.
Source: blueprint finite-extension supplement Step 3
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def levelChart (T : Scheme.{u}) (R : CoefficientDerivedSystemCalculus l E T)
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P) (q : ℕ) :=
  Functor.isoWhiskerLeft ((purCoefficientModel l E T).functor ⋙ R.reduction)
      (coordinateEvaluation l E T P V q) ≪≫
    Functor.isoWhiskerRight (finiteReductionChart l E T R q)
      (finiteRealization l E T q).functor

attribute [local irreducible] levelChart

/-- Balancing at any ramified quotient, using the actual tensor associators.
Source: blueprint finite-extension supplement Step 3
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def scalarLevel (C : ComparisonFamily l k) (T : CondensedERealization.Base k)
    (PE : StrictEtaleEvaluation T.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (PF : StrictEtaleEvaluation T.scheme (integralExceptionalIntegers l F)
      (integralExceptionalUniformizer l F))
    (VE : BrownTowerComparison.Site T.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) PE)
    (VF : BrownTowerComparison.Site T.scheme (integralExceptionalIntegers l F)
      (integralExceptionalUniformizer l F) PF)
    (K : CondensedERealization.Integral l E T.scheme) :
    ((reduction l F T.scheme ((C.coefficient F).reduction T.scheme) ⋙
      VF.proEvaluation.evaluation m ⋙ (VF.realization m).derived).obj
        ((integralScalar l E F i k T).obj K).obj) ≅
      (FiniteCoefficientAdjoints.tensor (finiteMap l E F i e he n m h) T.scheme).obj
        ((reduction l E T.scheme ((C.coefficient E).reduction T.scheme) ⋙
          VE.proEvaluation.evaluation n ⋙ (VE.realization n).derived).obj K.obj) :=
  (levelChart l F T.scheme ((C.coefficient F).reduction T.scheme) PF VF m).app
      ((integralScalar l E F i k T).obj K).obj ≪≫
    (finiteRealization l F T.scheme m).functor.mapIso
      ((pbcDerivedExtend
        (PurCompactSupport.projection l F (m+1)
          (Nat.succ_le_succ (Nat.zero_le m)) T.scheme)).mapIso
        ((scalarPresentation l E F i T.scheme).app K.obj) ≪≫
      (compactSupportCoefficientBalancedReduction l E F i e he (n+1) (m+1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Nat.succ_le_succ (Nat.zero_le m)) h T.scheme).app
          ((purCoefficientModel l E T.scheme).functor.obj K.obj)) ≪≫
    (finiteScalarComparison l E F i e he n m h T.scheme).symm.app
      ((pbcDerivedExtend
        (PurCompactSupport.projection l E (n+1)
          (Nat.succ_le_succ (Nat.zero_le n)) T.scheme)).obj
        ((purCoefficientModel l E T.scheme).functor.obj K.obj)) ≪≫
    (FiniteCoefficientAdjoints.tensor (finiteMap l E F i e he n m h) T.scheme).mapIso
      ((levelChart l E T.scheme ((C.coefficient E).reduction T.scheme) PE VE n).symm.app K.obj)

attribute [local irreducible] scalarLevel
variable {C : CoefficientData l E k} (B : Context l E k X Y f c C)
  (M : CondensedERealization.Integral l E X.scheme)
  (L : CondensedERealization.Integral l E Y.scheme)
  (tau : (integralSupport l E c C.reduction
    (C.atCompactification X Y f c).integral).obj M ⟶ L)

/-- Invertibility of the exact finite transpose, with all domain witnesses retained.
Source: blueprint finite-extension supplement Steps 4--5
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def IsFiniteTransposeIso (q : ℕ)
    (d : FiniteAdjunction l E k X Y f c B q)
    (hM : FiniteDomainX l E k X Y f c B M q)
    (hL : FiniteDomainY l E k X Y f c B L q)
    (hp : IsLevelProjectionIso l E k X Y f c B M q) : Prop :=
  IsIso (finiteTranspose l E k X Y f c B M L tau q d hM hL hp)

/-- Finite transposes with their constructible finite-Tor domains.
Source: blueprint finite-extension supplement Steps 1 and 4--5
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteData :=
  (datum : ∀ q : ℕ, FiniteAdjunction l E k X Y f c B q) ×'
  (hM : ∀ q, FiniteDomainX l E k X Y f c B M q) ×'
  (hL : ∀ q, FiniteDomainY l E k X Y f c B L q) ×'
  (hp : ∀ q, IsLevelProjectionIso l E k X Y f c B M q) ×'
  (∀ q, IsFiniteTransposeIso l E k X Y f c B M L tau q
    (datum q) (hM q) (hL q) (hp q))

/-- The actual finite adjunction transpose.
Source: blueprint finite-extension supplement
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteData.arrow (D : FiniteData l E k X Y f c B M L tau) (q : ℕ) :
    (levelX l E k X Y f c B q).obj M.obj ⟶
      (@FiniteCoefficientAdjoints.upper X.scheme Y.scheme f
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) q) _ (B.transport.finite q) _ _ c).obj
        ((levelY l E k X Y f c B q).obj L.obj) :=
  finiteTranspose l E k X Y f c B M L tau q
    (D.1 q) (D.2.1 q) (D.2.2.1 q) (D.2.2.2.1 q)

/-- Whole-system alpha before finite evaluation.
Source: blueprint actual-system transpose a_S
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def systemProjection :
    (reduction l E Y.scheme (C.reduction Y.scheme)).obj
        ((integralSupport l E c C.reduction
          (C.atCompactification X Y f c).integral).obj M).obj ⟶
      B.transport.compact.functor.obj
        ((reduction l E X.scheme (C.reduction X.scheme)).obj M.obj) :=
  (reduction l E Y.scheme (C.reduction Y.scheme)).map
    ((supportPresentation l E (C.reduction X.scheme) B.strict B.brown B.evaluation
      B.transport (PurIntegralSupportComparison.beta l E B.strict B.brown B.evaluation
        B.transport)).inv.app M.obj) ≫
    PurIntegralRepresentingPair.alpha l E (C.reduction X.scheme) (C.reduction Y.scheme)
      B.strict B.brown B.evaluation B.transport M.obj

/-- The actual reduced trace composed with inverse alpha.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def systemTrace (hp : IsIso (systemProjection l E k X Y f c B M)) :
    B.transport.compact.functor.obj
        ((reduction l E X.scheme (C.reduction X.scheme)).obj M.obj) ⟶
      (reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj :=
  haveI := hp
  inv (systemProjection l E k X Y f c B M) ≫
    (reduction l E Y.scheme (C.reduction Y.scheme)).map tau.hom

/-- Bounds, normalization and origin needed for the actual Brown Hom bijection.
These fields are conclusions of the scalar-extension theorem.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def BrownDomain : Prop :=
  (B.transport.siteX.Origin
    ((reduction l E X.scheme (C.reduction X.scheme)).obj M.obj)) ∧
  (B.transport.siteY.Origin
    ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj)) ∧
  (IsNormalizedCoefficientSystem.{u+1,u,u+1,u+2}
    (J := Scheme.ProEt.topology Y.scheme)
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    B.transport.siteY.proEvaluation
    ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj)) ∧
  (∀ q, FiniteDomainY l E k X Y f c B L q) ∧
  (∃ a : ℤ, ∀ q, (exceptionalLevel l E (C.reduction Y.scheme)
    B.strict B.brown B.evaluation B.transport L q).IsGE a) ∧
  (IsIso (systemProjection l E k X Y f c B M))

variable {l E k X Y f c B M L}

/-- The originX component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.originX (D : BrownDomain l E k X Y f c B M L) := D.1

/-- The originY component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.originY (D : BrownDomain l E k X Y f c B M L) := D.2.1

/-- The normalizedY component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.normalizedY (D : BrownDomain l E k X Y f c B M L) :
    IsNormalizedCoefficientSystem.{u+1,u,u+1,u+2}
      (J := Scheme.ProEt.topology Y.scheme)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      B.transport.siteY.proEvaluation
      ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj) := D.2.2.1

/-- The finiteTorY component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.finiteTorY (D : BrownDomain l E k X Y f c B M L) := D.2.2.2.1

/-- The lowerBound component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.lowerBound (D : BrownDomain l E k X Y f c B M L) := D.2.2.2.2.1

/-- The projection_iso component of the actual Brown domain.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev BrownDomain.projection_iso (D : BrownDomain l E k X Y f c B M L) := D.2.2.2.2.2

variable (l E k X Y f c B M L)

/-- Actual Brown transpose of the actual reduced trace, before evaluation.
Source: blueprint finite-extension supplement Step 6
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def BrownDomain.theta (D : BrownDomain l E k X Y f c B M L) :
    (reduction l E X.scheme (C.reduction X.scheme)).obj M.obj ⟶
      (brown l E B.strict B.brown B.evaluation B.transport).obj
        ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj) :=
  (B.transport.hom _ D.originY D.normalizedY D.finiteTorY D.lowerBound _ D.originX).symm
    (systemTrace l E k X Y f c B M L tau D.projection_iso)

attribute [local irreducible] FiniteData.arrow systemProjection systemTrace BrownDomain.theta

/-- Scalar-extended pair: finite transposes, actual Brown isomorphism with its
finite evaluations, bounded etale output, and rational representation.
Source: blueprint finite-extension supplement Steps 4--7
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def ExtendedPair :=
  (finite : FiniteData l E k X Y f c B M L tau) ×'
  (domain : BrownDomain l E k X Y f c B M L) ×'
  (_theta_iso : IsIso (BrownDomain.theta l E k X Y f c B M L tau domain)) ×'
  (_etale_bound : ∃ a : ℤ, (B.brown.right.obj
    (B.transport.siteY.direct.obj
      ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj))).IsGE a) ×'
  (_theta_evaluation : ∀ q,
    (B.transport.siteX.realization q).derived.map
      ((B.transport.siteX.proEvaluation.evaluation q).map
          (BrownDomain.theta l E k X Y f c B M L tau domain) ≫
        (B.transport.evaluation q).hom.app
          ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj)) ≫
      (finiteCoordinates l E B.strict B.brown B.evaluation B.transport B.transport_laws q).hom.app
        ((B.transport.siteY.proEvaluation.evaluation q).obj
          ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj)) =
      FiniteData.arrow l E k X Y f c B M L tau finite q) ×'
  (RationalPair l E k X Y f c C M L tau)

section
variable {l E k X Y f c B M L tau}

/-- The finite component of the scalar-extended representing pair.
Source: blueprint finite-extension supplement Steps 4--7
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev ExtendedPair.finite (Q : ExtendedPair l E k X Y f c B M L tau) := Q.1

/-- The domain component of the scalar-extended representing pair.
Source: blueprint finite-extension supplement Steps 4--7
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev ExtendedPair.domain (Q : ExtendedPair l E k X Y f c B M L tau) := Q.2.1

/-- The rational component of the scalar-extended representing pair.
Source: blueprint finite-extension supplement Steps 4--7
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
abbrev ExtendedPair.rational (Q : ExtendedPair l E k X Y f c B M L tau) := Q.2.2.2.2.2

end

/-- The integral representing bijections with their exact counit formula.
Source: blueprint integral Hom display, applied over the extension field
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def IntegralPair :=
  (hom : ∀ K : CondensedERealization.Integral l E X.scheme,
    (K ⟶ M) ≃ ((integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj K ⟶ L)) ×'
  (∀ K h, hom K h = (integralSupport l E c C.reduction
    (C.atCompactification X Y f c).integral).map h ≫ tau)

/-- Supplied data and the reconstructed trace, with neither recognition branch discarded.
Source: blueprint integral Hom display
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def suppliedTrace
    (A : Supplied l E (C.reduction X.scheme) (C.reduction Y.scheme)
      B.strict B.brown B.evaluation B.transport L) :=
  B.pairs.hom L A A.object (𝟙 _)

/-- The finite-coordinate map phi_n includes the actual reconstruction counit.
Source: blueprint finite-extension supplement Steps 1 and 4
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def suppliedPhi
    (A : Supplied l E (C.reduction X.scheme) (C.reduction Y.scheme)
      B.strict B.brown B.evaluation B.transport L) (q : ℕ) :=
  (B.transport.siteX.realization q).derived.map
    ((B.transport.siteX.proEvaluation.evaluation q).map
      ((adjunction l E X.scheme (C.reduction X.scheme)).counit.app A.system) ≫
      (A.phi q).hom) ≫
    (finiteCoordinates l E B.strict B.brown B.evaluation B.transport B.transport_laws q).hom.app
      ((B.transport.siteY.proEvaluation.evaluation q).obj
        ((reduction l E Y.scheme (C.reduction Y.scheme)).obj L.obj))

/-- The exact finite coefficient mate equation at all ramified factorizations.
Source: blueprint finite-extension supplement Steps 4--5
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteMateFormula
    (CC : ComparisonFamily l k)
    (B : Context l E k X Y f c (CC.coefficient E))
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (CC.coefficient E).reduction
      ((CC.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L)
    (D : FiniteData l E k X Y f c B M L tau)
    (BF : Context l F k X Y f c (CC.coefficient F))
    (DF : FiniteData l F k X Y f c BF
      ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
      (scalarTrace l E k X Y f c F i CC M L tau))
    (change : ∀ (n m : ℕ) (h : m + 1 ≤ e * (n + 1)),
    letI := B.transport.finite n
    letI := BF.transport.finite m
    FiniteCoefficientAdjoints.Change (finiteMap l E F i e he n m h) c
      (D.1 n) (DF.1 m)) : Prop :=
  ∀ (n m : ℕ) (h : m + 1 ≤ e * (n + 1)),
  letI := B.transport.finite n
  letI := BF.transport.finite m
  (scalarLevel l E k F i e he n m h CC X B.strict.PX BF.strict.PX
    B.transport.siteX BF.transport.siteX M).hom ≫
    (FiniteCoefficientAdjoints.tensor (finiteMap l E F i e he n m h) X.scheme).map
      (FiniteData.arrow l E k X Y f c B M L tau D n) ≫
    ((change n m h).mate.hom.app
      ⟨(levelY l E k X Y f c B n).obj L.obj, D.2.2.1 n⟩) =
  FiniteData.arrow l F k X Y f c BF
      ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
      (scalarTrace l E k X Y f c F i CC M L tau) DF m ≫
    (FiniteCoefficientAdjoints.upper _ c).map
      (scalarLevel l E k F i e he n m h CC Y B.strict.PY BF.strict.PY
        B.transport.siteY BF.transport.siteY L).hom


/-- Finite extension compatibility at all factorizations through a ramified quotient.
For m+1=e(n+1) this is the cofinal finite-free formula. For smaller m it is the
same counit-normalized quotient mate, without a concentration assertion.
Source: blueprint finite-extension supplement Steps 4--5
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def FiniteCompatibility
    (CC : ComparisonFamily l k)
    (B : Context l E k X Y f c (CC.coefficient E))
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (CC.coefficient E).reduction
      ((CC.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L)
    (D : FiniteData l E k X Y f c B M L tau)
    (BF : Context l F k X Y f c (CC.coefficient F))
    (DF : FiniteData l F k X Y f c BF
      ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
      (scalarTrace l E k X Y f c F i CC M L tau)) :=
  (change : ∀ (n m : ℕ) (h : m + 1 ≤ e * (n + 1)),
    letI := B.transport.finite n
    letI := BF.transport.finite m
    FiniteCoefficientAdjoints.Change (finiteMap l E F i e he n m h) c
      (D.1 n) (DF.1 m)) ×'
  (FiniteMateFormula l E k X Y f c F i e he CC B M L tau D BF DF change)

/-- Scalar extension of an arbitrary condensed constructible test object.
Source: blueprint finite-field Hom compatibility
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def fieldTest (K : CondensedERealization.Constructible E X.scheme) :
    CondensedERealization.Constructible F X.scheme :=
  ⟨(fieldScalar l E F i X.scheme).obj K.obj,
    fieldScalar_preserves l E F i X.scheme K⟩

/-- The canonical inverse condensed compact-support projection at a constructible test.
Source: blueprint finite-field Hom compatibility
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def fieldProjectionInverse (K : CondensedERealization.Constructible E X.scheme) :=
  haveI := finiteProjection_isIso l E F i k X Y f c K
  inv ((condensedProjection (fieldMap l E F i) c).app K.obj)

/-- Coefficient compatibility of representing Hom bijections, on every condensed
E-test, using the fixed lattice realizations and compact-support projection.
Source: blueprint finite-extension supplement Step 8
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def HomScalarSquare (CC : ComparisonFamily l k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (CC.coefficient E).reduction
      ((CC.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L)
    (QE : RationalPair l E k X Y f c (CC.coefficient E) M L tau)
    (QF : RationalPair l F k X Y f c (CC.coefficient F)
      ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
      (scalarTrace l E k X Y f c F i CC M L tau)) : Prop :=
  ∀ (K : CondensedERealization.Constructible E X.scheme)
    (a : K.obj ⟶ (object l E k (CC.coefficient E) X M).obj),
    QF.hom (fieldTest l E k X F i K)
        ((fieldScalar l E F i X.scheme).map a ≫
          (latticeScalar l E F i k X ((CC.coefficient E).realization.atObject X)
            ((CC.coefficient F).realization.atObject X)).inv.app M) ≫
      (latticeScalar l E F i k Y ((CC.coefficient E).realization.atObject Y)
        ((CC.coefficient F).realization.atObject Y)).hom.app L =
    fieldProjectionInverse l E k X Y f c F i K ≫
      (fieldScalar l E F i Y.scheme).map (QE.hom K a)

/-- The scalar trace is transitive with the specified integral tensor associators.
Source: blueprint finite-extension supplement Step 8
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def TraceComposition (CC : ComparisonFamily l k)
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (CC.coefficient E).reduction
      ((CC.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L) : Prop :=
  ∀ (G : Type u) [NormedField G] [NormedAlgebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (j : F →ₐ[ℚ_[l]] G),
    scalarTrace l F k X Y f c G j CC
        ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
        (scalarTrace l E k X Y f c F i CC M L tau) ≫
      (integralScalarComp l E F G i j k Y).hom.app L =
    (integralSupport l G c (CC.coefficient G).reduction
      ((CC.coefficient G).atCompactification X Y f c).integral).map
        ((integralScalarComp l E F G i j k X).hom.app M) ≫
      scalarTrace l E k X Y f c G (j.comp i) CC M L tau

/-- Ordinary extension agrees with its specified completed scalar extension.
The isomorphism asserted is the published comparison chi, never a chosen map.
Source: blueprint finite-extension supplement Step 3
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def CompletionAgreement (T : CondensedERealization.Base k)
    (K : CondensedERealization.Integral l E T.scheme) : Prop :=
  IsIso ((completedIntegralScalarComparison l E F i T.scheme).app
    ((purCoefficientModel l E T.scheme).functor.obj K.obj)) ∧
  IsDerivedCompleteUnrestricted l F T.scheme
    ((completedDerivedScalarExtension l E F i T.scheme).obj
      ((purCoefficientModel l E T.scheme).functor.obj K.obj))

/-- One extension result, including all finite quotient mates and the specified
whole-system transpose and rational scalar square.
Source: blueprint finite-extension supplement Steps 3--8
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def ExtensionResult
    (CC : ComparisonFamily l k)
    (BE : Context l E k X Y f c (CC.coefficient E))
    (BF : Context l F k X Y f c (CC.coefficient F))
    (M : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c (CC.coefficient E).reduction
      ((CC.coefficient E).atCompactification X Y f c).integral).obj M ⟶ L)
    (QE : RationalPair l E k X Y f c (CC.coefficient E) M L tau)
    (DE : FiniteData l E k X Y f c BE M L tau) :=
  (_completionX : CompletionAgreement l E k F i X M) ×'
  (_completionY : CompletionAgreement l E k F i Y L) ×'
  (extended : ExtendedPair l F k X Y f c BF
    ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
    (scalarTrace l E k X Y f c F i CC M L tau)) ×'
  (_integral : IntegralPair l F k X Y f c
    ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
    (scalarTrace l E k X Y f c F i CC M L tau)) ×'
  (_compatibility : ∀ (e : ℕ) (he : PurCompactSupport.Ramification l E F i e),
    FiniteCompatibility l E k X Y f c F i e he CC BE M L tau DE BF extended.finite) ×'
  (_rational_square : HomScalarSquare l E k X Y f c F i CC M L tau QE extended.rational) ×'
  (_trace_composition : TraceComposition l E k X Y f c F i CC M L tau) ×'
  (∀ (G : Type u) [NormedField G] [NormedAlgebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G] (j : F →ₐ[ℚ_[l]] G),
    ∃ QG : RationalPair l G k X Y f c (CC.coefficient G)
      ((integralScalar l F G j k X).obj ((integralScalar l E F i k X).obj M))
      ((integralScalar l F G j k Y).obj ((integralScalar l E F i k Y).obj L))
      (scalarTrace l F k X Y f c G j CC
        ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
        (scalarTrace l E k X Y f c F i CC M L tau)),
      HomScalarSquare l F k X Y f c G j CC
        ((integralScalar l E F i k X).obj M) ((integralScalar l E F i k Y).obj L)
        (scalarTrace l E k X Y f c F i CC M L tau) extended.rational QG)

/-- Naturality for actual supplied-system arrows, expressed on the reconstructed
integral maps and all rational test arrows. The Brown square uses actual system
maps, rather than inferred levelwise faithfulness.
Source: blueprint finite-extension supplement Step 8
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def SuppliedNaturality (CC : ComparisonFamily l k)
    (BE : Context l E k X Y f c (CC.coefficient E)) : Prop :=
  ∀ (L L' : CondensedERealization.Integral l E Y.scheme)
    (A : Supplied l E ((CC.coefficient E).reduction X.scheme)
      ((CC.coefficient E).reduction Y.scheme) BE.strict BE.brown BE.evaluation BE.transport L)
    (A' : Supplied l E ((CC.coefficient E).reduction X.scheme)
      ((CC.coefficient E).reduction Y.scheme) BE.strict BE.brown BE.evaluation BE.transport L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (BE.pairs.coordinate.pair L' A').theta.hom =
      (BE.pairs.coordinate.pair L A).theta.hom ≫
        (brown l E BE.strict BE.brown BE.evaluation BE.transport).map
          ((reduction l E Y.scheme ((CC.coefficient E).reduction Y.scheme)).map b.hom) →
    ∀ (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F),
      (integralSupport l F c (CC.coefficient F).reduction
          ((CC.coefficient F).atCompactification X Y f c).integral).map
          ((integralScalar l E F i k X).map
            (ObjectProperty.homMk ((totalLimit l E X.scheme).map a))) ≫
        scalarTrace l E k X Y f c F i CC A'.object L'
          (suppliedTrace l E k X Y f c BE L' A') =
      scalarTrace l E k X Y f c F i CC A.object L
          (suppliedTrace l E k X Y f c BE L A) ≫ (integralScalar l E F i k Y).map b

/-- Naturality of the actual Brown transposes and rational bijections in any
commuting pair of integral trace maps.
Source: blueprint finite-extension supplement Step 8
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension). -/
def PairNaturality (C : CoefficientData l E k)
    (B : Context l E k X Y f c C) : Prop :=
  ∀ (M M' : CondensedERealization.Integral l E X.scheme)
    (L L' : CondensedERealization.Integral l E Y.scheme)
    (tau : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M ⟶ L)
    (tau' : (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).obj M' ⟶ L')
    (Q : ExtendedPair l E k X Y f c B M L tau)
    (Q' : ExtendedPair l E k X Y f c B M' L' tau')
    (a : M ⟶ M') (b : L ⟶ L'),
    (integralSupport l E c C.reduction
      (C.atCompactification X Y f c).integral).map a ≫ tau' = tau ≫ b →
    ((reduction l E X.scheme (C.reduction X.scheme)).map a.hom ≫
        BrownDomain.theta l E k X Y f c B M' L' tau' Q'.domain =
      BrownDomain.theta l E k X Y f c B M L tau Q.domain ≫
        (brown l E B.strict B.brown B.evaluation B.transport).map
          ((reduction l E Y.scheme (C.reduction Y.scheme)).map b.hom)) ∧
    ∀ (K : CondensedERealization.Constructible E X.scheme)
      (h : K.obj ⟶ (object l E k C X M).obj),
      Q'.rational.hom K
          (h ≫ ((C.realization.atObject X).realization.functor.map
            ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map a)).hom)
        = Q.rational.hom K h ≫ ((C.realization.atObject Y).realization.functor.map
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map b)).hom

/-- Rationalization and finite scalar extension of reconstructed representing pairs,
with the actual Brown-system transpose and all canonical quotient mates.
Source: current blueprint sk-prop-sp-rational, localized Hom display, and
sk-thm-sp-qbar field transitions
(blueprint: lem-pur-reconstructed-pair-finite-scalar-extension).
Proof: tensor the integral representing Hom equivalence with E and descend by the
fully faithful realization equivalence. Finite freeness identifies ordinary and
completed integral scalar extension. Tensor balancing identifies every ramified
quotient reduction. The finite adjunction counit equations identify its transpose
with extension of the supplied phi followed by the canonical mate. The same equation
for further quotients proves every finite transpose invertible and identifies any
two cofinal choices with the unique transpose of the same reduced trace. Transpose
the actual whole-system reduced trace using the Brown Hom equivalence. Its evaluated
maps are the finite transposes, so evaluation detects its invertibility. Uniform
finite lower bounds give bounded etale Brown output. Reconstruct by the actual-system
recognition alternative over F and cancel the reduction/limit unit and counit to
identify its trace with scalarTrace. Rationalize again. Finally the tensor associator
and support-comparison composition equations prove trace transitivity, the Hom
scalar square, and naturality for actual supplied arrows. No cohomological concentration
claim is needed after a nonflat quotient. -/
theorem reconstructed_pair_finite_scalar_extension
    (CC : ComparisonFamily l k)
    (BE : Context l E k X Y f c (CC.coefficient E)) :
    (∀ (L : CondensedERealization.Integral l E Y.scheme)
      (A : Supplied l E ((CC.coefficient E).reduction X.scheme)
        ((CC.coefficient E).reduction Y.scheme)
        BE.strict BE.brown BE.evaluation BE.transport L),
      ∃ QE : RationalPair l E k X Y f c (CC.coefficient E) A.object L
          (suppliedTrace l E k X Y f c BE L A),
        ∃ DE : FiniteData l E k X Y f c BE A.object L
            (suppliedTrace l E k X Y f c BE L A),
          (∀ q, FiniteData.arrow l E k X Y f c BE A.object L
            (suppliedTrace l E k X Y f c BE L A) DE q =
              suppliedPhi l E k X Y f c BE L A q) ∧
        ∀ (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
          [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
          (BF : Context l F k X Y f c (CC.coefficient F)),
          Nonempty (ExtensionResult l E k X Y f c F i CC BE BF A.object L
            (suppliedTrace l E k X Y f c BE L A) QE DE)) ∧
      SuppliedNaturality l E k X Y f c CC BE ∧
      (∀ (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
        [FiniteDimensional ℚ_[l] F]
        (BF : Context l F k X Y f c (CC.coefficient F)),
        PairNaturality l F k X Y f c (CC.coefficient F) BF) := by
  sorry

end WeilConjectures.PurRepresentingPairFiniteScalar
