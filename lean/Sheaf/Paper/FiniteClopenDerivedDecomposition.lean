/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Data.Set.Finite.Lattice
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite clopen decomposition of derived coefficient categories

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-derived-decomposition).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Preserve the published automatically included hypotheses in theorem signatures.
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

/-- Finite or completed coefficients, with n denoting exponent n+1.
Source: Stacks 04TS and the section-invariant finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRing (X : Scheme.{u}) (n : ℕ) (integral : Bool) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  if integral then completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X
  else integralCoefficientCommRingSheaf P.coefficients.l P.extension X n

/-- The actual inclusion of the component site: compose its structure map with j.
Source: Stacks 00XZ, 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenSiteInclusion {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- Continuity of this concrete site inclusion, with no added assumption.
Source: Stacks 00XZ (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenSiteInclusionContinuous {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenSiteInclusion j).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

/-- Restrict a coefficient ring by precomposition along the component site.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRingRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R

/-- Forget commutativity only; this is the published module-sheaf encoding.
Source: Stacks Modules on Sites (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
abbrev clopenModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The canonical sectionwise module restriction, including its scalar action.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    clopenModules X R ⥤ clopenModules Y (clopenRingRestriction j R) :=
  SheafOfModules.pushforward (F := clopenSiteInclusion j) (𝟙 _)

/-- Exactness of restriction, required to descend the actual degreewise functor.
Source: Stacks 04TS and 015F (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: localize the small site at the open immersion (weakly-etale localization).
Restriction of module sheaves is exact; kernels and sheafified cokernels restrict
locally. Its formula is additive. This uses sheaf exactness, not sectionwise
surjectivity of epimorphisms. -/
theorem clopenRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive ∧ PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) := by
  have : (clopenSiteInclusion j).IsCocontinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  have : (clopenSiteInclusion j).IsLeftAdjoint := by
    exact (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial).isLeftAdjoint
  have : (clopenRestriction j R).Additive := ⟨by intros; rfl⟩
  have : (clopenRestriction j R).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward (F := clopenSiteInclusion j) (𝟙 _)).IsLeftAdjoint
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let T := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (clopenRingRestriction j R)
  have : PreservesFiniteLimits (clopenRestriction j R ⋙ SheafOfModules.toSheaf T) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S ⋙
      (clopenSiteInclusion j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)))
  have : PreservesFiniteLimits (clopenRestriction j R) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf T)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity from exact sectionwise restriction. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive := (clopenRestriction_exact j R).1

/-- Left exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.1

/-- Right exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.2

/-- The standard unbounded localization of these abelian module categories.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenHasDerived (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (clopenModules X R) := HasDerivedCategory.standard _

/-- Restrict complexes degreewise and descend through quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (clopenRestriction j R).mapDerivedCategory

/-- Invertibility of ell in a residue field over the fixed algebraically closed base.
Source: purity conventions (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: ell differs from p, so is nonzero in k. The structure map to the residue
field carries its inverse in k to an inverse there. No new geometric hypothesis
is required. -/
theorem clopenResidue_isUnit (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    IsUnit (P.coefficients.l : Y.left.residueField y) := by
  simpa only [map_natCast] using (P.coefficientPrime_isUnit_stalk Y.left Y.hom y).map
    (IsLocalRing.residue (Y.left.presheaf.stalk y))

/-- The recorded constructible integral pullback, supplying only the source-implied
residue-field invertibility. Source: blueprint integral coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  constructibleIntegralPullback P.coefficients.l P.extension j.left

/-- The recorded raw rationalized pullback, without Karoubi completion.
Source: blueprint rational coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalDerivedPullback P.coefficients.l P.extension j.left

/-- The recorded common-stage pullback, on the fixed algebraic coefficient closure.
Source: blueprint common-stage coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStagePullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left


/-- The completed tensor on the constructible integral category, with the recorded
normalization on strict K-flat towers. Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  constructibleIntegralTensor P.coefficients.l P.extension Y.left

/-- The recorded rational tensor, extended linearly on morphisms.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  rationalDerivedTensor P.coefficients.l P.extension Y.left

/-- The common-stage tensor, formed at the coefficient compositum.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar Y.left

/-- The actual regular completed module in the intrinsic constructible category.
Only its membership proof comes from the published constant-coefficient theorem.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralUnit (Y : Scheme.{u}) :
    sfIntegralConstructibleCategory P.coefficients.l P.extension Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l P.extension Y,
    (integralConstantCoefficient_constructible P.coefficients.l P.extension Y
      P.field P.coefficients.different).2.1⟩

/-- The raw rational image of the same regular integral module.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalUnit (Y : Scheme.{u}) :=
  (sfRationalConstructibleLocalization P.coefficients.l P.extension Y).obj (P.clopenIntegralUnit Y)

/-- The coefficient unit at any finite stage of the fixed algebraic closure.
Its small field model is the published one, and its integral representative is
the regular completed module in degree zero.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageUnit (Y : Scheme.{u})
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar Y :=
  ⟨B, (sfRationalConstructibleLocalization P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    Y).obj
      ⟨integralConstantCoefficientObject P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) Y,
        (integralConstantCoefficient_constructible P.coefficients.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
          Y P.field P.coefficients.different).2.1⟩⟩

/-- The existing canonical integral scalar/restriction comparison, on every finite
coefficient extension including identities. Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (K : sfIntegralConstructibleCategory P.coefficients.l P.extension X.left) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  integralPullbackScalarComparison P.coefficients.l P.extension L ι j.left K

/-- The same normalized comparison after raw rationalization. Its action is the
linear extension of the preceding integral map, exactly as in the recorded operations.
Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalPullbackScalarComparison P.coefficients.l P.extension L ι j.left


private def clopenTowerAsComplex {A : Type*} [Category A] [Abelian A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X n := C ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) n
  d n m :=
    { app k := (C.obj k).d n m
      naturality _ _ f := (C.map f).comm n m }
  shape n m h := by ext k; exact (C.obj k).shape n m h
  d_comp_d' n m k _ _ := by ext t; exact (C.obj t).d_comp_d n m k

private def clopenTowerAsComplexMap {A : Type*} [Category A] [Abelian A]
    {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ D) :
    clopenTowerAsComplex C ⟶ clopenTowerAsComplex D where
  f n :=
    { app k := (α.app k).f n
      naturality _ _ f := congrArg (fun g ↦ g.f n) (α.naturality f) }
  comm' n m _ := by ext k; exact (α.app k).comm n m

private theorem clopenRoosMap_unique {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (μ : strictRoosComplex X ⟶ strictRoosComplex Y) (f : X ⟶ Y)
    (h : ∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫
        biprod.map ((strictRoosProductMap f).f p) ((strictRoosProductMap f).f (p + 1))) :
    μ = strictRoosMapOfSquare (strictRoosProductMap f) (strictRoosProductMap f)
      (strictRoosProductMap_comm f) := by
  apply HomologicalComplex.Hom.ext
  funext m
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, m = p + 1 := ⟨m - 1, by omega⟩
  exact (cancel_mono (strictRoosCoordinates Y p).hom).mp
    ((h p).trans (strictRoosMapOfSquare_coordinates _ _ _ p).symm)

private theorem clopenRoosComparison {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    Nonempty (integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ integralOperationsRoosFunctor) := by
  obtain ⟨θ, _, hn, _⟩ := strictRoosAdditiveComparison F (fun _ ↦ inferInstance)
  refine ⟨NatIso.ofComponents (fun C ↦ θ (clopenTowerAsComplex C)) ?_⟩
  intro C D α
  obtain ⟨μ, ν, hμ, hν, hnat⟩ :=
    hn (clopenTowerAsComplex C) (clopenTowerAsComplex D) (clopenTowerAsComplexMap α)
  let a := strictRoosProductMap (clopenTowerAsComplexMap α)
  have hμ' : μ = strictRoosMapOfSquare a a
      (strictRoosProductMap_comm (clopenTowerAsComplexMap α)) :=
    clopenRoosMap_unique μ (clopenTowerAsComplexMap α) hμ
  have heq : μ = integralOperationsRoosMap α := hμ'
  let β := (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (clopenTowerAsComplexMap α)
  let b := strictRoosProductMap β
  have hν' : ν = strictRoosMapOfSquare b b (strictRoosProductMap_comm β) :=
    clopenRoosMap_unique ν β hν
  have heq' : ν = integralOperationsRoosMap
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F.mapHomologicalComplex (ComplexShape.up ℤ)) |>.map α) := hν'
  change (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (integralOperationsRoosMap α) ≫ _ =
    _ ≫ integralOperationsRoosMap _
  exact (congrArg (fun f ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
    (θ (clopenTowerAsComplex D)).hom) heq).symm.trans
      (hnat.trans (congrArg (fun f ↦ (θ (clopenTowerAsComplex C)).hom ≫ f) heq'))

private theorem clopen_heq_square {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') (hA : A = A') (hB : B = B') (hfg : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst A'
  subst B'
  simpa using eq_of_heq hfg

private theorem clopenNatIsoOfHEq {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (ho : ∀ K, F.obj K = G.obj K)
    (hm : ∀ (K K' : C) (f : K ⟶ K'), HEq (F.map f) (G.map f)) :
    Nonempty (F ≅ G) := by
  refine ⟨NatIso.ofComponents (fun K ↦ eqToIso (ho K)) ?_⟩
  intro K K' f
  exact clopen_heq_square _ _ (ho K) (ho K') (hm K K' f)

attribute [local irreducible] integralDerivedPullback integralScalarExtension
  scalarCompletion integralOrdinaryScalar

private theorem clopenScalarSquare
    {A B C D A' B' : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B']
    (incA : A' ⥤ A) (incB : B' ⥤ B) (r : A ⥤ B) (r' : C ⥤ D)
    (sA oA : A ⥤ C) (sB oB : B ⥤ D) (p : A' ⥤ B')
    (eA : incA ⋙ oA ≅ incA ⋙ sA) (eB : incB ⋙ oB ≅ incB ⋙ sB)
    (eR : incA ⋙ r ≅ p ⋙ incB) (eO : r ⋙ oB ≅ oA ⋙ r') :
    Nonempty (incA ⋙ sA ⋙ r' ≅ p ⋙ incB ⋙ sB) :=
  ⟨(Functor.associator incA sA r').symm ≪≫
    (Functor.isoWhiskerRight eA r').symm ≪≫
    Functor.associator incA oA r' ≪≫
    (Functor.isoWhiskerLeft incA eO).symm ≪≫
    (Functor.associator incA r oB).symm ≪≫
    Functor.isoWhiskerRight eR oB ≪≫
    Functor.associator p incB oB ≪≫
    Functor.isoWhiskerLeft p eB⟩

private theorem clopenIntegralPullbackInclusion
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :
    Nonempty ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
        integralDerivedPullback P.coefficients.l P.extension j.left ≅
      P.clopenIntegralPullback j ⋙
        (sfIntegralConstructible P.coefficients.l P.extension Y.left).ι) :=
  ⟨Iso.refl _⟩

private theorem clopenScalarCompletion (W : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty ((sfIntegralConstructible P.coefficients.l P.extension W).ι ⋙
        integralOrdinaryDerivedScalar P.coefficients.l P.extension L ι W ≅
      (sfIntegralConstructible P.coefficients.l P.extension W).ι ⋙
        integralScalarExtension P.coefficients.l P.extension L ι W) := by
  refine ⟨NatIso.ofComponents
    (fun K ↦ scalarCompletionIso P.coefficients.l P.extension L ι W K.obj K.property.1) ?_⟩
  intro K K' f
  change (integralOrdinaryDerivedScalar P.coefficients.l P.extension L ι W).map f.hom ≫
      (scalarCompletion P.coefficients.l P.extension L ι W).app K'.obj =
    (scalarCompletion P.coefficients.l P.extension L ι W).app K.obj ≫
      (integralScalarExtension P.coefficients.l P.extension L ι W).map f.hom
  exact (scalarCompletion P.coefficients.l P.extension L ι W).naturality f.hom

private theorem clopenRationalPullbackComparison
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :
    Nonempty (P.clopenIntegralPullback j ⋙
        sfRationalConstructibleLocalization P.coefficients.l P.extension Y.left ≅
      sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
        P.clopenRationalPullback j) := by
  let := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  change Nonempty (constructibleIntegralPullback P.coefficients.l P.extension j.left ⋙
      sfRationalConstructibleLocalization P.coefficients.l P.extension Y.left ≅
    sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
      rationalDerivedPullback P.coefficients.l P.extension j.left)
  have hs :=
    (rationalDerivedPullback_existsUnique P.coefficients.l P.extension j.left).exists.choose_spec
  exact clopenNatIsoOfHEq
    (constructibleIntegralPullback P.coefficients.l P.extension j.left ⋙
      sfRationalConstructibleLocalization P.coefficients.l P.extension Y.left)
    (sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
      rationalDerivedPullback P.coefficients.l P.extension j.left)
    (fun K ↦ (hs.2.1
      ((sfRationalConstructibleLocalization P.coefficients.l P.extension X.left).obj K)).symm)
    (fun K K' f ↦ (hs.2.2 K K' f 1).symm)

private theorem clopenTorAmplitude_mono {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K : Scheme.proEtaleDerivedCategory Y A} {a b c d : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude Y A K a b) (hca : c ≤ a) (hbd : b ≤ d) :
    Scheme.HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hca.trans (h.1.trans hbd), ?_⟩
  intro L Q e f hf hQ M m hm
  exact h.2 L Q e f hf hQ M m (hm.imp
    (fun hm ↦ lt_of_lt_of_le hm hca) (fun hm ↦ lt_of_le_of_lt hbd hm))

private theorem clopenCohomologicalSupport_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K K' : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ K') :
    Scheme.proEtaleCohomologicalSupport K = Scheme.proEtaleCohomologicalSupport K' := by
  ext m
  exact not_congr ⟨fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e).symm,
    fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e)⟩

private theorem clopenTorAmplitude_of_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K K' : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ K') {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude Y A K a b) :
    Scheme.HasProEtaleTorAmplitude Y A K' a b := by
  refine ⟨h.1, ?_⟩
  intro L Q hL f hf hQ M m hm
  obtain ⟨eL⟩ := hL
  exact h.2 L Q ⟨eL ≪≫ e.symm⟩ f hf hQ M m hm

private theorem clopenPiTransport {J : Type*} {C : Type*} [Category C]
    {D E : J → Type*} [∀ i, Category (D i)] [∀ i, Category (E i)]
    (F : ∀ i, C ⥤ D i) (G : ∀ i, D i ⥤ E i) (H : ∀ i, C ⥤ E i)
    [(Functor.pi' F).IsEquivalence] [∀ i, (G i).IsEquivalence]
    (e : ∀ i, F i ⋙ G i ≅ H i) : (Functor.pi' H).IsEquivalence := by
  let α : Functor.pi' F ⋙ Functor.pi G ≅ Functor.pi' H :=
    NatIso.pi' (fun i ↦ e i)
  exact Functor.isEquivalence_of_iso α

private theorem clopenSubcategoryPi {J : Type*} {C : Type*} [Category C]
    {D : J → Type*} [∀ i, Category (D i)] (F : ∀ i, C ⥤ D i)
    [(Functor.pi' F).IsEquivalence] (P : ObjectProperty C)
    (Q : ∀ i, ObjectProperty (D i))
    (h : ∀ K, P K ↔ ∀ i, Q i ((F i).obj K))
    (hiso : ∀ i {M N : D i}, (M ≅ N) → Q i M → Q i N) :
    (Functor.pi' (fun i ↦ (Q i).lift (P.ι ⋙ F i)
      (fun K ↦ (h K.obj).mp K.property i))).IsEquivalence := by
  let G := Functor.pi' (fun i ↦ (Q i).lift (P.ι ⋙ F i)
    (fun K ↦ (h K.obj).mp K.property i))
  have hf : G.FullyFaithful :=
    { preimage := fun f ↦ ObjectProperty.homMk
        ((Functor.pi' F).preimage (fun i ↦ (f i).hom))
      map_preimage := fun f ↦ by
        funext i
        apply ObjectProperty.hom_ext
        exact congrFun ((Functor.pi' F).map_preimage (fun i ↦ (f i).hom)) i
      preimage_map := fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (Functor.pi' F).preimage_map f.hom }
  have : G.Full := hf.full
  have : G.Faithful := hf.faithful
  have : G.EssSurj := by
    refine ⟨fun Y ↦ ?_⟩
    let K := (Functor.pi' F).objPreimage (fun i ↦ (Y i).obj)
    let e := (Functor.pi' F).objObjPreimageIso (fun i ↦ (Y i).obj)
    have hK : P K := (h K).mpr (fun i ↦
      hiso i (((Pi.eval D i).mapIso e).symm) (Y i).property)
    exact ⟨⟨K, hK⟩, ⟨Pi.isoMk (fun i ↦
      ObjectProperty.isoMk (Q i) ((Pi.eval D i).mapIso e))⟩⟩
  exact Functor.IsEquivalence.mk

section Decomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

/-- Exact module equivalence and its explicit sectionwise inverse.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 1--3 of the node. The components cover the pro-etale site; distinct
intersections are empty. Glue modules and morphisms (module-sheaf gluing and set
sheaf morphism descent). On a test object V the inverse has sections the product
of the sections on V times_X Xi. Restriction maps and scalar actions are componentwise.
The sheaf axiom gives the unit and counit. Additivity is sectionwise and an additive
equivalence preserves kernels and cokernels. Empty components give zero factors;
the empty cover forces every section group to be zero. -/
theorem finiteClopen_module_equivalence (n : ℕ) (integral : Bool) :
    ∃ e : clopenModules X.left (P.clopenRing X.left n integral) ≌
        (∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      e.functor = Functor.pi' (fun i ↦
        clopenRestriction (j i).left (P.clopenRing X.left n integral)) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ∃ φ : ∀ (F : ∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
          (V : X.left.ProEt),
        ((e.inverse.obj F).val.obj (op V)) ≃+
          (∀ i, (F i).val.obj (op ((Scheme.proEtaleBaseChange (j i).left).obj V))),
        (∀ F V (r : (P.clopenRing X.left n integral).obj.obj (op V))
          (x : (e.inverse.obj F).val.obj (op V)) (i : I),
          φ F V (r • x) i =
            ((P.clopenRing X.left n integral).obj.map
              (MorphismProperty.Over.homMk
                (A := (clopenSiteInclusion (j i).left).obj
                  ((Scheme.proEtaleBaseChange (j i).left).obj V)) (B := V)
                (pullback.fst V.hom (j i).left) pullback.condition).op r) • φ F V x i) ∧
        (∀ (F : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (V W : X.left.ProEt) (f : V ⟶ W) (x : (e.inverse.obj F).val.obj (op W)),
          φ F V ((e.inverse.obj F).val.map f.op x) =
            fun i ↦ (F i).val.map ((Scheme.proEtaleBaseChange (j i).left).map f).op
              (φ F W x i)) ∧
        (∀ (F G : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (a : F ⟶ G) (V : X.left.ProEt) (x : (e.inverse.obj F).val.obj (op V)),
          φ G V ((e.inverse.map a).val.app (op V) x) =
            fun i ↦ (a i).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F V x i)) := by
  sorry

/-- The degreewise restrictions induce the product of the unbounded derived categories,
with componentwise cohomology, tensor and the regular coefficient unit.
Source: Stacks 04TS, 015F, 06YS, 0G7D
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 4--6. Restriction and insertion into one coordinate are exact.
Their identities descend through quasi-isomorphisms, so the product here is the
product of derived categories. Exact restriction commutes with cohomology. The
bilinear universal property identifies ordinary tensors and the coefficient unit.
K-flatness is detected componentwise by testing against insertions of acyclic
complexes. Descending the pure-tensor comparison on K-flat resolutions gives
the natural tensor isomorphism, with the normalized existing tensor models. -/
theorem finiteClopen_unbounded_decomposition (n : ℕ) (integral : Bool) :
    (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))).IsEquivalence ∧
    (∀ (i : I) (m : ℤ), Nonempty
      (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ⋙
          DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙
          clopenRestriction (j i).left (P.clopenRing X.left n integral))) ∧
    (∀ i : I, Nonempty
      ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (P.clopenRing X.left n integral)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))))) ∧
    ∀ (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology X.left)
        (P.clopenRing X.left n integral)) (i : I)
      (Mi : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology (Xi i).left)
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      Nonempty (M.closed.tensor ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ≅
        ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).prod
          (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))) ⋙
            Mi.closed.tensor) := by
  sorry

/-- Strict towers and their functorial Roos complexes restrict termwise.
Source: Stacks 08TC (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 7. Restriction keeps sectionwise countable products and their
projections, including the transition endomorphism 1-s. It therefore commutes
with its functorial shifted mapping cone on objects and strict maps. Exactness
of countable pro-etale products identifies these products with derived products.
Applying the exact restriction to any Roos triangle gives the component Roos
triangle, with its original maps; no canonical uniqueness of bare cones is used. -/
theorem finiteClopen_strict_roos (n : ℕ) (integral : Bool) (i : I) :
    Nonempty (integralOperationsRoosFunctor ⋙
        (clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
            (ComplexShape.up ℤ)) ⋙ integralOperationsRoosFunctor) := by
  let S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (P.clopenRing X.left n integral)
  let T := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))
  have toSheaf_preserves {Y : Scheme.{u}}
      (R : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) :
      PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{u + 1} R) := by
    have : PreservesLimitsOfShape (Discrete ℕ)
        (SheafOfModules.toSheaf.{u + 1} R ⋙ sheafToPresheaf _ _) :=
      comp_preservesLimitsOfShape (SheafOfModules.forget.{u + 1} R)
        (PresheafOfModules.toPresheaf R.obj)
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{u + 1} S) :=
    toSheaf_preserves S
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{u + 1} T) :=
    toSheaf_preserves T
  have : ReflectsLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{u + 1} T) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let F := clopenRestriction (j i).left (P.clopenRing X.left n integral)
  have : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ SheafOfModules.toSheaf.{u + 1} T) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{u + 1} S ⋙
      (clopenSiteInclusion (j i).left).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.ProEt.topology (Xi i).left) (Scheme.ProEt.topology X.left)))
  have : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u + 1} T)
  exact clopenRoosComparison F

/-- Finite constructibility, fixed cohomological intervals and fixed Tor intervals
are detected on the components; hence both finite-coefficient subcategories split.
Source: blueprint section-invariant well-definedness, finite stage
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 8. Intersect a finite stratification with the clopen pieces;
conversely unite their finitely many stratifications. Cohomology is componentwise,
so every common interval works. Test Tor against inserted degree-zero modules and
use componentwise derived tensor. Lifting the restriction functors to these full
subcategories and restricting the gluing inverse gives the two equivalences.
No nonempty-index hypothesis is needed; ordered intervals also work for zero objects. -/
theorem finiteClopen_finite_bounds (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b ↔
        ∀ i, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b)) := by
  sorry

/-- Restriction on the finite constructible full subcategory, with its actual
ambient pullback on both objects and arrows. Source: blueprint finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteConstructiblePullback (n : ℕ) (i : I) :=
  (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K.obj).1.mp
      K.property) i)

/-- The finite-Tor condition is detected on the finite list of components.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: use finiteClopen_finite_bounds for constructibility and Tor in a fixed interval.
For the converse take the minimum and maximum of the finitely many component bounds.
For no components take [0,0]; vanishing is detected by the empty covering sheaf axiom. -/
theorem finiteClopen_finiteTor_iff (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) := by
  have hb := P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K
  constructor
  · intro h i
    obtain ⟨a, b, ht⟩ := h.2
    exact ⟨hb.1.mp h.1 i, a, b, (hb.2.2 a b ht.1).mp ht i⟩
  · intro h
    have hc := hb.1.mpr (fun i ↦ (h i).1)
    have ht : ∀ i, ∃ a b : ℤ, Scheme.HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b :=
      fun i ↦ (h i).2
    choose a b ht using ht
    obtain ⟨c, hc'⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd'⟩ := (Set.finite_range b).bddAbove
    refine ⟨hc, min c d, max c d, ?_⟩
    apply (hb.2.2 (min c d) (max c d) (min_le_max (a := c) (b := d))).mpr
    intro i
    exact clopenTorAmplitude_mono (ht i)
      ((min_le_left c d).trans (hc' (Set.mem_range_self i)))
      ((hd' (Set.mem_range_self i)).trans (le_max_right c d))

/-- The finite-Tor restriction is the full-subcategory lift of the recorded pullback.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteTorPullback (n : ℕ) (i : I) :=
  (finiteTorConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((finiteTorConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ (P.finiteClopen_finiteTor_iff X Xi j hdisjoint hcover n K.obj).mp K.property i)

/-- The finite derived restriction above is the recorded intrinsic inverse image,
after identifying its restricted constant coefficient sheaf with the component's.
The normalization on Q specifies termwise coefficient transport, including maps.
Source: Stacks 00XZ, 04TS, 015F
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: constant sheafification commutes with localization; its unit identifies
constant sections. Transport modules by the inverse ring isomorphism. The
underlying sectionwise restriction is the inverse image for an open immersion.
Its exact termwise descent is the recorded finiteDerivedPullback. -/
theorem finiteClopen_finite_restriction_identification (n : ℕ) (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left n false) ≅
        integralCoefficientCommRingSheaf P.coefficients.l P.extension (Xi i).left n)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n false))) ≌
        Scheme.proEtaleDerivedCategory (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty (clopenDerivedRestriction (j i).left (P.clopenRing X.left n false) ⋙
        e.functor ≅ finiteDerivedPullback P.coefficients.l P.extension n (j i).left) := by
  sorry

/-- Both finite coefficient full-subcategory equivalences use these exact restrictions.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restrict the ambient derived equivalence using the componentwise predicates.
The inverse gluing preserves them by the converse parts of the two bound statements. -/
theorem finiteClopen_finite_equivalences (n : ℕ) :
    (Functor.pi' (fun i ↦ P.clopenFiniteConstructiblePullback X Xi j
      hdisjoint hcover n i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenFiniteTorPullback X Xi j
      hdisjoint hcover n i)).IsEquivalence := by
  have hid := fun i ↦ P.finiteClopen_finite_restriction_identification
    X Xi j hdisjoint hcover n i
  choose c e hQ hF using hid
  let α := fun i ↦ Classical.choice (hF i)
  have : (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left (P.clopenRing X.left n false))).IsEquivalence :=
    (P.finiteClopen_unbounded_decomposition X Xi j hdisjoint hcover n false).1
  have : (Functor.pi' (fun i ↦
      finiteDerivedPullback P.coefficients.l P.extension n (j i).left)).IsEquivalence :=
    clopenPiTransport _ (fun i ↦ (e i).functor) _ α
  have hclosed (Y : Scheme.{u}) :
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y).IsClosedUnderIsomorphisms := by
    let := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    exact (Scheme.proEtale_bounded_constructible_isTriangulated Y
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).1
  constructor
  · exact clopenSubcategoryPi
      (fun i ↦ finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left)
      (fun i ↦ Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left)
      (fun K ↦ (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K).1)
      (fun i {M N} e h ↦ @ObjectProperty.prop_of_iso _ _ _ (hclosed (Xi i).left) _ _ e h)
  · apply clopenSubcategoryPi
      (fun i ↦ finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
      (finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left)
      (fun i ↦ finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left)
      (fun K ↦ P.finiteClopen_finiteTor_iff X Xi j hdisjoint hcover n K)
    intro i M N e h
    refine ⟨@ObjectProperty.prop_of_iso _ _ _ (hclosed (Xi i).left) _ _ e h.1, ?_⟩
    obtain ⟨a, b, ht⟩ := h.2
    exact ⟨a, b, clopenTorAmplitude_of_iso e ht⟩

/-- Tensor and integral reduction are componentwise for the actual coefficient functors.
Source: Stacks 06YS, 0G7D, 08TC; blueprint coefficient transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 5--6 and 9--11. Restriction carries sheaf tensor generators to the
same pure tensors. Descend on K-flat representatives to obtain the finite natural
comparison. For integral tensor and reduction, restrict the strict towers and
use the natural Roos comparison. Extend the resulting maps linearly to rational
Homs and then represent them at the common finite coefficient compositum.
All maps commute with identity and composite coefficient changes because the
pure-tensor formulas and the strict tower maps do. -/
theorem finiteClopen_tensor_and_reduction (i : I) :
    (∀ n : ℕ, Nonempty
      (finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).prod
          (finiteDerivedPullback P.coefficients.l P.extension n (j i).left)) ⋙
            finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty (P.clopenIntegralTensor X ⋙ P.clopenIntegralPullback (j i) ≅
      ((P.clopenIntegralPullback (j i)).prod (P.clopenIntegralPullback (j i))) ⋙
        P.clopenIntegralTensor (Xi i)) ∧
    Nonempty (P.clopenRationalTensor X ⋙ P.clopenRationalPullback (j i) ≅
      ((P.clopenRationalPullback (j i)).prod (P.clopenRationalPullback (j i))) ⋙
        P.clopenRationalTensor (Xi i)) ∧
    Nonempty (P.clopenCommonStageTensor X ⋙ P.clopenCommonStagePullback (j i) ≅
      ((P.clopenCommonStagePullback (j i)).prod (P.clopenCommonStagePullback (j i))) ⋙
        P.clopenCommonStageTensor (Xi i)) ∧
    (∀ n : ℕ, Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n)) ∧
    (∀ (m n : ℕ) (h : n ≤ m), Nonempty
      (coefficientFiniteQuotientDerived P.coefficients.l P.extension X.left h ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        finiteDerivedPullback P.coefficients.l P.extension m (j i).left ⋙
          coefficientFiniteQuotientDerived P.coefficients.l P.extension (Xi i).left h)) := by
  sorry

/-- Integral finite-Tor restriction, including detection of each common interval
uniformly over every finite reduction.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: commute restriction with derived reduction and the strict Roos functor.
Completeness is the Roos triangle with its canonical reduction unit, hence is
componentwise. Apply finiteClopen_finite_bounds at every positive exponent; the
same a,b is retained, so these bounds are uniform in all reductions. A finite
union of the component intervals supplies common bounds for the inverse. -/
theorem finiteClopen_integral_bounds (K : sfIntegralConstructibleCategory
    P.coefficients.l P.extension X.left) :
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K.obj ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((P.clopenIntegralPullback (j i)).obj K).obj) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) ⊆ Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b)) := by
  have hred (i : I) (n : ℕ) : Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
          K.obj) ≅
      (scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
        ((P.clopenIntegralPullback (j i)).obj K).obj) := by
    obtain ⟨e⟩ := (P.finiteClopen_tensor_and_reduction X Xi j hdisjoint hcover i).2.2.2.2.1 n
    exact ⟨e.app K⟩
  have htor (a b : ℤ) (hab : a ≤ b) :
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
          K.obj) a b) ↔
      ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
          ((P.clopenIntegralPullback (j i)).obj K).obj) a b) := by
    constructor
    · intro h i n
      obtain ⟨e⟩ := hred i n
      exact clopenTorAmplitude_of_iso e
        (((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab).mp (h n) i)
    · intro h n
      apply ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab).mpr
      intro i
      obtain ⟨e⟩ := hred i n
      exact clopenTorAmplitude_of_iso e.symm (h i n)
  refine ⟨?_, ?_, htor⟩
  · constructor
    · intro h i
      obtain ⟨a, b, hab, ht⟩ := h.2
      exact ⟨((P.clopenIntegralPullback (j i)).obj K).property,
        a, b, hab, (htor a b hab).mp ht i⟩
    · intro h
      have hi := fun i ↦ (h i).2
      choose a b hab ht using hi
      obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
      obtain ⟨d, hd⟩ := (Set.finite_range b).bddAbove
      refine ⟨K.property, min c d, max c d, min_le_max, ?_⟩
      apply (htor _ _ min_le_max).mpr
      intro i n
      exact clopenTorAmplitude_mono (ht i n)
        ((min_le_left c d).trans (hc (Set.mem_range_self i)))
        ((hd (Set.mem_range_self i)).trans (le_max_right c d))
  · intro a b hab
    constructor
    · intro h i n
      obtain ⟨e⟩ := hred i n
      rw [← clopenCohomologicalSupport_iso e]
      exact ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab).mp
        (h n) i
    · intro h n
      apply ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab).mpr
      intro i
      obtain ⟨e⟩ := hred i n
      rw [clopenCohomologicalSupport_iso e]
      exact h i n

/-- Lift the canonical constructible pullback to the integral finite-Tor category.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTorPullback (i : I) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X.left ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension (Xi i).left :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left).lift
    ((finiteTorConstructibleIntegral P.coefficients.l P.extension X.left).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension (j i).left)
    (fun K ↦ (P.finiteClopen_integral_bounds X Xi j hdisjoint hcover
      ⟨K.obj, K.property.1⟩).1.mp K.property i)

/-- Integral, rationalized, and common-stage constructible restriction equivalences.
The finite-Tor field categories are the very same categories by definition.
Source: blueprint section-invariant well-definedness, coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 9--11. The exact module equivalence preserves every reduction
and the strict Roos construction. Completeness, constructible reductions, and
bounds uniform in the positive level are thus componentwise. Finiteness of I
provides one common interval, both for cohomology and Tor. Restrict the integral
equivalence. Rationalization has unchanged objects and tensors each Hom with E;
finite products commute with that tensor via coordinate insertion and summation.
At the algebraically closed stage choose the finite compositum of all component
fields, glue there, and represent arrows there. Equality is checked after a further
finite compositum, proving full faithfulness and essential surjectivity. The empty
family gives the zero category, equivalent to the empty product category. -/
theorem finiteClopen_constructible_equivalences :
    (Functor.pi' (fun i ↦ P.clopenIntegralPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenIntegralTorPullback X Xi j
      hdisjoint hcover i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenRationalPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenCommonStagePullback (j i))).IsEquivalence := by
  sorry

/-- Scalar extension commutes with the same restrictions, for arbitrary finite
coefficient extensions, including the identity map. Rationalization is compatible
with the integral restriction equivalence.
Source: blueprint coefficient transport, steps 6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: on strict K-flat representatives the two scalar/restriction composites
have identical pure-tensor maps at every quotient of the target coefficient
ring, with the same transition equations. Restricting Roos gives the natural
integral comparison. The rational comparison is its linear extension, and common
stages compute these same comparisons after a finite compositum. -/
theorem finiteClopen_scalar_extension (i : I)
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι X.left ⋙
          integralDerivedPullback P.coefficients.l L (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι (Xi i).left) ∧
    Nonempty (P.clopenIntegralPullback (j i) ⋙
        sfRationalConstructibleLocalization P.coefficients.l P.extension (Xi i).left ≅
      sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
        P.clopenRationalPullback (j i)) := by
  constructor
  · obtain ⟨eY⟩ := P.clopenScalarCompletion X.left L ι
    obtain ⟨eXi⟩ := P.clopenScalarCompletion (Xi i).left L ι
    obtain ⟨eR⟩ := P.clopenIntegralPullbackInclusion (j i)
    exact clopenScalarSquare
      (sfIntegralConstructible P.coefficients.l P.extension X.left).ι
      (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι
      (integralDerivedPullback P.coefficients.l P.extension (j i).left)
      (integralDerivedPullback P.coefficients.l L (j i).left)
      (integralScalarExtension P.coefficients.l P.extension L ι X.left)
      (integralOrdinaryDerivedScalar P.coefficients.l P.extension L ι X.left)
      (integralScalarExtension P.coefficients.l P.extension L ι (Xi i).left)
      (integralOrdinaryDerivedScalar P.coefficients.l P.extension L ι (Xi i).left)
      (P.clopenIntegralPullback (j i)) eY eXi eR
      (scalarPullbackOrdinary P.coefficients.l P.extension L ι (j i).left)
  · exact P.clopenRationalPullbackComparison (j i)

/-- Restriction preserves the specified coefficient units at every stage.
Source: blueprint coefficient transports, steps 5--6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the sheaf-level coefficient ring restricts to the component coefficient
ring, by localization of constant sheafification and sectionwise integral limits.
The regular modules therefore restrict to regular modules. The finite K-flat
and integral strict Roos formulas preserve this identification in degree zero.
Rationalization and the common-stage representative functors preserve these
isomorphisms, with no restriction on the chosen finite coefficient stage. -/
theorem finiteClopen_coefficient_units (i : I) :
    (∀ n : ℕ, Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
          (finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ≅
        finiteConstantCoefficientObject P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty ((P.clopenIntegralPullback (j i)).obj (P.clopenIntegralUnit X.left) ≅
      P.clopenIntegralUnit (Xi i).left) ∧
    Nonempty ((P.clopenRationalPullback (j i)).obj (P.clopenRationalUnit X.left) ≅
      P.clopenRationalUnit (Xi i).left) ∧
    ∀ B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
      Nonempty ((P.clopenCommonStagePullback (j i)).obj (P.clopenCommonStageUnit X.left B) ≅
        P.clopenCommonStageUnit (Xi i).left B) := by
  sorry

/-- The empty family forces the empty scheme and has the terminal product category.
Source: Stacks 04TS and the empty covering sheaf axiom
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the union of the empty family of images is empty, so the covering condition
makes X empty. Functions on an empty index type and their coordinatewise morphisms
are unique. The preceding equivalences identify each source category with that
product; this includes zero sheaves and complexes, with no chosen nonzero component. -/
theorem finiteClopen_empty [IsEmpty I] (n : ℕ) (integral : Bool) :
    IsEmpty X.left ∧
      Subsingleton (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))) ∧
      ∀ F G : (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
        Subsingleton (F ⟶ G) := by
  refine ⟨⟨fun x ↦ ?_⟩, inferInstance, fun _ _ ↦ ⟨fun f g ↦ funext (fun i ↦ isEmptyElim i)⟩⟩
  have hx : x ∈ ⋃ i, Set.range (j i).left := by rw [hcover]; trivial
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact isEmptyElim i

/-- The completed coefficient identification and its constructible comparison.
It relates the module-derived equivalence to the actual completed pullback;
completed pullback on arbitrary unbounded objects is not asserted to be an equivalence.
Source: Stacks 04TS; blueprint integral finite-clopen transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restriction preserves sectionwise inverse limits, so the compatible finite
constant-ring identifications give the completed ring identification. Transport
scalars along its inverse. On complete objects the normalized Roos construction
computes the original restriction, with the original canonical reduction units.
This identifies the two restrictions naturally on the full integral subcategory. -/
theorem finiteClopen_integral_restriction_identification (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left 0 true) ≅
        completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension (Xi i).left)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left 0 true))) ≌
        DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left 0 true) ⋙ e.functor ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι) := by
  sorry

end Decomposition
end PurityFiniteSetting
end WeilConjectures
