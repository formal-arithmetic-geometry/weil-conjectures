/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.CompletedSupportIntermediateTowerCore
import Sheaf.Paper.CompletedSupportExchangeReduction
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-! # Finite origins and successive completed compact-support exchange

Source: Stacks 099M, 099N and 099R; the final compatibility paragraph of
thm-cbc-complete-proetale.
(blueprint: lem-cbc-completed-support-intermediate-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
open AlgebraicGeometry.ProEtale.StrictTower
open OrderedExchange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Quotient completion with the actual completed coefficient action.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
abbrev ringCompletion (T : Scheme.{t}) :=
  completedReductionTower T d ⋙ completedRlim T (d.completedRing T)

/-- Its specified augmented strict-tower unit.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringUnit (T : Scheme.{t}) : 𝟭 (d.derived T) ⟶ ringCompletion d T :=
  (d.constantRlimAdjunction T).unit ≫
    whiskerRight (completedReductionAugmentation d T) (completedRlim T (d.completedRing T))

/-- The completed-ring representative of the intermediate object H, with real data.
Source: blueprint intermediate object
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringSupport {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :=
  (cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p ⋙ ringCompletion d Y

/-- Coefficient restriction of completion, fixed by rho and the normalized limit map.
Source: Stacks 099M, 0A07 (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringCompletionRestriction (T : Scheme.{t}) :
    ringCompletion d T ⋙ res d T ≅ res d T ⋙ completion d T :=
  isoWhiskerLeft (completedReductionTower T d) (OrderedExchange.lambda d T) ≪≫
    isoWhiskerRight (rho d T) (rlim (A := A) T)

/-- Res(H) is precisely the specified completed constant-coefficient support object.
Source: blueprint intermediate object; Stacks 099M
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringSupportRestriction {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    ringSupport d j p ⋙ res d Y ≅ res d X ⋙ completed d j p :=
  isoWhiskerLeft ((cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p)
      (ringCompletionRestriction d Y) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (cbcEndpointOpen d j).mapDerivedCategory (OrderedExchange.chi d p) ≪≫
        isoWhiskerRight (cbcEndpointDerivedScalarOpen d j) (push (A := A) p))
      (completion d Y)

/-- Finite-coefficient extension with the actual P_n action.
Source: Stacks 03DI (blueprint: lem-cbc-completed-support-intermediate-tower). -/
abbrev finiteOpen {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] (n : ℕ) :=
  proEtaleRingDerivedOpenExtension j (d.finiteRing U n) (d.finiteRing X n)
    (d.finiteRingIso j n)

/-- Its unit-normalized exact derived adjunction.
Source: Stacks 03DI (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteOpenAdj {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] (n : ℕ) :
    finiteOpen d j n ⊣ d.finitePull j n :=
  (show proEtaleRingOpenExtension j (d.finiteRing U n) (d.finiteRing X n)
      (d.finiteRingIso j n) ⊣ proEtaleRingModulePullback j (d.finiteRing U n)
        (d.finiteRing X n) (d.finiteRingIso j n) from Adjunction.ofIsRightAdjoint _)
    |>.mapDerivedCategoryRightDerivedAdjunction
      |>.ofNatIsoRight (proEtaleRingModulePullback j (d.finiteRing U n)
        (d.finiteRing X n) (d.finiteRingIso j n)).rightDerivedFunctorIsoMapDerivedCategory

/-- The P_n-linear open tensor map is the mate of the actual reduction/pullback map.
Source: Stacks 06YY, 03DI (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteOpenTensor {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] (n : ℕ) :
    d.reduction X n ⋙ finiteOpen d j n ⟶
      (cbcEndpointOpen d j).mapDerivedCategory ⋙ d.reduction U n :=
  (mateEquiv (cbcEndpointDerivedOpenAdj d j) (finiteOpenAdj d j n)).symm
    (d.chi j n).inv

/-- The finite proper projection, before forgetting its quotient-ring action.
Source: Stacks 099N (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteProperProjection {U Y : Scheme.{t}} (p : U ⟶ Y) (n : ℕ) :
    d.push p ⋙ d.reduction Y n ⟶ d.reduction U n ⋙ d.finitePush p n :=
  mateEquiv (proEtaleRingDerivedAdjunction p (d.completedRing Y) (d.completedRing U)
    (d.integralRingIso p))
    (proEtaleRingDerivedAdjunction p (d.finiteRing Y n) (d.finiteRing U n)
      (d.finiteRingIso p n)) (d.chi p n).hom

/-- The finite open tensor mate is invertible.
Source: Stacks 03DI, 06YY (blueprint: lem-cbc-completed-support-intermediate-tower).
Proof: the reduction/pullback comparison is itself the inverse mate of the canonical
restriction/pullback isomorphism under the scalar-extension adjunctions. The iterated
mates identity identifies its inverse open mate with conjugation of that isomorphism
under the composite open/scalar adjunctions. Conjugation preserves isomorphisms.
(blueprint: lem-cbc-completed-support-finite-open-tensor-iso). -/
theorem finiteOpenTensor_isIso {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j]
    (n : ℕ) : IsIso (finiteOpenTensor d j n) := by
  let a := cbcEndpointDerivedOpenAdj d j
  let b := finiteOpenAdj d j n
  let x := proEtaleRingDerivedExtensionAdjunction (d.projection X n)
  let u := proEtaleRingDerivedExtensionAdjunction (d.projection U n)
  let q := proEtaleRingRestrictionDerivedPullback j
    (d.completedRing U) (d.finiteRing U n) (d.completedRing X) (d.finiteRing X n)
    (d.projection U n) (d.projection X n) (d.integralRingIso j)
    (d.finiteRingIso j n) (d.projection_comm j n)
  change IsIso (((mateEquiv a b).symm
    ((mateEquiv u x).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans)
  rw [iterated_mateEquiv_conjugateEquiv_symm a b x u]
  change IsIso ((conjugateEquiv (a.comp u) (x.comp b)).symm q.inv)
  infer_instance

private theorem exactDerivedReflects
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro q
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ q).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso q) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem restrictionReflects (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionDerivedRestrict T φ).ReflectsIsomorphisms := by
  have : (reductionRestrict T φ).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties φ).2.2
  exact exactDerivedReflects (reductionRestrict T φ)

private theorem ringTowerUnit_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completedReductionTower T d).map ((ringUnit d T).app K)) := by
  have : (proEtaleRingRestrictScalars (exchangeScalar d T)).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (exchangeScalar d T)).2.2
  have : (exchangeTowerModuleRes d T).ReflectsIsomorphisms := inferInstance
  have : (exchangeTowerRes d T).ReflectsIsomorphisms :=
    exactDerivedReflects (exchangeTowerModuleRes d T)
  have h := (rho_unit d T K).2
  change (res d T).map ((ringUnit d T).app K) ≫
    (ringCompletionRestriction d T).hom.app K = (unit d T).app ((res d T).obj K) at h
  have hu := (strictUnits d (𝟙 T)).2
  have : IsIso ((reduction d T).map ((unit d T).app ((res d T).obj K))) :=
    NatIso.isIso_app_of_isIso (whiskerRight (unit d T) (reduction d T)) _
  have : IsIso ((reduction d T).map ((res d T).map ((ringUnit d T).app K)) ≫
      (reduction d T).map ((ringCompletionRestriction d T).hom.app K)) := by
    rw [← Functor.map_comp, h]
    infer_instance
  have : IsIso ((reduction d T).map ((res d T).map ((ringUnit d T).app K))) :=
    IsIso.of_isIso_comp_right _ ((reduction d T).map
      ((ringCompletionRestriction d T).hom.app K))
  have : IsIso ((exchangeTowerRes d T).map
      ((completedReductionTower T d).map ((ringUnit d T).app K))) :=
    (NatIso.isIso_map_iff (rho d T) ((ringUnit d T).app K)).mpr (by
      change IsIso ((reduction d T).map ((res d T).map ((ringUnit d T).app K)))
      infer_instance)
  exact isIso_of_reflects_iso _ (exchangeTowerRes d T)

/-- The finite reduction of the completed ring unit is invertible.
Source: Stacks 099M, 099N (blueprint: lem-cbc-completed-support-intermediate-tower).
Proof: rho_unit transports the completed-ring unit to the constant-coefficient unit.
The strictUnits theorem makes its full constant reduction invertible. Transport back
through rho and reflect the isomorphism along exact scalar restriction on strict
towers, using homology to prove conservativity on derived categories. Evaluate at n
and use completedReductionEvaluation; exact quotient scalar restriction reflects
the resulting finite isomorphism.
(blueprint: lem-cbc-completed-support-finite-ring-unit-iso). -/
theorem finiteRingUnit_isIso {U : Scheme.{t}} (n : ℕ) :
    IsIso (whiskerRight (ringUnit d U) (d.reduction U n)) := by
  have h (K : d.derived U) :
      IsIso ((d.reduction U n).map ((ringUnit d U).app K)) := by
    have := ringTowerUnit_isIso d U K
    let E := reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n
    have : IsIso ((reductionDerivedRestrict U (d.projection U n)).map
        ((d.reduction U n).map ((ringUnit d U).app K))) :=
      (NatIso.isIso_map_iff (asIso (completedReductionEvaluation U d n))
        ((ringUnit d U).app K)).mp (by
          change IsIso (E.map ((completedReductionTower U d).map ((ringUnit d U).app K)))
          infer_instance)
    have := restrictionReflects U (d.projection U n)
    exact isIso_of_reflects_iso _ (reductionDerivedRestrict U (d.projection U n))
  rw [NatTrans.isIso_iff_isIso_app]
  exact h

/-- Finite tensor and completion maps are invertible without a uniform cohomological bound.
Source: Stacks 099M, 099N; node proof Steps 5--6.
Proof: combine finiteOpenTensor_isIso, proved by the iterated mates identity, with
finiteRingUnit_isIso, proved by normalized scalar transport of the strict unit.
Both statements hold in P_n modules; exact scalar restriction reflects isomorphisms.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem finiteUnits {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] (n : ℕ) :
    IsIso (finiteOpenTensor d j n) ∧
      IsIso (whiskerRight (ringUnit d U) (d.reduction U n)) := by
  exact ⟨finiteOpenTensor_isIso d j n, finiteRingUnit_isIso d n⟩

/-- The actual P_n-linear comparison H_n -> Rp_n* c! K_n, constructed before any origins.
Source: blueprint finite comparisons (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteComparison {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    ringSupport d j p ⋙ d.reduction Y n ⟶
      d.reduction X n ⋙ finiteOpen d j n ⋙ d.finitePush p n :=
  let v := whiskerLeft ((cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p)
    (whiskerRight (ringUnit d Y) (d.reduction Y n))
  letI := (finiteUnits d (𝟙 Y) n).2
  letI : IsIso v := inferInstance
  CategoryTheory.inv v ≫
    whiskerLeft (cbcEndpointOpen d j).mapDerivedCategory (finiteProperProjection d p n) ≫
    whiskerRight (@asIso _ _ _ _ (finiteOpenTensor d j n) (finiteUnits d j n).1).inv
      (d.finitePush p n)

private theorem finiteComparison_isIso {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) : IsIso (finiteComparison d j p n) := by
  have hp (E : d.derived U) : IsIso ((finiteProperProjection d p n).app E) := by
    let a := proEtaleRingDerivedAdjunction p (d.completedRing Y) (d.completedRing U)
      (d.integralRingIso p)
    let b := proEtaleRingDerivedAdjunction p (d.finiteRing Y n) (d.finiteRing U n)
      (d.finiteRingIso p n)
    have he : (finiteProperProjection d p n).app E = d.finiteProjection p E n := by
      apply (b.homEquiv _ _).symm.injective
      dsimp only [b, Functor.comp_obj]
      rw [AdicCoefficientDatum.finiteProjection, Equiv.symm_apply_apply]
      exact mateEquiv_counit a b (TwoSquare.mk _ _ _ _ (d.chi p n).hom) E
    rw [he]
    infer_instance
  have : IsIso (finiteProperProjection d p n) := NatIso.isIso_of_isIso_app _
  have := (finiteUnits d (𝟙 Y) n).2
  unfold finiteComparison
  infer_instance

attribute [local irreducible] finiteComparison

/-- The retained etale antecedent is exactly Rp_et* c_et! L_n, in D+ separately at n.
Source: Stacks 03DI, 099R (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteAntecedent {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (n : ℕ)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{t + 1} (ProEtale.PbcQuotient d n)))) :=
  (Etale.rightDerivedLowerStarPlus (ModuleCat.{t + 1} (ProEtale.PbcQuotient d n)) p).obj
    ((Etale.openImmersionLowerShriek
      (ModuleCat.{t + 1} (ProEtale.PbcQuotient d n)) j).mapDerivedCategoryPlus.obj L)

section TwoSteps
variable {X U Y V Z X' U' Y' V' Z' : Scheme.{t}}
variable (c : X ⟶ U) (p : U ⟶ Y) (i : Y ⟶ V) (q : V ⟶ Z)
variable (c' : X' ⟶ U') (p' : U' ⟶ Y') (i' : Y' ⟶ V') (q' : V' ⟶ Z')
variable [IsOpenImmersion c] [IsOpenImmersion i]
variable [IsOpenImmersion c'] [IsOpenImmersion i']
variable (x : X' ⟶ X) (u : U' ⟶ U) (y : Y' ⟶ Y) (v : V' ⟶ V) (z : Z' ⟶ Z)

/-- Source of x_h(H), identified with L(G_z F_h F_f M) using theta_f.
Source: blueprint first substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def firstSource :
    completed d c p ⋙ completed d i q ⋙ completePull d z ⟶
      reduction d X ⋙ tower (A := A) c p ⋙ tower (A := A) i q ⋙ G A z ⋙
        rlim (A := A) Z' :=
  whiskerLeft (completed d c p) (exchangeSource d i q z) ≫
    whiskerRight (whiskerRight (whiskerRight (theta d c p) (tower (A := A) i q))
      (G A z)) (rlim (A := A) Z')

/-- Target of x_h(H), retaining theta_f and the completed pullback reduction at Y.
Source: blueprint first substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def firstTarget :
    completed d c p ⋙ completePull d y ⋙ completed d i' q' ⟶
      reduction d X ⋙ tower (A := A) c p ⋙ G A y ⋙ tower (A := A) i' q' ⋙
        rlim (A := A) Z' :=
  whiskerLeft (completed d c p) (exchangeTarget d i' q' y) ≫
    whiskerRight (whiskerRight (whiskerRight (theta d c p) (G A y))
      (tower (A := A) i' q')) (rlim (A := A) Z')

/-- Source for Bhat_h'(x_f), using mu_h' and the same unit-normalized pullback reduction.
Source: blueprint second substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def secondSource :
    completed d c p ⋙ completePull d y ⋙ completed d i' q' ⟶
      reduction d X ⋙ tower (A := A) c p ⋙ G A y ⋙ tower (A := A) i' q' ⋙
        rlim (A := A) Z' :=
  whiskerLeft (completed d c p ⋙ completePull d y) (mu d i' q') ≫
    whiskerRight (whiskerRight
      (whiskerLeft (completed d c p) (pullReduction d y) ≫
        whiskerRight (theta d c p) (G A y)) (tower (A := A) i' q')) (rlim (A := A) Z')

/-- Target for Bhat_h'(x_f), with the intermediate reduction theta_f' made explicit.
Source: blueprint second substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def secondTarget :
    completePull d x ⋙ completed d c' p' ⋙ completed d i' q' ⟶
      reduction d X ⋙ G A x ⋙ tower (A := A) c' p' ⋙ tower (A := A) i' q' ⋙
        rlim (A := A) Z' :=
  whiskerLeft (completePull d x ⋙ completed d c' p') (mu d i' q') ≫
    whiskerRight (whiskerRight
      (whiskerLeft (completePull d x) (theta d c' p') ≫
        whiskerRight (pullReduction d x) (tower (A := A) c' p'))
      (tower (A := A) i' q')) (rlim (A := A) Z')

private theorem transport_first
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (S : C ⥤ D) (R : D ⥤ E) (T : C ⥤ E) (θ : S ⋙ R ⟶ T)
    {F G : D ⥤ H} {P Q : E ⥤ H}
    (a : F ⟶ G) (b : F ⟶ R ⋙ P) (c : G ⟶ R ⋙ Q) (e : P ⟶ Q)
    (h : a ≫ c = b ≫ whiskerLeft R e) :
    whiskerLeft S a ≫ (whiskerLeft S c ≫ whiskerRight θ Q) =
      (whiskerLeft S b ≫ whiskerRight θ P) ≫ whiskerLeft T e := by
  ext K
  have hh := congr_app h (S.obj K)
  have hn := e.naturality (θ.app K)
  simp only [Functor.comp_obj] at hn
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj] at hh ⊢
  rw [← Category.assoc, hh, Category.assoc, ← hn, Category.assoc]

private theorem transport_second
    {C D E F G : Type*} [Category C] [Category D] [Category E] [Category F] [Category G]
    (R : D ⥤ E) (H : E ⥤ F) (L : F ⥤ G) (B : D ⥤ G)
    (μ : B ⟶ R ⋙ H ⋙ L) {S T : C ⥤ D} {P Q : C ⥤ E}
    (a : S ⟶ T) (α : T ⋙ R ⟶ Q) (β : S ⋙ R ⟶ P) (e : P ⟶ Q)
    (h : whiskerRight a R ≫ α = β ≫ e) :
    whiskerRight a B ≫
        (whiskerLeft T μ ≫ whiskerRight (whiskerRight α H) L) =
      (whiskerLeft S μ ≫ whiskerRight (whiskerRight β H) L) ≫
        whiskerRight (whiskerRight e H) L := by
  ext K
  have hh := congr_app h K
  have hn := μ.naturality (a.app K)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj] at hh ⊢
  rw [← Category.assoc, hn]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun w ↦ μ.app (S.obj K) ≫ L.map (H.map w)) hh

private theorem transport_endpoints
    {C D E F G H I : Type*} [Category C] [Category D] [Category E] [Category F]
    [Category G] [Category H] [Category I]
    (S : C ⥤ D) (P : D ⥤ E) (R : D ⥤ F) (R' : E ⥤ G)
    (V : F ⥤ G) (Q : G ⥤ H) (L : H ⥤ I) (B : E ⥤ I) (T : C ⥤ F)
    (μ : B ⟶ R' ⋙ Q ⋙ L) (α : P ⋙ R' ⟶ R ⋙ V) (θ : S ⋙ R ⟶ T) :
    whiskerLeft S (whiskerLeft P μ ≫ whiskerRight (whiskerRight α Q) L) ≫
        whiskerRight (whiskerRight (whiskerRight θ V) Q) L =
      whiskerLeft (S ⋙ P) μ ≫
        whiskerRight (whiskerRight (whiskerLeft S α ≫ whiskerRight θ V) Q) L := by
  ext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]

/-- Both substitution identities, as equalities of natural transformations, with all
four endpoint comparisons displayed. Source: blueprint final compatibility sentence.
Proof: apply exchangeSubstitution for h at the complete intermediate object, then
substitute theta_f and use naturality of the strict e_h. This proves the first equation.
For the second, apply naturality of mu_h' to x_f, substitute the strict reduction square
completedExchange_reduction for f, and use functoriality of F_h' and Rlim. Expanding
exchangeTarget makes firstTarget and secondSource equal by functoriality. These
computations occur in the strict diagram category before evaluation. They apply to every
derived input and hence are natural in the original K.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem twoSubstitutions
    [QuasiCompact c] [QuasiCompact c'] [QuasiCompact i] [QuasiCompact i']
    [IsProper p] [IsProper p'] [IsProper q] [IsProper q']
    (hc : x ≫ c = c' ≫ u) (hp : u ≫ p = p' ≫ y)
    (hi : y ≫ i = i' ≫ v) (hq : v ≫ q = q' ≫ z)
    (sc : IsPullback x c' c u) (_sp : IsPullback u p' p y)
    (si : IsPullback y i' i v) (_sq : IsPullback v q' q z) :
    (whiskerLeft (completed d c p)
        (completedExchange d i q i' q' y v z hi hq si) ≫
      firstTarget d c p i' q' y =
      firstSource d c p i q z ≫
        whiskerLeft (reduction d X ⋙ tower (A := A) c p)
          (whiskerRight (strictExchange i q i' q' y v z hi hq si) (rlim (A := A) Z'))) ∧
    (whiskerRight (completedExchange d c p c' p' x u y hc hp sc) (completed d i' q') ≫
      secondTarget d c' p' i' q' x =
      secondSource d c p i' q' y ≫
        whiskerLeft (reduction d X)
          (whiskerRight
            (whiskerRight (strictExchange c p c' p' x u y hc hp sc)
              (tower (A := A) i' q')) (rlim (A := A) Z'))) ∧
    firstTarget d c p i' q' y = secondSource d c p i' q' y := by
  have eh := (exchangeSubstitution d i q i' q' y v z hi hq si _sq).1
  have ef := completedExchange_reduction d c p c' p' x u y hc hp sc _sp
  refine ⟨?_, ?_, ?_⟩
  · exact transport_first (completed d c p) (reduction d Y)
      (reduction d X ⋙ tower (A := A) c p) (theta d c p)
      (completedExchange d i q i' q' y v z hi hq si)
      (exchangeSource d i q z) (exchangeTarget d i' q' y)
      (whiskerRight (strictExchange i q i' q' y v z hi hq si) (rlim (A := A) Z')) eh
  · exact transport_second (reduction d Y') (tower (A := A) i' q')
      (rlim (A := A) Z') (completed d i' q') (mu d i' q')
      (completedExchange d c p c' p' x u y hc hp sc)
      (whiskerLeft (completePull d x) (theta d c' p') ≫
        whiskerRight (pullReduction d x) (tower (A := A) c' p'))
      (whiskerLeft (completed d c p) (pullReduction d y) ≫
        whiskerRight (theta d c p) (G A y))
      (whiskerLeft (reduction d X) (strictExchange c p c' p' x u y hc hp sc))
      (by simpa only [Category.assoc] using ef)
  · exact transport_endpoints (completed d c p) (completePull d y) (reduction d Y)
      (reduction d Y') (G A y) (tower (A := A) i' q') (rlim (A := A) Z')
      (completed d i' q') (reduction d X ⋙ tower (A := A) c p)
      (mu d i' q') (pullReduction d y) (theta d c p)

end TwoSteps


/-- The constants-to-functions coefficient comparison commutes with actual inverse image.
Source: Stacks 09BT, 099R.
Proof: on each constant coefficient section both composites are the same constant
function. Sheafification uniqueness proves equality, and the prescribed finiteRingIso
is the constants/pullback comparison transported along these isomorphisms.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem finiteScalarSquare {U Y : Scheme.{t}} (f : U ⟶ Y) (n : ℕ) :
    (exchangeConstantIso f (ProEtale.PbcQuotient d n)).hom ≫
        (finiteOriginConstantIso U (ProEtale.PbcQuotient d n)).hom =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
          (finiteOriginConstantIso Y (ProEtale.PbcQuotient d n)).hom ≫
        (d.finiteRingIso f n).hom := by
  have he (T : Scheme.{t}) : pbcLevelConstantComparison T d n =
      finiteOriginConstantIso T (ProEtale.PbcQuotient d n) := by
    apply (pbcLevelConstantComparison_exists T d n).unique
    · exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec
    · intro V b
      exact ConcreteCategory.congr_hom
        (congr_app (toSheafify_naturality (ProEt.topology T)
          (AdicCoefficients.constants T (ProEtale.PbcQuotient d n))) V) b |>.symm
  dsimp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [he U, he Y, ← Functor.map_comp_assoc, Iso.hom_inv_id]
  change _ = (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

attribute [local irreducible] finiteOriginConstantIso

/-- The actual pullback/scalar comparison in finite constant coefficients.
Source: Stacks 03DA (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteScalarPull {U Y : Scheme.{t}} (f : U ⟶ Y) (n : ℕ) :=
  proEtaleRingRestrictionDerivedPullback f
    (exchangeConstantRing Y (ProEtale.PbcQuotient d n)) (d.finiteRing Y n)
    (exchangeConstantRing U (ProEtale.PbcQuotient d n)) (d.finiteRing U n)
    (finiteOriginConstantIso Y (ProEtale.PbcQuotient d n)).hom
    (finiteOriginConstantIso U (ProEtale.PbcQuotient d n)).hom
    (exchangeConstantIso f (ProEtale.PbcQuotient d n))
    (d.finiteRingIso f n) (finiteScalarSquare d f n)

/-- The ordinary finite scalar/open comparison, fixed by its right mate.
Source: Stacks 03DI, 03DA (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteScalarOpenInverse {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j]
    (n : ℕ) :
    finiteOriginToConstant X (ProEtale.PbcQuotient d n) ⋙
        openExtension (A := ProEtale.PbcQuotient d n) j ⟶
      finiteOpen d j n ⋙ finiteOriginToConstant U (ProEtale.PbcQuotient d n) :=
  (mateEquiv (finiteOpenAdj d j n)
    (openAdjunction (A := ProEtale.PbcQuotient d n) j)).symm
    (finiteScalarPull d j n).hom

/-- The coefficient-isomorphism mate is invertible before forgetting the scalar action.
Source: Stacks 03DA, 03DI.
Proof: finiteOriginConstantIso is a coefficient isomorphism, so exact scalar restriction
is an equivalence, with inverse restriction along its inverse. The ordinary open-unit
mate is identity on extension generators, and hence an isomorphism. Exact derivation
retains its unit normalization and invertibility.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem finiteScalarOpenInverse_isIso {X U : Scheme.{t}} (j : X ⟶ U)
    [IsOpenImmersion j] (n : ℕ) : IsIso (finiteScalarOpenInverse d j n) := by
  have he (T : Scheme.{t}) :
      (proEtaleRingRestrictScalars
        (finiteOriginConstantIso T (ProEtale.PbcQuotient d n)).hom).IsEquivalence := by
    let c := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
        (finiteOriginConstantIso T (ProEtale.PbcQuotient d n))
    exact inferInstanceAs (proEtaleScalarEquivalence T c).functor.IsEquivalence
  have hX := he X
  have hU := he U
  change IsIso (((mateEquiv (finiteOpenAdj d j n)
    (openAdjunction (A := ProEtale.PbcQuotient d n) j)).symm
      (TwoSquare.mk _ _ _ _ (finiteScalarPull d j n).hom)).natTrans)
  exact inverseMate_isIso_of_equivalences (finiteOpenAdj d j n)
    (openAdjunction (A := ProEtale.PbcQuotient d n) j)
      (TwoSquare.mk _ _ _ _ (finiteScalarPull d j n).hom)

/-- Direct image commutes with finite coefficient restriction with its fixed unit.
Source: Stacks 03DA, 0E48 (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteScalarPush {U Y : Scheme.{t}} (p : U ⟶ Y) (n : ℕ) :=
  proEtaleRingRestrictionDerivedDirectImage p
    (exchangeConstantRing Y (ProEtale.PbcQuotient d n)) (d.finiteRing Y n)
    (exchangeConstantRing U (ProEtale.PbcQuotient d n)) (d.finiteRing U n)
    (finiteOriginConstantIso Y (ProEtale.PbcQuotient d n)).hom
    (finiteOriginConstantIso U (ProEtale.PbcQuotient d n)).hom
    (exchangeConstantIso p (ProEtale.PbcQuotient d n))
    (d.finiteRingIso p n) (finiteScalarSquare d p n)

/-- Restriction of finite compact support to constant P_n coefficients.
Source: Stacks 03DA, 03DI (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteScalarSupport {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    finiteOpen d j n ⋙ d.finitePush p n ⋙
        finiteOriginToConstant Y (ProEtale.PbcQuotient d n) ⟶
      finiteOriginToConstant X (ProEtale.PbcQuotient d n) ⋙
        ordinary (A := ProEtale.PbcQuotient d n) j p :=
  letI := finiteScalarOpenInverse_isIso d j n
  whiskerLeft (finiteOpen d j n) (finiteScalarPush d p n).hom ≫
    whiskerRight (CategoryTheory.inv (finiteScalarOpenInverse d j n))
      (push (A := ProEtale.PbcQuotient d n) p)

/-- The normalized scalar realization preserves the identity finite scalar section.
Source: Stacks 03DA, 099R.
Proof: naturality of constant sheafification moves the identity ring homomorphism
past its unit; the remaining factor is the adjunct defining finiteScalarMap.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem originScalarUnit (T : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    etaleOriginScalars T Λ ≫ (finiteScalarMap Λ T Λ (RingHom.id Λ)).hom =
      ProEtale.finiteCoefficientScalarMap T Λ := by
  have h := finiteScalarMap_unit Λ T Λ (RingHom.id Λ)
  change etaleOriginScalars T Λ ≫ (finiteScalarMap Λ T Λ (RingHom.id Λ)).hom =
    (𝟙 _) ≫ ProEtale.finiteCoefficientScalarMap T Λ at h
  exact h.trans (Category.id_comp _)

/-- Realization of fixed finite modules compared with the normalized scalar realization.
Both send unit sections identically. Source: Stacks 03DA, 099R
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def originRealization (T : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    etaleOriginRealization T Λ ≅ C Λ T Λ (RingHom.id Λ) :=
  (pbcAssociatedRestriction_exists T Λ Λ
    ((adicLisseForget T).obj (etaleOriginRing T Λ))
    (ProEtale.finiteCoefficientRingSheaf T Λ)
    (etaleOriginScalars T Λ) (ProEtale.finiteCoefficientScalarMap T Λ)
    (RingHom.id Λ) (finiteScalarMap Λ T Λ (RingHom.id Λ))
    (originScalarUnit T Λ)).exists.choose

/-- The same comparison on bounded-below etale complexes in the ambient derived category.
Source: Stacks 099R (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def originDerived (T : Scheme.{t}) (n : ℕ) :
    DerivedCategory.Plus.ι ⋙ etaleOriginComparison T (ProEtale.PbcQuotient d n) ≅
      HD (ProEtale.PbcQuotient d n) T (ProEtale.PbcQuotient d n) (RingHom.id _) :=
  let Λ := ProEtale.PbcQuotient d n
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} Λ) T ⋙
      C Λ T Λ (RingHom.id Λ)).Additive := h_additive Λ T Λ (RingHom.id Λ)
  letI : PreservesFiniteLimits (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} Λ) T ⋙
      C Λ T Λ (RingHom.id Λ)) := h_finiteLimits Λ T Λ (RingHom.id Λ)
  letI : PreservesFiniteColimits (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} Λ) T ⋙
      C Λ T Λ (RingHom.id Λ)) := h_finiteColimits Λ T Λ (RingHom.id Λ)
  isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.mapDerivedCategoryNatIso
      (isoWhiskerLeft (ProEtale.comparisonUpperStar
        (ModuleCat.{t + 1} (ProEtale.PbcQuotient d n)) T)
        (originRealization T (ProEtale.PbcQuotient d n)))) ≪≫
    (H (ProEtale.PbcQuotient d n) T (ProEtale.PbcQuotient d n)
      (RingHom.id _)).mapDerivedCategoryPlusCompatibility.symm

/-- The second finite comparison is the proper etale mate after the exact open mate.
Its source is the prescribed antecedent and its target retains the actual finite action
through the faithful coefficient equivalence. Source: Stacks 099R, 03DI
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def finiteOriginSupport {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (ProEtale.PbcQuotient d n) ((d.reduction X n).obj K)) :
    (etaleOriginComparison Y (ProEtale.PbcQuotient d n)).obj
        (finiteAntecedent d j p n W.complex).obj ⟶
      (ordinary (A := ProEtale.PbcQuotient d n) j p).obj
        ((finiteOriginToConstant X (ProEtale.PbcQuotient d n)).obj
          ((d.reduction X n).obj K)) :=
  let Λ := ProEtale.PbcQuotient d n
  let L := (Etale.openImmersionLowerShriek
    (ModuleCat.{t + 1} Λ) j).mapDerivedCategoryPlus.obj W.complex
  (originDerived d Y n).hom.app (finiteAntecedent d j p n W.complex) ≫
    (hR Λ p Λ (RingHom.id Λ)).app L ≫
    (push (A := Λ) p).map
      ((hJ Λ j Λ (RingHom.id Λ)).hom.app W.complex ≫
        (openExtension (A := Λ) j).map
          ((originDerived d X n).inv.app W.complex ≫ W.iso.hom))

attribute [local irreducible] originDerived originRealization
  finiteScalarSupport finiteOriginSupport

/-- The retained origin comparison is the specified natural composite, rather than an
unrelated isomorphism to the same antecedent. Source: Stacks 099N, 099R.
Proof: the proper qcqs etale direct-image mate and the exact open mate are isomorphisms.
Their normalization with quotient scalar extension identifies this composite with
finiteComparison followed by the original alpha_n. This calculation is natural in
quotient-ring maps, so the retained witnesses respect quotient normalizations.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem retainedOrigins {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] (K : d.derived X)
    (_hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (ProEtale.PbcQuotient d n)
      ((d.reduction X n).obj K)) :
    ∀ n : ℕ, ∃ V : FiniteEtaleOriginWitness Y (ProEtale.PbcQuotient d n)
        ((d.reduction Y n).obj ((ringSupport d j p).obj K)),
      ∃ h : V.complex = finiteAntecedent d j p n (W n).complex,
      V.iso.hom ≫ (finiteOriginToConstant Y (ProEtale.PbcQuotient d n)).map
          ((finiteComparison d j p n).app K) ≫
        (finiteScalarSupport d j p n).app ((d.reduction X n).obj K) =
          eqToHom (congrArg (fun L ↦
            (etaleOriginComparison Y (ProEtale.PbcQuotient d n)).obj L.obj)
            h) ≫
          finiteOriginSupport d j p K n (W n) := by
  intro n
  let Λ := ProEtale.PbcQuotient d n
  have hfinite := finiteComparison_isIso d j p n
  have : IsIso (hR Λ p Λ (RingHom.id Λ)) := hR_isIso Λ p Λ (RingHom.id Λ)
  have : IsIso (finiteOriginSupport d j p K n (W n)) := by
    unfold finiteOriginSupport
    infer_instance
  have : IsIso (finiteScalarSupport d j p n) := by
    unfold finiteScalarSupport
    let := finiteScalarOpenInverse_isIso d j n
    infer_instance
  let a := (finiteOriginToConstant Y Λ).mapIso
    ((@asIso _ _ _ _ (finiteComparison d j p n) hfinite).app K) ≪≫
      (asIso (finiteScalarSupport d j p n)).app ((d.reduction X n).obj K)
  let V : FiniteEtaleOriginWitness Y Λ
      ((d.reduction Y n).obj ((ringSupport d j p).obj K)) :=
    ⟨finiteAntecedent d j p n (W n).complex,
      asIso (finiteOriginSupport d j p K n (W n)) ≪≫ a.symm⟩
  refine ⟨V, rfl, ?_⟩
  change (_ ≫ a.inv) ≫ _ ≫ _ = (𝟙 _) ≫ _
  rw [Category.id_comp, Category.assoc]
  change _ ≫ a.inv ≫ a.hom = _
  rw [Iso.inv_hom_id, Category.comp_id]
  rfl


/-- The comparison is P_n-linear and H has the intrinsic completion property. Every
finite origin has exactly the displayed D+ antecedent; no shared bound is chosen.
Source: Stacks 099M, 099N, 099R; node proof Steps 4--7.
Proof: coefficient restriction identifies ringSupport with completed constant support
by rho and lambda and preserves the completion units. The constant complete object
therefore transports to intrinsic completeness by the coefficient equivalence and the
Koszul/quotient-unit comparison. Finite proper projection and open tensor descent are
invertible before restriction. Apply the exact etale open comparison to the supplied
alpha_n and then the canonical qcqs proper direct-image mate to its D+ antecedent.
Use bounded-below injective representatives separately for each n. Scalar extension
and restriction compose to the same derived direct image, so the comparison is P_n
linear. Naturality in quotient scalars gives the quotient-transition and augmentation
compatibility; the strict normalization theorem records this compatibility on the
actual strict reduction tower, rather than choosing lifts of individual evaluations.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem finiteAndIntrinsic {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] (K : d.derived X)
    (_hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (ProEtale.PbcQuotient d n)
      ((d.reduction X n).obj K)) :
    d.TowerComplete Y ((ringSupport d j p).obj K) ∧
    (∀ n : ℕ, IsIso (finiteComparison d j p n)) ∧
    (∀ n : ℕ, ∃ V : FiniteEtaleOriginWitness Y (ProEtale.PbcQuotient d n)
        ((d.reduction Y n).obj ((ringSupport d j p).obj K)),
      V.complex = finiteAntecedent d j p n (W n).complex) := by
  have hcomplete : IsComplete d Y
      ((res d Y).obj ((ringSupport d j p).obj K)) := by
    apply (NatTrans.isIso_app_iff_of_iso (unit d Y)
      ((ringSupportRestriction d j p).app K)).mpr
    exact (completionUnits d j p).2.2.2.2 ((res d X).obj K)
  refine ⟨((restriction_complete d Y).1 _).mpr hcomplete,
    finiteComparison_isIso d j p, ?_⟩
  intro n
  obtain ⟨V, h, _⟩ := retainedOrigins d j p K _hK W n
  exact ⟨V, h⟩


/-- Completed-ring strict compact-support tower, retaining every quotient transition.
Source: blueprint finite compatibility
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
abbrev ringTowerSupport {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] := cbcTowerDerived (cbcEndpointOpen d j) ⋙ d.towerPush p

/-- Strict ringed proper projection, the same counit-tensor mate before evaluation.
Source: Stacks 099N (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringProperProjection {U Y : Scheme.{t}} (p : U ⟶ Y) :
    d.push p ⋙ completedReductionTower Y d ⟶ completedReductionTower U d ⋙ d.towerPush p :=
  mateEquiv (proEtaleRingDerivedAdjunction p (d.completedRing Y) (d.completedRing U)
    (d.integralRingIso p)) (d.towerAdjunction p) (d.reductionTowerPullbackIso p).hom

/-- The strict ordinary support reduction map before target completion.
Source: blueprint t_f (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringOrdinaryReduction {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    (cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p ⋙ completedReductionTower Y d ⟶
      completedReductionTower X d ⋙ ringTowerSupport d j p :=
  whiskerLeft (cbcEndpointOpen d j).mapDerivedCategory (ringProperProjection d p) ≫
    whiskerRight (cbcEndpointReduction d j).hom (d.towerPush p)

/-- The full strict reduction of the completed-ring unit is invertible.
Source: Stacks 099M.
Proof: rho_unit identifies the scalar restriction of the completed-ring unit with
the constant-coefficient unit, up to the canonical completion restriction isomorphism.
Apply strictUnits and rho, then reflect the isomorphism through exact scalar restriction
on the strict-tower derived category. Conservativity follows by applying homology.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem ringReducedUnit (T : Scheme.{t}) :
    IsIso (whiskerRight (ringUnit d T) (completedReductionTower T d)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ringTowerUnit_isIso d T

/-- Actual completed-ring strict theta, fixed by the ordinary counit-tensor map.
Source: blueprint strict comparison
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringTheta {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    ringSupport d j p ⋙ completedReductionTower Y d ⟶
      completedReductionTower X d ⋙ ringTowerSupport d j p :=
  letI := ringReducedUnit d Y
  let v := whiskerLeft ((cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p)
    (whiskerRight (ringUnit d Y) (completedReductionTower Y d))
  letI : IsIso v := inferInstance
  CategoryTheory.inv v ≫ ringOrdinaryReduction d j p

/-- Evaluation of the strict target using the specified finite proper and open maps.
Source: Stacks 099N, 03DI (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringTargetEvaluation {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (K : d.derived X) (n : ℕ) :
    (reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n).obj
        ((ringTowerSupport d j p).obj ((completedReductionTower X d).obj K)) ⟶
      (reductionDerivedRestrict Y (d.projection Y n)).obj
        ((d.finitePush p n).obj ((finiteOpen d j n).obj ((d.reduction X n).obj K))) :=
  let evY := reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n
  evY.map ((d.towerPush p).map (cbcEndpointReductionInv d j K)) ≫
    d.towerPushReductionEvaluation p ((cbcEndpointOpen d j).mapDerivedCategory.obj K) n ≫
    (reductionDerivedRestrict Y (d.projection Y n)).map
      ((d.finitePush p n).map
        ((@asIso _ _ _ _ (finiteOpenTensor d j n) (finiteUnits d j n).1).inv.app K))

/-- The strict output tower in constant coefficients, using the canonical coefficient maps.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ringTargetRestriction {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    completedReductionTower X d ⋙ ringTowerSupport d j p ⋙ exchangeTowerRes d Y ≅
      res d X ⋙ reduction d X ⋙ tower (A := A) j p :=
  isoWhiskerLeft (completedReductionTower X d ⋙ cbcTowerDerived (cbcEndpointOpen d j))
      (exchangeResPush d p) ≪≫
    isoWhiskerRight (isoWhiskerLeft (completedReductionTower X d)
      (cbcEndpointTowerScalarOpen d j)) (R A p) ≪≫
    isoWhiskerRight (rho d X) (tower (A := A) j p)

/-- One strict comparison gives the finite comparisons, their transitions and their
augmentation normalization, and restricts to exactly theta_f. Source: Stacks 099M, 099N.
Proof: the strict proper and open maps commute with the quotient augmentation by their
counit and open-unit mate formulas. Their evaluation formulas are respectively the
finite perfect-quotient projection and the finite open tensor map. Naturality of these
formulas with the completion unit proves the evaluated equation. The same mate
calculation with rho gives the scalar equation. Thus all quotient transitions and
augmentations are carried by these actual strict morphisms, with the specified finite
P_n-linear comparisons as their evaluations.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem strictFiniteCoherence {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] :
    IsIso (ringTheta d j p) ∧
    (whiskerLeft ((cbcEndpointOpen d j).mapDerivedCategory ⋙ d.push p)
        (whiskerRight (ringUnit d Y) (completedReductionTower Y d)) ≫ ringTheta d j p =
      ringOrdinaryReduction d j p) ∧
    (∀ (K : d.derived X) (n : ℕ),
      (reductionTowerDerivedEvaluation Y
          (reductionModuleRing Y (d.completedRing Y)) n).map ((ringTheta d j p).app K) ≫
        ringTargetEvaluation d j p K n =
      (completedReductionEvaluation Y d n).app ((ringSupport d j p).obj K) ≫
        (reductionDerivedRestrict Y (d.projection Y n)).map ((finiteComparison d j p n).app K)) ∧
    (whiskerRight (ringTheta d j p) (exchangeTowerRes d Y) ≫
        (ringTargetRestriction d j p).hom =
      whiskerLeft (ringSupport d j p) (rho d Y).hom ≫
        whiskerRight (ringSupportRestriction d j p).hom (reduction d Y) ≫
          whiskerLeft (res d X) (theta d j p)) := by
  sorry

/-- The intermediate-object assertion for the supplied compatible compactification tower.
The main declaration assembles the normalized intermediate comparison, intrinsic and
finite-origin conclusions. The exchange and two-substitution clauses are the natural
transformation statements exchangeSubstitution and twoSubstitutions above, specialized
to cf and cg and their induced base changes.
Source: main-20261015, thm-cbc-complete-proetale, final compatibility sentence;
Stacks 099M, 099N, 03DI, 03DJ, 0A07.
Proof: work through restriction to constant coefficients, using rho for the actual
strict reduction and lambda for Rlim. Complete the open extension before proper
pushforward. The completion reflector inverts its reduced unit; proper direct image
preserves complete objects. Apply strictFiniteCoherence and reconstructionNormalization
for theta and mu, and finiteAndIntrinsic for the separate D+ antecedents. The proper
and open finite mates are precisely finiteOriginSupport, as retainedOrigins states.
Apply the natural exchangeSubstitution first for cg and then for cf; naturality of
mu gives twoSubstitutions. All identities are in the derived strict diagram categories,
so quotient transitions, augmentations and naturality are retained before evaluation.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem completedSupportIntermediateTower {X Y Z : Scheme.{t}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (ProEtale.PbcQuotient d n)
      ((d.reduction X n).obj K)) :
    IsComplete d Y ((completed d T.cf.i T.cf.g).obj ((res d X).obj K)) ∧
    d.TowerComplete Y ((ringSupport d T.cf.i T.cf.g).obj K) ∧
    IsIso (theta d T.cf.i T.cf.g) ∧ IsIso (mu d T.cf.i T.cf.g) ∧
    (properCompletedOpen d T.cf.i T.cf.g ≫ limitCompletedOpen d T.cf.i T.cf.g =
      mu d T.cf.i T.cf.g) ∧
    (reducedUnit d T.cf.i T.cf.g ≫ theta d T.cf.i T.cf.g =
      ordinaryReduction d T.cf.i T.cf.g) ∧
    (∀ n : ℕ, IsIso (finiteComparison d T.cf.i T.cf.g n)) ∧
    (∀ n : ℕ, ∃ V : FiniteEtaleOriginWitness Y (ProEtale.PbcQuotient d n)
        ((d.reduction Y n).obj ((ringSupport d T.cf.i T.cf.g).obj K)),
      ∃ e : V.complex = finiteAntecedent d T.cf.i T.cf.g n (W n).complex,
      V.iso.hom ≫ (finiteOriginToConstant Y (ProEtale.PbcQuotient d n)).map
          ((finiteComparison d T.cf.i T.cf.g n).app K) ≫
        (finiteScalarSupport d T.cf.i T.cf.g n).app ((d.reduction X n).obj K) =
          eqToHom (congrArg (fun L ↦
            (etaleOriginComparison Y (ProEtale.PbcQuotient d n)).obj L.obj) e) ≫
          finiteOriginSupport d T.cf.i T.cf.g K n (W n)) := by
  have hc := completionUnits d T.cf.i T.cf.g
  have hn := reconstructionNormalization d T.cf.i T.cf.g
  have hf := finiteAndIntrinsic d T.cf.i T.cf.g K hK W
  exact ⟨hc.2.2.2.2 ((res d X).obj K), hf.1, hc.2.2.1, hc.2.2.2.1,
    hn.2, hn.1, hf.2.1, retainedOrigins d T.cf.i T.cf.g K hK W⟩

end AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
