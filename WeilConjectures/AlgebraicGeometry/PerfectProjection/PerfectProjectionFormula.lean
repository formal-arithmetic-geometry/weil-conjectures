/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.IdentityProjectionCompactification.ProjectionFormulaIdentityCompactification
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateSlicePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
meta import Mathlib.Lean.Meta.CongrTheorems
meta import Mathlib.Tactic.Set
meta import Mathlib.Util.TermReduce

/-!
# Perfect projection formula for completed coefficient reductions

Source: Weil conjectures blueprint, proper base change, order 1275; Stacks Project,
Cohomology on Sites, Tags 0B56 and 0944, and More on Algebra, Tag 0657
(blueprint: lemma-weil-pbc-perfect-projection-formula).

The completed ring is presented as the limit of constant finite quotient sheaves.
The recorded finite-coefficient comparisons identify this presentation with the
continuous-functions presentation, including its quotient maps. Tensors and derived
categories are ordinary and uncompleted. Natural numbers index positive exponents n+1.
-/

/- The completed-coefficient abbreviations carry extensionally identical sheafification
proofs that Lean stores under different auxiliary names. A single conversion beneath
`Functor.map` unfolds localization before reconciling them. This bounded tactic proves
that conversion by congruence and proof irrelevance; its output is kernel checked.
Only the listed item abbreviations may be unfolded. -/
local syntax (name := perfectProjectionExact) "perfect_projection_exact " term : tactic

meta section
open Lean Meta Elab Tactic
private def projectionConversionAliases : Array Name := #[
  `AlgebraicGeometry.Scheme.PerfectProjection.reductionMap,
  `AlgebraicGeometry.Scheme.PerfectProjection.baseChangeSource,
  `AlgebraicGeometry.Scheme.PerfectProjection.baseChangeTarget,
  `AlgebraicGeometry.Scheme.PerfectProjection.reduction,
  `AlgebraicGeometry.Scheme.PerfectProjection.pullback,
  `AlgebraicGeometry.Scheme.PerfectProjection.directImage,
  `AlgebraicGeometry.Scheme.PerfectProjection.projection,
  `AlgebraicGeometry.Scheme.PerfectProjection.exchange,
  `AlgebraicGeometry.Scheme.PerfectProjection.derived,
  `AlgebraicGeometry.Scheme.PerfectProjection.modules,
  `inferInstance]
private structure ProjectionConversionState where
  proofs : Std.HashMap (Expr × Expr) Expr := {}
  congruences : Std.HashMap (Expr × Array Bool) CongrTheorem := {}
private def projectionMetadataHEq (fuel : Nat) (left right : Expr) :
    StateRefT ProjectionConversionState MetaM Expr := do
  match fuel with
  | 0 => throwError "structural conversion exceeded its depth bound"
  | fuel + 1 =>
    let a := left.consumeMData
    let b := right.consumeMData
    if let some p := (← get).proofs.get? (a,b) then return p
    let p ← do
      if a == b then return ← mkHEqRefl a
      if (← isProof a) && (← isProof b) then
        return ← mkAppM ``proof_irrel_heq #[a,b]
      let fa := a.getAppFn
      let fb := b.getAppFn
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      if fa == fb && aa.size == bb.size && !aa.isEmpty then
        let info ← getFunInfoNArgs fa aa.size
        let fixed := aa.zip bb |>.map fun (x,y) => x == y
        let key := (fa,fixed)
        let thm ← match (← get).congruences.get? key with
          | some thm => pure thm
          | none => do
            let thm ← mkRichHCongr (← inferType fa) info
              (fixedFun := true) (fixedParams := fixed) (forceHEq := true)
            modify fun st => { st with congruences := st.congruences.insert key thm }
            pure thm
        let mut result := mkApp thm.proof fa
        for i in [:aa.size] do
          result := mkApp result aa[i]!
          match thm.argKinds[i+1]! with
          | .fixed => pure ()
          | .subsingletonInst => result := mkApp result bb[i]!
          | .eq | .heq =>
            result := mkApp result bb[i]!
            let expected ← whnf (← inferType result)
            let hp ← forallTelescope expected.bindingDomain! fun xs ty => do
              let hp ← match ty.eq?, ty.heq? with
                | some (_, x,y), _ => do
                  let h ← projectionMetadataHEq fuel x y
                  mkAppM ``eq_of_heq #[h]
                | _, some (_, x, _, y) => projectionMetadataHEq fuel x y
                | _, _ => throwError "unexpected congruence premise {ty}"
              mkLambdaFVars xs hp
            result := mkApp result hp
          | k => throwError "unexpected congruence argument {repr k}"
        return result
      if let some v ← delta? a (projectionConversionAliases.contains ·) then
        let h₁ ← mkHEqRefl a
        let h₂ ← projectionMetadataHEq fuel v.headBeta b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      if let some v ← delta? b (projectionConversionAliases.contains ·) then
        let h₁ ← projectionMetadataHEq fuel a v.headBeta
        let h₂ ← mkHEqRefl b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      match a,b with
      | .const n us, .const m vs =>
        if n == m && us.length == vs.length then
          if ← (us.zip vs).allM (fun (u,v) => isLevelDefEq u v) then
            return ← mkHEqRefl a
      | .sort u, .sort v =>
        if ← isLevelDefEq u v then return ← mkHEqRefl a
      | _, _ => pure ()
      throwError "structural conversion stopped at\n{a}\nVERSUS\n{b}"
    modify fun st => { st with proofs := st.proofs.insert (a,b) p }
    return p
termination_by fuel
end

open Lean Meta Elab Tactic in
@[local tactic perfectProjectionExact] private meta def evalPerfectProjectionExact : Tactic :=
    fun stx => withMainContext do
  let h : TSyntax `term := ⟨stx[1]⟩
  let p ← elabTerm h none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let source ← instantiateMVars (← inferType p)
  let target ← instantiateMVars (← getMainTarget)
  let (heq, _) ← (projectionMetadataHEq 1000 source target).run {}
  let eq ← mkAppM ``eq_of_heq #[heq]
  let result ← mkAppM ``Eq.mp #[eq,p]
  (← getMainGoal).assign result
  replaceMainGoal []

@[expose] public noncomputable section


set_option Elab.async true
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
-- Avoid scanning the large representative tactic states for unused tactics.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 30000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 2000] CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape
  CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.PerfectProjection

set_option linter.flexible false in
/-- Cached existing site infrastructure for the completed-coefficient proofs.
Source: Mathlib sheafification, sheaf limits and homological totalization instances
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply the existing instance without changing its mathematical structure. -/
theorem completedCommRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) CommRingCat.{u + 1} := inferInstance

set_option linter.flexible false in
/-- Cached existing site infrastructure for the completed-coefficient proofs.
Source: Mathlib sheafification, sheaf limits and homological totalization instances
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply the existing instance without changing its mathematical structure. -/
theorem completedRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) RingCat.{u + 1} := inferInstance

set_option linter.flexible false in
/-- Cached existing site infrastructure for the completed-coefficient proofs.
Source: Mathlib sheafification, sheaf limits and homological totalization instances
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply the existing instance without changing its mathematical structure. -/
theorem completedCommRingLimits (T : Scheme.{u}) :
    HasLimitsOfSize.{u + 1, u + 1} (Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  inferInstance

attribute [local instance 3000] completedCommRingWeakSheafify completedRingWeakSheafify
  completedCommRingLimits

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option linter.flexible false in
/-- The recorded completed ring, in its constant finite-quotient presentation.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ring (T : Scheme.{u}) := adicLisseCompletedRing T d.ideal

set_option linter.flexible false in
/-- The existing module category over this completed ring, at the mandated coefficient size.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev modules (T : Scheme.{u}) := proEtaleRingModules T (ring d T)

set_option linter.flexible false in
/-- The ordinary localization of module complexes, with no completion condition.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev derived (T : Scheme.{u}) := DerivedCategory (modules d T)

set_option linter.flexible false in
/-- The residue as an object of the ordinary derived category over the completed ring.
Source: blueprint order 1275, displayed formula
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev quotient (T : Scheme.{u}) (n : ℕ) : derived d T :=
  (DerivedCategory.singleFunctor (modules d T) 0).obj
    (CompletedConstantReduction.residue T d.ideal n)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option linter.flexible false in
/-- The projectionwise constant-ring comparison is a cone, including all tower arrows.
Source: Stacks 098T and blueprint order 1275, proof step 1
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: commute the quotient projection past the inverse-image functor, use the
constant-comparison naturality of the profinite inverse-image lemma, and then use
the limit cone equation for the quotient system on Y. -/
theorem coefficientCone_naturality {n m : ℕᵒᵖ} (a : n ⟶ m) :
    𝟙 ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)) ≫
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) m) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (m.unop + 1))) =
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))) ≫
      (adicLisseRingSystem X d.ideal).map a := by
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  change 𝟙 _ ≫ _ ≫ c.app m = (_ ≫ c.app n) ≫ _
  rw [Category.id_comp, Category.assoc, ← c.naturality]
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, limit.w]

set_option linter.flexible false in
/-- The actual inverse-limit comparison, characterized by its quotient projections.
Source: blueprint order 1275, coefficient identification
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def coefficientMap :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ⟶
      ring d X :=
  limit.lift (adicLisseRingSystem X d.ideal)
    { pt := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)
      π := { app := fun n ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
              (proEtaleConstantComparison f).app
                (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
             naturality := fun _ _ a ↦ coefficientCone_naturality d f a } }

set_option linter.flexible false in
/-- The specified comparison is invertible for the finite quotient tower.
Source: blueprint order 1275, proof step 1; Stacks 098T
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply profinite-coefficient inverse image to the quotient ring system.
The cone projection equations identify its canonical map with coefficientMap.
The function-sheaf and constant-sheaf presentations agree by the recorded finite
coefficient comparisons, naturally in every quotient transition. -/
theorem coefficientMap_isIso : IsIso (coefficientMap d f) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
    Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
      (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let c (T : Scheme.{u}) : proEtaleCoefficientTower T Q ⟶ adicLisseRingSystem T d.ideal :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [proEtaleCoefficientTower, Functor.comp_map, Q, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
  have hc (T : Scheme.{u}) : IsIso (c T) := by
    have : ∀ n, IsIso ((c T).app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
    exact NatIso.isIso_of_isIso_app _
  have : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  have hp := proEtale_profinite_coefficient_inverse_image Q
  have := hp.2.1 X Y f
  have := hc X
  have := hc Y
  have he : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f = proEtaleProfiniteComparison f Q ≫ limMap (c X) := by
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, coefficientMap, limit.lift_π,
      limMap_π]
    change _ ≫ _ ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, limMap_π]
    simp only [c, NatTrans.ofOpSequence_app, Category.comp_id]
    exact (hp.2.2.1 X Y f n).symm
  have : IsIso ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)))
    (coefficientMap d f)

set_option linter.flexible false in
/-- The canonical coefficient identification; only its invertibility is postponed.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def coefficients :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ≅
      ring d X :=
  @asIso _ _ _ _ (coefficientMap d f) (coefficientMap_isIso d f)

set_option linter.flexible false in
/-- The ordinary derived pullback with this specific completed coefficient identification.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev pullback :=
  proEtaleRingDerivedPullback f (ring d Y) (ring d X) (coefficients d f)

set_option linter.flexible false in
/-- The ordinary derived direct image with the same coefficient action.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev directImage :=
  proEtaleRingDerivedDirectImage f (ring d Y) (ring d X) (coefficients d f)

variable (aY : ProEtaleTensorModel Y (ring d Y))
  (aX : ProEtaleTensorModel X (ring d X))
  (K : derived d X)

set_option linter.flexible false in
/-- The existing canonical projection mate, with the completed coefficients specialized.
Source: Stacks 0B56 and blueprint order 1275
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev projection (P : derived d Y) :=
  proEtaleProjectionFormulaMate f (ring d Y) (ring d X)
    (coefficients d f) aY aX K P

set_option linter.flexible false in
/-- The full isomorphism locus of the specified projection morphism.
Source: blueprint order 1275, Detailed form
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def locus : ObjectProperty (derived d Y) :=
  fun P ↦ IsIso (projection d f aY aX K P)

attribute [local irreducible] coefficients SheafOfModules.monoidalClosed_kfg
  SheafOfModules.monoidalCategory
  CategoryTheory.tensorAdjunctionTotalInverse CategoryTheory.tensorAdjunctionTotal

set_option linter.flexible false in
private theorem strictPerfect_mem
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (F G : DerivedCategory C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (B : C) (hB : τ.isoLocus ((DerivedCategory.singleFunctor C 0).obj B))
    (T : CochainComplex C ℤ) (lo hi : ℤ)
    (hb : ∀ n : ℤ, n < lo ∨ hi < n → IsZero (T.X n))
    (rank : ℤ → ℕ) (i : ∀ n, T.X n ⟶ ∏ᶜ fun _ : Fin (rank n) ↦ B)
    (p : ∀ n, (∏ᶜ fun _ : Fin (rank n) ↦ B) ⟶ T.X n)
    (split : ∀ n, i n ≫ p n = 𝟙 _) :
    τ.isoLocus (DerivedCategory.Q.obj T) := by
  let H := DerivedCategory.singleFunctor C 0
  apply CategoryTheory.bounded_complex_mem_triangulated τ.isoLocus T lo hi hb
  intro n _ _
  have hfree : τ.isoLocus (H.obj (∏ᶜ fun _ : Fin (rank n) ↦ B)) :=
    τ.isoLocus.prop_of_isLimit
      (isLimitOfPreserves H (limit.isLimit
        (Discrete.functor (fun _ : Fin (rank n) ↦ B)))) (fun _ ↦ hB)
  exact τ.isoLocus.prop_of_retract ((show Retract (T.X n)
    (∏ᶜ fun _ : Fin (rank n) ↦ B) from ⟨i n, p n, split n⟩).map H) hfree

set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Thick closure, the finite-free base case (including rank zero), and site-perfectness.
Source: Stacks 0944 and blueprint order 1275, Detailed form
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: (1) The profinite coefficient comparison gives the ordinary ringed-topos
operations. (2) The unit normalization of ringed-projection-mate-exact gives the
identity on the coefficient ring; additivity gives finite free sheaves, also rank zero.
(3) Its two functors are exact and its natural transformation respects shifts.
The triangle morphism isomorphism lemma gives two-out-of-three; naturality gives
inverse F(r) pi_P^{-1} G(i) on any retract. Thus the locus is thick triangulated.
(4) Restrict using ringed-projection-restriction. On each covering object use its
own bounded finite-projective representative. The terms are finite-free retracts;
stupid truncations give degreewise-split distinguished triangles, so finite induction
proves invertibility there. Local detection proves it globally. No uniform bound
or global thick-generation claim about all site-perfect objects is used. -/
theorem perfect_projection_formula :
    (locus d f aY aX K).IsTriangulated ∧
    (locus d f aY aX K).IsStableUnderRetracts ∧
    (∀ m : ℕ, locus d f aY aX K
      ((DerivedCategory.singleFunctor (modules d Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj
          (ring d Y))))) ∧
    (∀ P : derived d Y,
      SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) P →
        locus d f aY aX K P) := by
  classical
  let (U : Y.ProEt) : HasDerivedCategory (SheafOfModules.{u + 1}
      (((adicLisseForget Y).obj (ring d Y)).over U)) := HasDerivedCategory.standard _
  obtain ⟨sF, sG, hF, hG, τ, hτ, hs, hu⟩ :=
    proEtaleProjectionMateExact f (ring d Y) (ring d X) (coefficients d f) aY aX K
  let := sF
  let := sG
  have := hF
  have := hG
  have := hs
  have hlocus : locus d f aY aX K = τ.isoLocus := by
    funext P
    exact congrArg IsIso (hτ P).symm
  rw [hlocus]
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro m
    exact τ.isoLocus.prop_of_isLimit
      (isLimitOfPreserves (DerivedCategory.singleFunctor (modules d Y) 0)
        (limit.isLimit (Discrete.functor (fun _ : Fin m ↦
          SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))))) (fun _ ↦ hu)
  · intro P hP
    obtain ⟨T, hT, ⟨e⟩⟩ := hP
    rw [NatTrans.isoLocus]
    rw [hτ P]
    apply SheafOfModules.ringedRestrictionLocalIso
      ((adicLisseForget Y).obj (ring d Y))
    intro V
    obtain ⟨S, hS, hlocal⟩ := hT V
    refine ⟨S, hS, ?_⟩
    intro U q hq
    obtain ⟨B, ⟨lo, hi, hb⟩, ⟨pkg⟩, z, hz⟩ := hlocal U q hq
    have := hz
    let R := ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2}
      ((adicLisseForget Y).obj (ring d Y)) U
    let L := SheafOfModules.overFunctor.{u + 1}
      ((adicLisseForget Y).obj (ring d Y)) U
    have : L.Additive := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).1
    have : PreservesFiniteLimits L :=
      (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).2.1
    have : PreservesFiniteColimits L :=
      (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} _ U).2.2
    let model : R.obj P ≅ DerivedCategory.Q.obj B :=
      R.mapIso e ≪≫ L.mapDerivedCategoryFactors.app T ≪≫
        (asIso (DerivedCategory.Q.map z)).symm
    obtain ⟨loc⟩ := proEtaleProjectionMateSlicePresentation f
      (ring d Y) (ring d X) (coefficients d f) aY aX K U
    let := loc.sourceShift
    let := loc.targetShift
    have := loc.sourceExact
    have := loc.targetExact
    have := loc.shiftCompatible
    let one := (DerivedCategory.singleFunctor (modules d Y) 0).obj
      (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
    have hunit : IsIso (proEtaleProjectionFormulaMate f (ring d Y) (ring d X)
        (coefficients d f) aY aX K one) := (congrArg IsIso (hτ one)).mp hu
    have hlocalunit : IsIso (loc.mate.app (R.obj one)) := by
      have : IsIso (loc.sourceComparison.hom.app one ≫
          loc.mate.app (R.obj one)) := by
        rw [← loc.equation one]
        infer_instance
      exact IsIso.of_isIso_comp_left (loc.sourceComparison.hom.app one) _
    let unitIso : R.obj one ≅ (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U)) :=
      (L.mapDerivedCategorySingleFunctor 0).app
        (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
    have hunit' : IsIso (loc.mate.app ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U)))) :=
      (NatTrans.isIso_app_iff_of_iso loc.mate unitIso).mp hlocalunit
    have hB := strictPerfect_mem loc.source loc.target loc.mate _ hunit'
      B lo hi hb pkg.N pkg.i pkg.p pkg.splitting
    have : IsIso (loc.mate.app (R.obj P)) :=
      (NatTrans.isIso_app_iff_of_iso loc.mate model).mpr hB
    have : IsIso (R.map (projection d f aY aX K P) ≫
        loc.targetComparison.hom.app P) := by
      rw [loc.equation P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (loc.targetComparison.hom.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem moduleUnit_existsUnique
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    ∃! j : (proEtaleRingModulePullback f R S c).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≅
          SheafOfModules.unit ((adicLisseForget X).obj S),
      ∀ (U : Y.ProEtᵒᵖ) (r : R.obj.obj U),
        ((proEtaleRingModuleAdjunction f R S c).homEquiv
          _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f R S c).hom.app U r := by
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (adicLisseForget Y).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((adicLisseForget X).obj S) :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj'.homEquiv _ _ (SheafOfModules.pullbackObjUnitToUnit φ) = _
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  refine ⟨j, ?_, ?_⟩
  · intro U r
    exact congrArg (fun z ↦ z.val.app U r) hj
  · intro j' hj'
    apply Iso.ext
    apply (adj.homEquiv _ _).injective
    rw [hj]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact hj' U r

set_option linter.flexible false in
private theorem restrictedUnit_existsUnique
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aY : R ⟶ RY) (aX : S ⟶ RX)
    (c0 : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (hc : c0.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ c.hom) :
    ∃! e : (proEtaleRingModulePullback f R S c0).obj
        ((proEtaleRingRestrictScalars aY).obj
          (SheafOfModules.unit ((adicLisseForget Y).obj RY))) ≅
        (proEtaleRingRestrictScalars aX).obj
          (SheafOfModules.unit ((adicLisseForget X).obj RX)),
      ∀ (U : Y.ProEtᵒᵖ) (x : RY.obj.obj U),
        ((proEtaleRingModuleAdjunction f R S c0).homEquiv _ _ e.hom).val.app U x =
          (proEtaleRingDirectImageMap f RY RX c).hom.app U x := by
  let resY := proEtaleRingRestrictScalars aY
  let resX := proEtaleRingRestrictScalars aX
  let adj := proEtaleRingModuleAdjunction f R S c0
  let adj' := proEtaleRingModuleAdjunction f RY RX c
  let cmp := proEtaleRingRestrictionDirectImage f R RY S RX
    aY aX c0 c hc
  let t := proEtaleRingRestrictionPullbackInv f R RY S RX
    aY aX c0 c hc
  have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso
    f R RY S RX aY aX c0 c hc
  obtain ⟨j, hj, _⟩ := moduleUnit_existsUnique f RY RX c
  let M := SheafOfModules.unit ((adicLisseForget Y).obj RY)
  let e : (proEtaleRingModulePullback f R S
      c0).obj ((proEtaleRingRestrictScalars aY).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj RY))) ≅
        (proEtaleRingRestrictScalars aX).obj
          (SheafOfModules.unit ((adicLisseForget X).obj RX)) :=
    (asIso t).app M ≪≫ resX.mapIso j
  have he : adj.homEquiv _ _ e.hom =
      resY.map (adj'.homEquiv _ _ j.hom) ≫
        cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX)) := by
    change adj.homEquiv _ _ (t.app M ≫ resX.map j.hom) = _
    have hh := mate_adjunct adj' adj (TwoSquare.mk _ _ _ _ t) M _ j.hom
    have hm := congrArg (fun q ↦ q.app
      (SheafOfModules.unit ((adicLisseForget X).obj RX)))
        (restrictionPullback_mate f R RY S RX aY aX c0 c hc)
    change (mateEquiv adj' adj (TwoSquare.mk _ _ _ _ t)).app _ = cmp.hom.app _ at hm
    rw [hm] at hh
    exact hh
  have he' : ∀ (U : Y.ProEtᵒᵖ)
      (x : RY.obj.obj U),
      (adj.homEquiv _ _ e.hom).val.app U x =
        (proEtaleRingDirectImageMap f RY RX c).hom.app U x := by
    intro U x
    rw [he]
    change (cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX))).val.app U
      ((adj'.homEquiv _ _ j.hom).val.app U x) = _
    erw [(Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique f R RY S RX
        aY aX c0 c hc)).1]
    exact hj U x
  refine ⟨e, he', ?_⟩
  intro e' he''
  apply Iso.ext
  apply (adj.homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (he'' U x).trans (he' U x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
/-- The canonical module pullback comparison is fixed by the constant-section adjunct.
Source: blueprint order 1275, proof step 5
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the level comparison of profinite-coefficient inverse image commutes with the
completed-ring projection, so its adjunct is linear for the completed coefficient
action. Restrict the module adjunction to this linear map. The inverse coefficient
comparison gives its inverse. Uniqueness of adjuncts and sheaf maps gives uniqueness. -/
theorem quotientPullback_existsUnique (n : ℕ) :
    ∃! e : (proEtaleRingModulePullback f (ring d Y) (ring d X)
        (coefficients d f)).obj (CompletedConstantReduction.residue Y d.ideal n) ≅
          CompletedConstantReduction.residue X d.ideal n,
      ∀ (U : Y.ProEtᵒᵖ)
        (x : (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))).obj.obj U),
        ((proEtaleRingModuleAdjunction f (ring d Y) (ring d X)
          (coefficients d f)).homEquiv _ _ e.hom).val.app U x =
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app
          (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))) ≫
          (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison f).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).hom.app U) x := by
  let RY := adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))
  let RX := adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))
  have : IsIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) := by
    let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n
    exact (proEtale_profinite_coefficient_inverse_image Q).1 X Y f (op n)
  let c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX :=
    asIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
  let aY : ring d Y ⟶ RY := limit.π (adicLisseRingSystem Y d.ideal) (op n)
  let aX : ring d X ⟶ RX := limit.π (adicLisseRingSystem X d.ideal) (op n)
  have hc : (coefficients d f).hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ c.hom := by
    unfold coefficients
    exact limit.lift_π _ (op n)
  exact restrictedUnit_existsUnique f (ring d Y) (ring d X) RY RX aY aX
    (coefficients d f) c hc


set_option linter.flexible false in
/-- Pull back the quotient module by its uniquely normalized module comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientPullback (n : ℕ) :=
  (quotientPullback_existsUnique d f n).exists.choose

set_option linter.flexible false in
/-- The derived comparison is the exact termwise pullback comparison in degree zero.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientDerivedPullback (n : ℕ) :
    (pullback d f).obj (quotient d Y n) ≅ quotient d X n :=
  ((proEtaleRingModulePullback f (ring d Y) (ring d X)
    (coefficients d f)).mapDerivedCategorySingleFunctor 0).app
      (CompletedConstantReduction.residue Y d.ideal n) ≪≫
    (DerivedCategory.singleFunctor (modules d X) 0).mapIso (quotientPullback d f n)

set_option linter.flexible false in
/-- K_n as an A_X-object: derived tensor with the restricted quotient sheaf.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev reduction (n : ℕ) := aX.tensor.obj (K, quotient d X n)

set_option linter.flexible false in
/-- The reduction projection map uses the canonical quotient pullback identification.
Source: blueprint order 1275, displayed pi_n
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def reductionMap (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ⟶
      (directImage d f).obj (reduction d aX K n) :=
  projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))

/-- Chosen representatives for evaluating the signed-totalization inverse at a quotient.
The maps represent the fixed K and the fixed quotient, rather than new derived objects.
Source: blueprint order 1275, proof steps 5--6
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
structure Resolution (n : ℕ) where
  injective : CochainComplex (modules d X) ℤ
  isKInjective : injective.IsKInjective
  representsK : K ≅ DerivedCategory.Q.obj injective
  coefficient : CochainComplex (modules d Y) ℤ
  bounded : ∃ l r : ℤ, ∀ i : ℤ, i < l ∨ r < i → IsZero (coefficient.X i)
  package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((adicLisseForget Y).obj (ring d Y)) coefficient
  representsQuotient : DerivedCategory.Q.obj coefficient ≅ quotient d Y n

set_option linter.flexible false in
set_option cleanup.letToHave true in
/-- Every quotient admits the representatives used in the totalization comparison.
Source: blueprint order 1275, proof steps 5--6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: take a K-injective representative of K in all module sheaves. Perfectness of
the quotient over A gives a bounded finite-projective A-resolution. Termwise constant
sheafification followed by completed scalar extension gives the coefficient complex;
completed-constant-sheaf-reduction supplies its augmentation quasi-isomorphism and
finite-free retracts. Localize the augmentation to obtain representsQuotient. -/
theorem resolution_exists (n : ℕ) : Nonempty (Resolution d (X := X) (Y := Y) K n) := by
  classical
  have : IsNoetherianRing A := d.noetherian
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ := d.quotientPerfect (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have := ha
  have := hb
  have (i : ℤ) : Module.Projective A (F.X i) := (hF i).1
  have (i : ℤ) : Projective (F.X i) := inferInstance
  let Q := (CochainComplex.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))
  obtain ⟨q, hq⟩ := DerivedCategory.Q_map_surjective_of_projective F Q b eF.inv
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  have hq' : QuasiIso q :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u + 1} A) q).mp inferInstance
  have hbound : ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    intro i hi
    rcases hi with hi | hi
    · exact F.isZero_of_isStrictlyGE a i hi
    · exact F.isZero_of_isStrictlyLE b i hi
  obtain ⟨hred, hret, hbounded⟩ :=
    (CompletedConstantReduction.completed_constant_sheaf_reduction Y d.ideal).2.2.2
      n F q a b hq' (fun i ↦ ⟨(hF i).2, (hF i).1⟩) hbound
  let C := ((completedAdicChange Y
    (CompletedConstantReduction.base Y d.ideal)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex Y A).obj F)
  have : HasFiniteBiproducts (modules d Y) := HasFiniteBiproducts.of_hasFiniteProducts
  choose N i p hip using hret
  let e (j : ℤ) := biproductIso (fun _ : Fin (N j) ↦
    SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget Y).obj (ring d Y)) C :=
    { N := N
      i := fun j ↦ i j ≫ (e j).inv
      p := fun j ↦ (e j).hom ≫ p j
      splitting := fun j ↦ by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hip]
        rfl }
  let q' := CompletedConstantReduction.reductionComplex Y d.ideal n
    ((CompletedConstantReduction.constantComplex Y A).obj F)
    (CompletedConstantReduction.constantAugmentation Y d.ideal n F q)
  have : QuasiIso q' := hred
  let eq : DerivedCategory.Q.obj C ≅ quotient d Y n :=
    asIso (DerivedCategory.Q.map q')
  exact ⟨⟨I, hI, eI, C, ⟨a, b, hbounded⟩, pkg, eq⟩⟩


set_option linter.flexible false in
/-- Every positive quotient is site-perfect and its canonical projection map is invertible.
Source: Stacks 0944 and 093M; blueprint order 1275, proof step 5
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: choose a bounded finite-projective A-resolution of A/I^(n+1), using the datum's
perfectness hypothesis. Completed-constant-sheaf-reduction realizes it as a bounded
complex of finite-free retracts representing the quotient. Thus the quotient is
site-perfect. Apply perfect_projection_formula and compose with the direct image
of the canonical quotient pullback isomorphism. This is exactly the displayed map. -/
theorem reductionMap_isIso (n : ℕ) :
    SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) ∧
      IsIso (reductionMap d f aY aX K n) := by
  obtain ⟨r⟩ := resolution_exists d (X := X) (Y := Y) K n
  have hperfect : SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) := by
    refine ⟨r.coefficient, ?_, ⟨r.representsQuotient.symm⟩⟩
    intro V
    refine ⟨⊤, (ProEt.topology Y).top_mem V, ?_⟩
    intro U g _
    let L := SheafOfModules.overFunctor ((adicLisseForget Y).obj (ring d Y)) U
    have : PreservesFiniteLimits L :=
      (ringedOverFunctor_exactGeneral ((adicLisseForget Y).obj (ring d Y)) U).2.1
    let e (m : ℕ) :
        L.obj (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
          ∏ᶜ fun _ : Fin m ↦
            SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U) :=
      PreservesProduct.iso L _
    let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        (((adicLisseForget Y).obj (ring d Y)).over U)
        ((L.mapHomologicalComplex (.up ℤ)).obj r.coefficient) :=
      { N := r.package.N
        i := fun i ↦ L.map (r.package.i i) ≫ (e (r.package.N i)).hom
        p := fun i ↦ (e (r.package.N i)).inv ≫ L.map (r.package.p i)
        splitting := fun i ↦ by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp,
            r.package.splitting, L.map_id]
          rfl }
    refine ⟨(L.mapHomologicalComplex (.up ℤ)).obj r.coefficient, ?_, ⟨pkg⟩, 𝟙 _, ?_⟩
    · obtain ⟨a, b, hab⟩ := r.bounded
      exact ⟨a, b, fun i hi ↦ L.map_isZero (hab i hi)⟩
    · infer_instance
  refine ⟨hperfect, ?_⟩
  have : IsIso (projection d f aY aX K (quotient d Y n)) :=
    (perfect_projection_formula d f aY aX K).2.2.2 _ hperfect
  change IsIso (projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n))).hom)
  infer_instance

set_option linter.flexible false in
/-- The specified pi_n as an isomorphism, with the original projection map as its hom.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def reductionIso (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ≅
      (directImage d f).obj (reduction d aX K n) :=
  @asIso _ _ _ _ (reductionMap d f aY aX K n)
    (reductionMap_isIso d f aY aX K n).2

set_option linter.flexible false in
/-- rho_n is the unique inverse of the canonical, resolution-independent projection map.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev inverse (n : ℕ) := (reductionIso d f aY aX K n).inv

set_option linter.flexible false in
/-- The actual quotient homomorphism is linear for the completed coefficient action.
Source: blueprint order 1275, tower clause
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: define the map by the quotient ring map on sections. The limit cone equation
makes it linear. Ring-map naturality makes it commute with restrictions. The underlying
section functions determine a module-sheaf morphism uniquely. -/
theorem quotientModuleMap_existsUnique (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    ∃! q : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n,
      ∀ (U : T.ProEtᵒᵖ)
        (x : (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U),
        q.val.app U x =
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op).hom.app U x := by
  let q := (adicLisseRingSystem T d.ideal).map (homOfLE h).op
  let φ : (CompletedConstantReduction.residue T d.ideal m).val.presheaf ⟶
      (CompletedConstantReduction.residue T d.ideal n).val.presheaf :=
    Functor.whiskerRight q.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let qm : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n :=
    ⟨PresheafOfModules.homMk φ (by
      intro U r x
      change (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U at x
      change q.hom.app U
          ((show (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U from
            (limit.π (adicLisseRingSystem T d.ideal) (op m)).hom.app U r) * x) =
        (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
          (limit.π (adicLisseRingSystem T d.ideal) (op n)).hom.app U r) *
            (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
              q.hom.app U x)
      rw [map_mul]
      congr 1
      exact congrArg (fun z ↦ z.hom.app U r)
        (limit.w (adicLisseRingSystem T d.ideal) (homOfLE h).op))⟩
  refine ⟨qm, fun _ _ ↦ rfl, ?_⟩
  intro qm' hqm'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hqm' U x

set_option linter.flexible false in
/-- The quotient tower map retains its uniquely specified sectionwise quotient formula.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientModuleMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :=
  (quotientModuleMap_existsUnique d T n m h).exists.choose

set_option linter.flexible false in
/-- The positive quotient tower map in the ordinary completed-coefficient derived category.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    quotient d T m ⟶ quotient d T n :=
  (DerivedCategory.singleFunctor (modules d T) 0).map (quotientModuleMap d T n m h)

set_option linter.flexible false in
private theorem derived_single_square
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {M N : C} {M' N' : D} (u : M ⟶ N) (v : M' ⟶ N')
    (a : L.obj M ⟶ M') (b : L.obj N ⟶ N') (h : L.map u ≫ b = a ≫ v) :
    L.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map u) ≫
        (L.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor D 0).map b =
      ((L.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor D 0).map a) ≫
          (DerivedCategory.singleFunctor D 0).map v := by
  have hn := (L.mapDerivedCategorySingleFunctor 0).hom.naturality u
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp, h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
/-- Quotient pullback comparisons commute with every quotient tower map.
Source: blueprint order 1275, proof steps 5 and 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the two adjuncts are the same map on each constant quotient section, by
profinite-coefficient inverse-image naturality. The unique module comparisons and
exact termwise pullback preserve this equality in the derived category. -/
theorem quotientDerivedPullback_naturality (n m : ℕ) (h : n ≤ m) :
    (pullback d f).map (quotientMap d Y n m h) ≫ (quotientDerivedPullback d f n).hom =
      (quotientDerivedPullback d f m).hom ≫ quotientMap d X n m h := by
  let L := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)
  let adj := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let adjR := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  have hr := congrArg (adjR.homEquiv _ _) (c.naturality (homOfLE h).op)
  simp only [Functor.comp_map, adjR.homEquiv_naturality_left,
    adjR.homEquiv_naturality_right] at hr
  have hm : L.map (quotientModuleMap d Y n m h) ≫ (quotientPullback d f n).hom =
      (quotientPullback d f m).hom ≫ quotientModuleMap d X n m h := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (adj.homEquiv _ _ (quotientPullback d f n).hom).val.app U
        ((quotientModuleMap d Y n m h).val.app U x) =
      (quotientModuleMap d X n m h).val.app ((proEtaleBaseChange f).op.obj U)
        ((adj.homEquiv _ _ (quotientPullback d f m).hom).val.app U x)
    dsimp only [quotientModuleMap, quotientPullback, adj]
    rw [(quotientModuleMap_existsUnique d Y n m h).exists.choose_spec,
      (quotientPullback_existsUnique d f n).exists.choose_spec,
      (quotientPullback_existsUnique d f m).exists.choose_spec,
      (quotientModuleMap_existsUnique d X n m h).exists.choose_spec]
    exact congrArg (fun z ↦ z.hom.app U x) hr
  have hn := (L.mapDerivedCategorySingleFunctor 0).hom.naturality
    (quotientModuleMap d Y n m h)
  change (pullback d f).map (quotientMap d Y n m h) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f n).hom =
    ((L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f m).hom) ≫ _
  dsimp only [Functor.comp_map] at hn
  dsimp only [pullback, proEtaleRingDerivedPullback, quotientMap]
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp, hm]


set_option linter.flexible false in
private theorem inverse_square {C : Type*} [Category C]
    {S S' T T' : C} (p : S ⟶ T) (p' : S' ⟶ T')
    [IsIso p] [IsIso p'] (a : S ⟶ S') (b : T ⟶ T')
    (h : p ≫ b = a ≫ p') : inv p ≫ a = b ≫ inv p' := by
  apply (cancel_mono p').1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

set_option linter.flexible false in
private theorem projection_naturality {P Q : derived d Y} (q : P ⟶ Q) :
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) q) ≫
        projection d f aY aX K Q =
      projection d f aY aX K P ≫
        (directImage d f).map
          (aX.tensor.map (Prod.mkHom (𝟙 K) ((pullback d f).map q))) := by
  exact (((proEtaleRingDerivedAdjunction f (ring d Y) (ring d X)
    (coefficients d f)).rightAdjointProjectionMap
    (T_C := Functor.curry.obj aX.tensor) (T_D := Functor.curry.obj aY.tensor)
    (Functor.curry.map (proEtaleCanonicalTensorComparison f (ring d Y) (ring d X)
      (coefficients d f) aY aX).hom ≫
        (Functor.curryObjProdComp (pullback d f) (pullback d f) aX.tensor).hom)).app K).naturality q

set_option linter.flexible false in
/-- Both the forward maps and their unique inverses commute with the whole quotient tower.
Source: blueprint order 1275, proof step 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: naturality of the canonical projection mate in its coefficient variable gives
the first equation, after quotientDerivedPullback_naturality identifies the target
maps. Multiply this square by the two inverse maps to get the second equation.
The argument applies to every n≤m, including equality, rather than only adjacent levels. -/
theorem tower_compatibility (n m : ℕ) (h : n ≤ m) :
    reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n ∧
    inverse d f aY aX K m ≫
      aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) =
    (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) ≫
      inverse d f aY aX K n := by
  have hnat := projection_naturality d f aY aX K (quotientMap d Y n m h)
  have hs := congrArg (fun z ↦ z ≫ (directImage d f).map
    (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))) hnat
  simp only [Category.assoc, ← Functor.map_comp, prod_comp,
    Category.comp_id] at hs
  rw [quotientDerivedPullback_naturality d f n m h] at hs
  have hf : reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n := by
    simpa only [reductionMap, Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id] using hs.symm
  refine ⟨hf, ?_⟩
  have := (reductionMap_isIso d f aY aX K m).2
  have := (reductionMap_isIso d f aY aX K n).2
  exact inverse_square _ _ _ _ hf

set_option linter.flexible false in
/-- The maps and inverses commute with coefficient-linear operators, also between objects.
Source: blueprint order 1275, proof step 6 and order 1274, paragraph 1
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the counit mate is natural in K. Tensor this naturality with the fixed quotient
and use functoriality of direct image. Its quotient pullback identification is fixed,
so it does not change the square. Multiply by the two inverses for the reverse square.
Taking K'=K gives endomorphisms; families of these squares give compatible operators
on the reduction tower by tower_compatibility. -/
theorem operator_compatibility (K' : derived d X) (q : K ⟶ K') (n : ℕ) :
    reductionMap d f aY aX K n ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) =
    aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) ≫
      reductionMap d f aY aX K' n ∧
    inverse d f aY aX K n ≫
      aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) =
    (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) ≫
      inverse d f aY aX K' n := by
  have h : reductionMap d f aY aX K n ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) =
    aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) ≫
      reductionMap d f aY aX K' n := by
    have hnat := derivedProjectionFormulaMate_naturality (pullback d f) (directImage d f)
      (proEtaleRingDerivedAdjunction f (ring d Y) (ring d X) (coefficients d f))
      aY.tensor aX.tensor
      (proEtaleCanonicalTensorComparison f (ring d Y) (ring d X) (coefficients d f) aY aX)
      K K' (quotient d Y n) q
    change projection d f aY aX K (quotient d Y n) ≫ _ =
      _ ≫ projection d f aY aX K' (quotient d Y n) at hnat
    simpa only [reductionMap, Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id] using
      congrArg (fun z ↦ z ≫ (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K') (quotientDerivedPullback d f n).hom))) hnat
  refine ⟨h, ?_⟩
  have := (reductionMap_isIso d f aY aX K n).2
  have := (reductionMap_isIso d f aY aX K' n).2
  exact inverse_square _ _ _ _ h

-- The finite-total argument uses the existing native normalized unit comparison.
-- Its canonical coherence theorem is proEtaleProjectionUnit_existsUnique.

variable {n : ℕ} (r : Resolution d (X := X) (Y := Y) K n)

attribute [local irreducible] proEtaleOrdinaryTensorPullback

set_option linter.flexible false in
/-- The signed total chain mate, with differential d_I tensor 1 + (-1)^a 1 tensor d_F.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.total :=
  SignedProjectionResolution.totalMate f (ring d Y) (ring d X) (coefficients d f)
    r.injective r.coefficient

/-- The specified finite-total inverse, using the degreewise finite-free retract package.
The existing tensorAdjunctionTotalInverse_summand gives the required summand formula
(1 tensor p_r) q_(I^a,N_r) push(1 tensor pull(i_r)); its total is finite in each degree.
Source: blueprint order 1275 and definition 1264
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.totalInverse :=
  SignedProjectionResolution.totalInverse f (ring d Y) (ring d X) (coefficients d f)
    r.injective r.coefficient r.package r.bounded

set_option linter.flexible false in
/-- The normalized source comparison, specified by the mixed representative squares.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.sourceModel :=
  SignedProjectionResolution.sourceModel f (ring d Y) (ring d X) (coefficients d f)
    aY K (quotient d Y n) r.injective r.isKInjective r.representsK
    r.coefficient r.representsQuotient r.package r.bounded

set_option linter.flexible false in
/-- The normalized target comparison, using exact pullback, mixed tensor and the
K-injective right-derived unit. Source: blueprint order 1275
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.targetModel :=
  ((directImage d f).mapIso
    (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n)))).symm ≪≫
      SignedProjectionResolution.targetModel f (ring d Y) (ring d X) (coefficients d f)
        aX K (quotient d Y n) r.injective r.isKInjective r.representsK
        r.coefficient r.representsQuotient r.package r.bounded

set_option linter.flexible false in
private theorem normalization_with_coefficient_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (K : DerivedCategory (proEtaleRingModules X S))
    (P : DerivedCategory (proEtaleRingModules Y R))
    (P' : DerivedCategory (proEtaleRingModules X S))
    (q : (proEtaleRingDerivedPullback f R S c).obj P ≅ P')
    (I : CochainComplex (proEtaleRingModules X S) ℤ) (hI : I.IsKInjective)
    (alpha : K ≅ DerivedCategory.Q.obj I)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (beta : DerivedCategory.Q.obj F ≅ P)
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
    (bounded : ∃ l h : ℤ, ∀ i : ℤ, i < l ∨ h < i → IsZero (F.X i)) :
    let V := proEtaleRingDerivedDirectImage f R S c
    let e := V.mapIso (b.tensor.mapIso (Iso.prod (Iso.refl K) q))
    let src := SignedProjectionResolution.sourceModel f R S c a K P I hI alpha F beta
      pkg bounded
    let tgt := e.symm ≪≫ SignedProjectionResolution.targetModel f R S c b K P I hI alpha
      F beta pkg bounded
    let pi := proEtaleProjectionFormulaMate f R S c a b K P ≫ e.hom
    pi = src.hom ≫ DerivedCategory.Q.map
        (SignedProjectionResolution.totalMate f R S c I F) ≫ tgt.inv ∧
      pi ≫ (tgt.hom ≫ DerivedCategory.Q.map
        (SignedProjectionResolution.totalInverse f R S c I F pkg bounded) ≫ src.inv) =
          𝟙 _ := by
  dsimp only
  have h := SignedProjectionResolution.normalization f R S c a b K P I hI alpha F beta
    pkg bounded
  refine ⟨?_, ?_⟩
  · rw [show proEtaleProjectionFormulaMate f R S c a b K P = _ from h.1]
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact h.2.1

section TotalizationProof

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingDerivedPullbackFactors

-- Avoid repeated inspection of the large representative tactic contexts.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Agreement with signed totalization, for every chosen resolution, fixes both arrows
and proves resolution independence of the inverse.
Source: blueprint order 1275, first proof and proof step 6; Stacks 0944
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: use exact termwise pullback and the canonical tensor comparison on flat K-flat
representatives to compute the counit mate on the chosen models. The resulting forward
map is the localization of the ordinary signed total mate. Its finite-total inverse
has the prescribed degreewise retract formula and commutes with both differentials,
including the sign (-1)^a. Localizing gives the displayed reverse map. Totalization
proves both composite identities, so uniqueness of inverse identifies it with rho_n.
The statement quantifies over every model; thus changing either resolution or any
splitting package gives the same derived forward map and the same inverse. -/
theorem totalization_compatibility :
    reductionMap d f aY aX K n =
      (r.sourceModel d f aY K).hom ≫ DerivedCategory.Q.map (r.total d f K) ≫
        (r.targetModel d f aX K).inv ∧
    inverse d f aY aX K n =
      (r.targetModel d f aX K).hom ≫ DerivedCategory.Q.map (r.totalInverse d f K) ≫
        (r.sourceModel d f aY K).inv := by
  have h := normalization_with_coefficient_iso f (ring d Y) (ring d X) (coefficients d f)
    aY aX K (quotient d Y n) (quotient d X n) (quotientDerivedPullback d f n)
    r.injective r.isKInjective r.representsK r.coefficient r.representsQuotient
    r.package r.bounded
  refine ⟨h.1, ?_⟩
  have hi : IsIso (reductionMap d f aY aX K n) :=
    (reductionMap_isIso d f aY aX K n).2
  apply (cancel_epi (reductionMap d f aY aX K n)).mp
  change reductionMap d f aY aX K n ≫ inv (reductionMap d f aY aX K n) = _
  rw [IsIso.hom_inv_id]
  exact h.2.symm

end TotalizationProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem coefficientMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    coefficientMap d (f ≫ g) =
      (proEtaleRingInverseImageComp f g).hom.app (ring d Z) ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap d g) ≫
          coefficientMap d f := by
  apply limit.hom_ext
  intro n
  have hπ (V W : Scheme.{u}) (k : V ⟶ W) :
      coefficientMap d k ≫ limit.π (adicLisseRingSystem V d.ideal) n =
        (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem W d.ideal) n) ≫
            (proEtaleConstantComparison k).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1))) :=
    limit.lift_π _ n
  have : Finite (A ⧸ d.ideal ^ (n.unop + 1)) := d.quotientFinite n.unop
  let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
  have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n.unop
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ :=
    proEtale_profinite_coefficient_inverse_image Q
  have hc' := hc X Y Z f g n
  dsimp only [Q, proEtaleCoefficientTower, Functor.comp_obj,
    Functor.const_obj_obj] at hc'
  rw [hπ, hc']
  rw [← Category.assoc, ← Category.assoc]
  have hn := (proEtaleRingInverseImageComp f g).hom.naturality
    (limit.π (adicLisseRingSystem Z d.ideal) n)
  erw [hn]
  simp only [Functor.comp_map, Category.assoc]
  rw [hπ X Y f]
  conv_rhs => rw [← Functor.map_comp_assoc, hπ Y Z g, Functor.map_comp]
  simp only [Category.assoc]
  rfl

set_option linter.flexible false in
private theorem coefficients_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    proEtaleRingCompositeCoefficients f g (ring d Z) (ring d Y) (ring d X)
      (coefficients d g) (coefficients d f) = coefficients d (f ≫ g) := by
  apply Iso.ext
  unfold coefficients
  dsimp only [proEtaleRingCompositeCoefficients, asIso_hom]
  exact (coefficientMap_comp d f g).symm


-- The explicit intermediate objects preserve the native projection-square statement.
-- Keeping its functor compositions visible avoids evaluating derived functor objects.
set_option cleanup.letToHave true in
set_option linter.flexible false in
private theorem reduction_square_algebra
    {C D C' D' : Type*} [cC : Category C] [cD : Category D] [cC' : Category C'] [cD' : Category D']
    (L : D ⥤ C) (R : C ⥤ D) (L' : D' ⥤ C') (R' : C' ⥤ D')
    (G : D ⥤ D') (H : C ⥤ C')
    (T : D × D ⥤ D) (U : C × C ⥤ C)
    (T' : D' × D' ⥤ D') (U' : C' × C' ⥤ C')
    (ξ : R ⋙ G ⟶ H ⋙ R')
    (μ : T ⋙ G ⟶ (G.prod G) ⋙ T')
    (ν : U ⋙ H ⟶ (H.prod H) ⋙ U')
    (K : C) (Q : D) (QX : C) (QY' : D') (QX' : C')
    (qf : L.obj Q ⟶ QX) (qg : G.obj Q ⟶ QY')
    (qf' : L'.obj QY' ⟶ QX') (qg' : H.obj QX ⟶ QX')
    (θ : H.obj (L.obj Q) ⟶ L'.obj (G.obj Q))
    (p : T.obj (R.obj K, Q) ⟶ R.obj (U.obj (K, L.obj Q)))
    (p₀ : T'.obj (R'.obj (H.obj K), QY') ⟶
      R'.obj (U'.obj (H.obj K, L'.obj QY')))
    (p₁ : T'.obj (R'.obj (H.obj K), G.obj Q) ⟶
      R'.obj (U'.obj (H.obj K, L'.obj (G.obj Q))))
    (hq : θ ≫ L'.map qg ≫ qf' = H.map qf ≫ qg')
    (hp : T'.map (Prod.mkHom (𝟙 (R'.obj (H.obj K))) qg) ≫ p₀ =
      p₁ ≫ R'.map (U'.map (Prod.mkHom (𝟙 (H.obj K)) (L'.map qg))))
    (hb : @Eq
        (@Quiver.Hom D' (@CategoryStruct.toQuiver D' (@Category.toCategoryStruct D' cD'))
          (@Functor.obj D cD D' cD' G
            (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C
              cC D cD R K) Q)))
          (@Functor.obj C' cC' D' cD' R'
            (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
              (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q)))))
        (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
          (@Functor.obj D cD D' cD' G
            (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C
              cC D cD R K) Q)))
          (@Functor.obj D cD D' cD' G
            (@Functor.obj C cC D cD R
              (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj
                D cD C cC L Q)))))
          (@Functor.obj C' cC' D' cD' R'
            (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
              (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q))))
          (@CategoryTheory.Functor.map D cD D' cD' G
            (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C
              cC D cD R K) Q))
            (@Functor.obj C cC D cD R
              (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj
                D cD C cC L Q))))
            p)
          (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
            (@Functor.obj D cD D' cD' G
              (@Functor.obj C cC D cD R
                (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K
                  (@Functor.obj D cD C cC L Q)))))
            (@Functor.obj C cC D' cD' (@Functor.comp C cC C' cC' D' cD' H R')
              (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj
                D cD C cC L Q))))
            (@Functor.obj C' cC' D' cD' R'
              (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
                (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                  (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q))))
            (@NatTrans.app C cC D' cD' (@Functor.comp C cC D cD D' cD' R G) (@Functor.comp C cC C'
              cC' D' cD' H R') ξ
              (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj
                D cD C cC L Q))))
            (@CategoryTheory.Functor.map C' cC' D' cD' R'
              (@Functor.obj C cC C' cC' H
                (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K
                  (@Functor.obj D cD C cC L Q))))
              (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
                (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                  (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q)))
              (@CategoryStruct.comp C' (@Category.toCategoryStruct C' cC')
                (@Functor.obj C cC C' cC' H
                  (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K
                    (@Functor.obj D cD C cC L Q))))
                (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C' cC'
                  (@Functor.comp (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C'
                    cC') C' cC'
                    (@Functor.prod C cC C' cC' C cC C' cC' H H) U')
                  (@Prod.mk C C K (@Functor.obj D cD C cC L Q)))
                (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
                  (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                    (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q)))
                (@NatTrans.app (Prod C C) (@uniformProd C cC C cC) C' cC'
                  (@Functor.comp (Prod C C) (@uniformProd C cC C cC) C cC C' cC' U H)
                  (@Functor.comp (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C'
                    cC') C' cC'
                    (@Functor.prod C cC C' cC' C cC C' cC' H H) U')
                  ν (@Prod.mk C C K (@Functor.obj D cD C cC L Q)))
                (@CategoryTheory.Functor.map (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
                  (@Functor.obj (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C'
                    cC')
                    (@Functor.prod C cC C' cC' C cC C' cC' H H) (@Prod.mk C C K (@Functor.obj D cD C
                      cC L Q)))
                  (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                    (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q))
                  (@Prod.mkHom C' (@Category.toCategoryStruct C' cC') C' (@Category.toCategoryStruct
                    C' cC')
                    (@Functor.obj C cC C' cC' H (@Prod.fst C C (@Prod.mk C C K (@Functor.obj D cD C
                      cC L Q))))
                    (@Functor.obj C cC C' cC' H K)
                    (@Functor.obj C cC C' cC' H (@Prod.snd C C (@Prod.mk C C K (@Functor.obj D cD C
                      cC L Q))))
                    (@Functor.obj D cD C' cC' (@Functor.comp D cD D' cD' C' cC' G L') Q)
                    (@CategoryStruct.id C' (@Category.toCategoryStruct C' cC') (@Functor.obj C cC C'
                      cC' H K)) θ))))))
        (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
          (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D' cD'
            (@Functor.comp (Prod D D) (@uniformProd D cD D cD) D cD D' cD' T G) (@Prod.mk D D
              (@Functor.obj C cC D cD R K) Q))
          (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D' cD'
            (@Functor.comp (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD')
              D' cD'
              (@Functor.prod D cD D' cD' D cD D' cD' G G) T')
            (@Prod.mk D D (@Functor.obj C cC D cD R K) Q))
          (@Functor.obj C' cC' D' cD' R'
            (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
              (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) (@Functor.obj D' cD' C' cC' L'
                (@Functor.obj D cD D' cD' G Q)))))
          (@NatTrans.app (Prod D D) (@uniformProd D cD D cD) D' cD'
            (@Functor.comp (Prod D D) (@uniformProd D cD D cD) D cD D' cD' T G)
            (@Functor.comp (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD')
              D' cD'
              (@Functor.prod D cD D' cD' D cD D' cD' G G) T')
            μ (@Prod.mk D D (@Functor.obj C cC D cD R K) Q))
          (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
            (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D' cD'
              (@Functor.comp (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD')
                D' cD'
                (@Functor.prod D cD D' cD' D cD D' cD' G G) T')
              (@Prod.mk D D (@Functor.obj C cC D cD R K) Q))
            (@Functor.obj (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
              (@Prod.mk D' D' (@Functor.obj C cC D' cD' (@Functor.comp C cC C' cC' D' cD' H R') K)
                (@Functor.obj D cD D' cD' G Q)))
            (@Functor.obj C' cC' D' cD' R'
              (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
                (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K)
                  (@Functor.obj D' cD' C' cC' L' (@Functor.obj D cD D' cD' G Q)))))
            (@CategoryTheory.Functor.map (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
              (@Functor.obj (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD')
                (@Functor.prod D cD D' cD' D cD D' cD' G G) (@Prod.mk D D (@Functor.obj C cC D cD R
                  K) Q))
              (@Prod.mk D' D' (@Functor.obj C cC D' cD' (@Functor.comp C cC C' cC' D' cD' H R') K)
                (@Functor.obj D cD D' cD' G Q))
              (@Prod.mkHom D' (@Category.toCategoryStruct D' cD') D' (@Category.toCategoryStruct D'
                cD')
                (@Functor.obj D cD D' cD' G (@Prod.fst D D (@Prod.mk D D (@Functor.obj C cC D cD R
                  K) Q)))
                (@Functor.obj C cC D' cD' (@Functor.comp C cC C' cC' D' cD' H R') K)
                (@Functor.obj D cD D' cD' G (@Prod.snd D D (@Prod.mk D D (@Functor.obj C cC D cD R
                  K) Q)))
                (@Functor.obj D cD D' cD' G Q)
                (@NatTrans.app C cC D' cD' (@Functor.comp C cC D cD D' cD' R G) (@Functor.comp C cC
                  C' cC' D' cD' H R') ξ K)
                (@CategoryStruct.id D' (@Category.toCategoryStruct D' cD') (@Functor.obj D cD D' cD'
                  G Q))))
            p₁))) :
    @Eq (@Quiver.Hom D' (@CategoryStruct.toQuiver D' (@Category.toCategoryStruct D' cD'))
      (@Functor.obj D cD D' cD' G
        (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC D
          cD R K) Q)))
      (@Functor.obj C' cC' D' cD' R'
        (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
          (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')))) (@CategoryStruct.comp D'
            (@Category.toCategoryStruct D' cD')
      (@Functor.obj D cD D' cD' G
        (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC D
          cD R K) Q)))
      (@Functor.obj D cD D' cD' G
        (@Functor.obj C cC D cD R (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk
          C C K QX))))
      (@Functor.obj C' cC' D' cD' R'
        (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
          (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')))
      (@CategoryTheory.Functor.map D cD D' cD' G
        (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC D
          cD R K) Q))
        (@Functor.obj C cC D cD R (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk
          C C K QX)))
        (@CategoryStruct.comp D (@Category.toCategoryStruct D cD)
          (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC
            D cD R K) Q))
          (@Functor.obj C cC D cD R
            (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj D
              cD C cC L Q))))
          (@Functor.obj C cC D cD R (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U
            (@Prod.mk C C K QX))) p
          (@CategoryTheory.Functor.map C cC D cD R
            (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K (@Functor.obj D
              cD C cC L Q)))
            (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K QX))
            (@CategoryTheory.Functor.map (Prod C C) (@uniformProd C cC C cC) C cC U
              (@Prod.mk C C K (@Functor.obj D cD C cC L Q)) (@Prod.mk C C K QX)
              (@Prod.mkHom C (@Category.toCategoryStruct C cC) C (@Category.toCategoryStruct C cC) K
                K
                (@Functor.obj D cD C cC L Q) QX (@CategoryStruct.id C (@Category.toCategoryStruct C
                  cC) K) qf)))))
      (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
        (@Functor.obj D cD D' cD' G
          (@Functor.obj C cC D cD R (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U
            (@Prod.mk C C K QX))))
        (@Functor.obj C cC D' cD' (@Functor.comp C cC C' cC' D' cD' H R')
          (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K QX)))
        (@Functor.obj C' cC' D' cD' R'
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')))
        (@NatTrans.app C cC D' cD' (@Functor.comp C cC D cD D' cD' R G) (@Functor.comp C cC C' cC'
          D' cD' H R') ξ
          (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U (@Prod.mk C C K QX)))
        (@CategoryTheory.Functor.map C' cC' D' cD' R'
          (@Functor.obj C cC C' cC' H (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U
            (@Prod.mk C C K QX)))
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX'))
          (@CategoryStruct.comp C' (@Category.toCategoryStruct C' cC')
            (@Functor.obj C cC C' cC' H (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C cC U
              (@Prod.mk C C K QX)))
            (@Functor.obj (Prod C C) (@uniformProd C cC C cC) C' cC'
              (@Functor.comp (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C' cC')
                C' cC'
                (@Functor.prod C cC C' cC' C cC C' cC' H H) U')
              (@Prod.mk C C K QX))
            (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
              (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX'))
            (@NatTrans.app (Prod C C) (@uniformProd C cC C cC) C' cC'
              (@Functor.comp (Prod C C) (@uniformProd C cC C cC) C cC C' cC' U H)
              (@Functor.comp (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C' cC')
                C' cC'
                (@Functor.prod C cC C' cC' C cC C' cC' H H) U')
              ν (@Prod.mk C C K QX))
            (@CategoryTheory.Functor.map (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
              (@Functor.obj (Prod C C) (@uniformProd C cC C cC) (Prod C' C') (@prod' C' cC' C' cC')
                (@Functor.prod C cC C' cC' C cC C' cC' H H) (@Prod.mk C C K QX))
              (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')
              (@Prod.mkHom C' (@Category.toCategoryStruct C' cC') C' (@Category.toCategoryStruct C'
                cC')
                (@Functor.obj C cC C' cC' H (@Prod.fst C C (@Prod.mk C C K QX))) (@Functor.obj C cC
                  C' cC' H K)
                (@Functor.obj C cC C' cC' H (@Prod.snd C C (@Prod.mk C C K QX))) QX'
                (@CategoryStruct.id C' (@Category.toCategoryStruct C' cC') (@Functor.obj C cC C' cC'
                  H K)) qg')))))) (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
      (@Functor.obj D cD D' cD' G
        (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC D
          cD R K) Q)))
      (@Functor.obj (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
        (@Prod.mk D' D' (@Functor.obj C' cC' D' cD' R' (@Functor.obj C cC C' cC' H K)) QY'))
      (@Functor.obj C' cC' D' cD' R'
        (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
          (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')))
      (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
        (@Functor.obj D cD D' cD' G
          (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D cD T (@Prod.mk D D (@Functor.obj C cC
            D cD R K) Q)))
        (@Functor.obj (Prod D D) (@uniformProd D cD D cD) D' cD'
          (@Functor.comp (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD') D'
            cD'
            (@Functor.prod D cD D' cD' D cD D' cD' G G) T')
          (@Prod.mk D D (@Functor.obj C cC D cD R K) Q))
        (@Functor.obj (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
          (@Prod.mk D' D' (@Functor.obj C' cC' D' cD' R' (@Functor.obj C cC C' cC' H K)) QY'))
        (@NatTrans.app (Prod D D) (@uniformProd D cD D cD) D' cD'
          (@Functor.comp (Prod D D) (@uniformProd D cD D cD) D cD D' cD' T G)
          (@Functor.comp (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD') D'
            cD'
            (@Functor.prod D cD D' cD' D cD D' cD' G G) T')
          μ (@Prod.mk D D (@Functor.obj C cC D cD R K) Q))
        (@CategoryTheory.Functor.map (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
          (@Functor.obj (Prod D D) (@uniformProd D cD D cD) (Prod D' D') (@prod' D' cD' D' cD')
            (@Functor.prod D cD D' cD' D cD D' cD' G G) (@Prod.mk D D (@Functor.obj C cC D cD R K)
              Q))
          (@Prod.mk D' D' (@Functor.obj C' cC' D' cD' R' (@Functor.obj C cC C' cC' H K)) QY')
          (@Prod.mkHom D' (@Category.toCategoryStruct D' cD') D' (@Category.toCategoryStruct D' cD')
            (@Functor.obj D cD D' cD' G (@Prod.fst D D (@Prod.mk D D (@Functor.obj C cC D cD R K)
              Q)))
            (@Functor.obj C' cC' D' cD' R' (@Functor.obj C cC C' cC' H K))
            (@Functor.obj D cD D' cD' G (@Prod.snd D D (@Prod.mk D D (@Functor.obj C cC D cD R K)
              Q))) QY'
            (@NatTrans.app C cC D' cD' (@Functor.comp C cC D cD D' cD' R G) (@Functor.comp C cC C'
              cC' D' cD' H R') ξ K)
            qg)))
      (@CategoryStruct.comp D' (@Category.toCategoryStruct D' cD')
        (@Functor.obj (Prod D' D') (@uniformProd D' cD' D' cD') D' cD' T'
          (@Prod.mk D' D' (@Functor.obj C' cC' D' cD' R' (@Functor.obj C cC C' cC' H K)) QY'))
        (@Functor.obj C' cC' D' cD' R'
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) (@Functor.obj D' cD' C' cC' L' QY'))))
        (@Functor.obj C' cC' D' cD' R'
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')))
        p₀
        (@CategoryTheory.Functor.map C' cC' D' cD' R'
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) (@Functor.obj D' cD' C' cC' L' QY')))
          (@Functor.obj (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX'))
          (@CategoryTheory.Functor.map (Prod C' C') (@uniformProd C' cC' C' cC') C' cC' U'
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) (@Functor.obj D' cD' C' cC' L' QY'))
            (@Prod.mk C' C' (@Functor.obj C cC C' cC' H K) QX')
            (@Prod.mkHom C' (@Category.toCategoryStruct C' cC') C' (@Category.toCategoryStruct C'
              cC')
              (@Functor.obj C cC C' cC' H K) (@Functor.obj C cC C' cC' H K) (@Functor.obj D' cD' C'
                cC' L' QY') QX'
              (@CategoryStruct.id C' (@Category.toCategoryStruct C' cC') (@Functor.obj C cC C' cC' H
                K)) qf'))))) := by
  have hy : T'.map (Prod.mkHom (ξ.app K) qg) =
      T'.map (Prod.mkHom (ξ.app K) (𝟙 (G.obj Q))) ≫
        T'.map (Prod.mkHom (𝟙 (R'.obj (H.obj K))) qg) := by
    rw [← T'.map_comp]
    apply congrArg T'.map
    exact Prod.hom_ext (Category.comp_id (ξ.app K)).symm
      (Category.id_comp qg).symm
  rw [hy]
  let z := R'.map (U'.map (Prod.mkHom (𝟙 (H.obj K)) (L'.map qg ≫ qf')))
  have hz := congrArg (fun q ↦ q ≫ z) hb
  dsimp only [z] at hz
  simp only [Category.assoc, ← Functor.map_comp, prod_comp, Category.id_comp] at hz
  rw [hq] at hz
  have hn := ξ.naturality (U.map (Prod.mkHom (𝟙 K) qf))
  dsimp only [Functor.comp_map] at hn
  have ht := ν.naturality (Prod.mkHom (𝟙 K) qf)
  simp only [Functor.comp_map, Functor.prod_map, H.map_id] at ht
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  rw [reassoc_of% ht]
  rw [reassoc_of% hp]
  simpa only [← Functor.map_comp, prod_comp, Category.id_comp, Category.assoc] using hz


section QuotientComposition

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors

set_option linter.flexible false in
private theorem homEquiv_compositor
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {RF : D ⥤ C} {RG : E ⥤ D} {RH : E ⥤ C}
    (a : F ⊣ RF) (b : G ⊣ RG) (c : H ⊣ RH)
    (e : H ≅ F ⋙ G) (z : RG ⋙ RF ≅ RH)
    (he : conjugateIsoEquiv (a.comp b) c e = z)
    {M : C} {N : E} (q : G.obj (F.obj M) ⟶ N) :
    c.homEquiv _ _ (e.hom.app M ≫ q) =
      (a.comp b).homEquiv _ _ q ≫ z.hom.app N := by
  have h := unit_conjugateEquiv (a.comp b) c e.hom M
  have hz : conjugateEquiv (a.comp b) c e.hom = z.hom :=
    congrArg Iso.hom he
  rw [hz] at h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← h, Category.assoc, ← z.hom.naturality]
  simp only [Category.assoc, Functor.comp_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem quotientPullback_compositor {Z : Scheme.{u}} (g : Y ⟶ Z) (n : ℕ)
    (D : proEtaleRingModuleDirectImage f (ring d Y) (ring d X) (coefficients d f) ⋙
      proEtaleRingModuleDirectImage g (ring d Z) (ring d Y) (coefficients d g) ≅
        proEtaleRingModuleDirectImage (f ≫ g) (ring d Z) (ring d X)
          (coefficients d (f ≫ g)))
    (hD : ∀ (N : modules d X) (U : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage f (ring d Y) (ring d X) (coefficients d f) ⋙
        proEtaleRingModuleDirectImage g (ring d Z) (ring d Y)
          (coefficients d g)).obj N).val.obj (op U)),
      (D.hom.app N).val.app (op U) m = N.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U).op m) :
    (Adjunction.leftAdjointCompIso
      (proEtaleRingModuleAdjunction g (ring d Z) (ring d Y) (coefficients d g))
      (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
      (proEtaleRingModuleAdjunction (f ≫ g) (ring d Z) (ring d X)
        (coefficients d (f ≫ g))) D).inv.app
          (CompletedConstantReduction.residue Z d.ideal n) ≫
      (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
        (quotientPullback d g n).hom ≫ (quotientPullback d f n).hom =
      (quotientPullback d (f ≫ g) n).hom := by
  let Q := CommRingCat.of (A ⧸ d.ideal ^ (n + 1))
  let rho (V W : Scheme.{u}) (k : V ⟶ W) :=
    proEtaleConstantDirectImageMap k CommRingCat.{u + 1} Q
  have hq (V W : Scheme.{u}) (k : V ⟶ W) (U : W.ProEtᵒᵖ)
      (x : (adicLisseConstantRing W (A ⧸ d.ideal ^ (n + 1))).obj.obj U) :
      ((proEtaleRingModuleAdjunction k (ring d W) (ring d V)
        (coefficients d k)).homEquiv _ _ (quotientPullback d k n).hom).val.app U x =
        (rho V W k).hom.app U x := by
    have he := (Classical.choose_spec (quotientPullback_existsUnique d k n).exists) U x
    have hr : (proEtaleSheafAdjunction k CommRingCat.{u + 1}).unit.app
        (adicLisseConstantRing W (A ⧸ d.ideal ^ (n + 1))) ≫
        (proEtaleSheafDirectImage k CommRingCat.{u + 1}).map
          ((proEtaleConstantComparison k).app
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) = rho V W k := by
      change ((proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _)
        (((proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _).symm
          (rho V W k)) = _
      exact ((proEtaleSheafAdjunction k CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
    exact he.trans (congrArg (fun t ↦ t.hom.app U x) hr)
  let ak := proEtaleRingModuleAdjunction g (ring d Z) (ring d Y) (coefficients d g)
  let ah := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let ac := proEtaleRingModuleAdjunction (f ≫ g) (ring d Z) (ring d X)
    (coefficients d (f ≫ g))
  let e := (Adjunction.leftAdjointCompIso ak ah ac D).symm
  have he : conjugateIsoEquiv (ak.comp ah) ac e = D := by
    apply Iso.ext
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv ak ah ac D
  apply (ac.homEquiv _ _).injective
  change ac.homEquiv _ _ (e.hom.app _ ≫ _) = _
  rw [homEquiv_compositor (C := modules d Z) (D := modules d Y)
    (E := modules d X) ak ah ac e D he]
  change ak.homEquiv _ _ (ah.homEquiv _ _
    ((proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
      (quotientPullback d g n).hom ≫ (quotientPullback d f n).hom)) ≫
      D.hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (D.hom.app (CompletedConstantReduction.residue X d.ideal n)).val.app U
    (((proEtaleRingModuleAdjunction g (ring d Z) (ring d Y) (coefficients d g)).homEquiv
      _ _ ((quotientPullback d g n).hom ≫
        (proEtaleRingModuleAdjunction f (ring d Y) (ring d X)
          (coefficients d f)).homEquiv _ _ (quotientPullback d f n).hom)).val.app U x) = _
  rw [Adjunction.homEquiv_naturality_right]
  change (D.hom.app (CompletedConstantReduction.residue X d.ideal n)).val.app U
    (((proEtaleRingModuleAdjunction f (ring d Y) (ring d X)
      (coefficients d f)).homEquiv _ _ (quotientPullback d f n).hom).val.app
        ((proEtaleBaseChange g).op.obj U)
        (((proEtaleRingModuleAdjunction g (ring d Z) (ring d Y)
          (coefficients d g)).homEquiv _ _ (quotientPullback d g n).hom).val.app U x)) = _
  rw [hq, hq, hD]
  -- Both composites are the extension of the same constant-presheaf section map.
  have hrho : rho X Z (f ≫ g) = rho Y Z g ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map (rho X Y f) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eFG := (MorphismProperty.Over.pullbackComp
            (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
          (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).hom.app
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj Q) := by
    apply ((proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}).homEquiv _ _).symm.injective
    change (proEtaleConstantComparison (f ≫ g)).app Q = _
    rw [proEtaleConstantComparison_comp f g Q]
    exact (adjunct_comp_comparison (proEtaleSheafAdjunction g CommRingCat.{u + 1})
      (proEtaleSheafAdjunction f CommRingCat.{u + 1})
      (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})
      (Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
        (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X))
      (rho Y Z g) (rho X Y f)).symm
  exact (congrArg (fun t ↦ t.hom.app U x) hrho).symm.trans
    (hq X Z (f ≫ g) U x).symm


set_option cleanup.letToHave true in
set_option linter.flexible false in
private theorem derived_single_compositor
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (L : C ⥤ D) (M : D ⥤ E) (N : C ⥤ E)
    [L.Additive] [M.Additive] [N.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (e : N ≅ L ⋙ M) (Q : C) (Q' : D) (Q'' : E)
    (a : L.obj Q ≅ Q') (b : M.obj Q' ≅ Q'') (c : N.obj Q ≅ Q'')
    (he : e.hom.app Q ≫ M.map a.hom ≫ b.hom = c.hom) :
    ((Functor.mapDerivedCategoryNatIso e).hom.app
      ((DerivedCategory.singleFunctor C 0).obj Q) ≫
      (Functor.mapDerivedCategoryCompIso L M).hom.app
        ((DerivedCategory.singleFunctor C 0).obj Q)) ≫
      M.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app Q ≫
        (DerivedCategory.singleFunctor D 0).map a.hom) ≫
      ((M.mapDerivedCategorySingleFunctor 0).hom.app Q' ≫
        (DerivedCategory.singleFunctor E 0).map b.hom) =
    (N.mapDerivedCategorySingleFunctor 0).hom.app Q ≫
      (DerivedCategory.singleFunctor E 0).map c.hom := by
  have h := Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor L M N e Q
  have hn := (M.mapDerivedCategorySingleFunctor 0).hom.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% h]
  simp only [← Functor.map_comp, he]

set_option cleanup.letToHave true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
private theorem quotientDerivedPullback_compositor {Z : Scheme.{u}} (g : Y ⟶ Z) (n : ℕ) :
    (eqToIso (congrArg (proEtaleRingDerivedPullback (f ≫ g) (ring d Z) (ring d X))
      (coefficients_comp d f g).symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison f g (ring d Z) (ring d Y)
          (ring d X) (coefficients d g) (coefficients d f)).hom.app (quotient d Z n) ≫
      (pullback d f).map (quotientDerivedPullback d g n).hom ≫
        (quotientDerivedPullback d f n).hom = (quotientDerivedPullback d (f ≫ g) n).hom := by
  obtain ⟨_, _, _, _, _, _, D, hD, _⟩ := proEtaleRingDerivedPullbackComposition f g
    (ring d Z) (ring d Y) (ring d X) (coefficients d g) (coefficients d f)
    (coefficients d (f ≫ g)) (coefficients_comp d f g).symm
  rw [proEtaleCanonicalDerivedPullback_normalization f g (ring d Z) (ring d Y)
    (ring d X) (coefficients d g) (coefficients d f) (coefficients d (f ≫ g))
    (coefficients_comp d f g) D hD]
  let e := (Adjunction.leftAdjointCompIso
    (proEtaleRingModuleAdjunction g (ring d Z) (ring d Y) (coefficients d g))
    (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleRingModuleAdjunction (f ≫ g) (ring d Z) (ring d X)
      (coefficients d (f ≫ g))) D).symm
  exact derived_single_compositor
    (proEtaleRingModulePullback g (ring d Z) (ring d Y) (coefficients d g))
    (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleRingModulePullback (f ≫ g) (ring d Z) (ring d X) (coefficients d (f ≫ g)))
    e (CompletedConstantReduction.residue Z d.ideal n)
    (CompletedConstantReduction.residue Y d.ideal n)
    (CompletedConstantReduction.residue X d.ideal n)
    (quotientPullback d g n) (quotientPullback d f n) (quotientPullback d (f ≫ g) n)
    (quotientPullback_compositor d f g n D hD)

end QuotientComposition

section BaseChange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)
  (aY' : ProEtaleTensorModel Y' (ring d Y'))
  (aX' : ProEtaleTensorModel X' (ring d X'))

set_option linter.flexible false in
/-- The canonical completed coefficient identifications agree around the square.
Source: blueprint order 1275, proof step 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: use identity/composition coherence of profinite coefficient inverse image.
At every quotient the two composites preserve the same constant sections and agree
by square commutativity. The completed projections determine the comparison uniquely,
so the resulting composite coefficient isomorphisms agree, with the required transport. -/
theorem coefficients_square (sq : ChosenCartesianSquare g' f' f g) : HEq
    (proEtaleRingCompositeCoefficients g' f (ring d Y) (ring d X) (ring d X')
      (coefficients d f) (coefficients d g'))
    (proEtaleRingCompositeCoefficients f' g (ring d Y) (ring d Y') (ring d X')
      (coefficients d g) (coefficients d f')) := by
  rw [coefficients_comp, coefficients_comp]
  have h := sq.w
  generalize g' ≫ f = k₁ at h ⊢
  generalize f' ≫ g = k₂ at h ⊢
  cases h
  rfl

set_option linter.flexible false in
/-- The actual base-change morphism, with the canonical completed coefficient coherence.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def exchange :=
  proEtaleAmbientRingedExchange sq (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq)

set_option linter.flexible false in
/-- Source comparison in the reduction projection-formula square: tensor pullback,
then base change of K and the canonical quotient comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def baseChangeSource (n : ℕ) :
    (pullback d g).obj (aY.tensor.obj ((directImage d f).obj K, quotient d Y n)) ⟶
      aY'.tensor.obj ((directImage d f').obj ((pullback d g').obj K), quotient d Y' n) :=
  (proEtaleCanonicalTensorComparison g (ring d Y) (ring d Y') (coefficients d g)
    aY aY').hom.app ((directImage d f).obj K, quotient d Y n) ≫
      aY'.tensor.map (Prod.mkHom ((exchange d f sq).app K)
        (quotientDerivedPullback d g n).hom)

set_option linter.flexible false in
/-- Target comparison in that square: ordinary ambient exchange and tensor pullback,
followed by the canonical quotient comparison. Exchange is not assumed invertible.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def baseChangeTarget (n : ℕ) :
    (pullback d g).obj ((directImage d f).obj (reduction d aX K n)) ⟶
      (directImage d f').obj (reduction d aX' ((pullback d g').obj K) n) :=
  (exchange d f sq).app (reduction d aX K n) ≫
    (directImage d f').map
      ((proEtaleCanonicalTensorComparison g' (ring d X) (ring d X') (coefficients d g')
        aX aX').hom.app (K, quotient d X n) ≫
          aX'.tensor.map (Prod.mkHom (𝟙 ((pullback d g').obj K))
            (quotientDerivedPullback d g' n).hom))

attribute [local irreducible] proEtaleProjectionFormulaMate proEtaleAmbientRingedExchange
  proEtaleCanonicalTensorComparison

-- Avoid repeated inspection of the large native-operation tactic contexts.
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option cleanup.letToHave true in
/-- Both directions of the reduction projection formula commute with base change.
Source: blueprint order 1275, proof step 6 and order 1274, base-change paragraph
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the normalized quotient adjuncts are the canonical constant-section maps,
which compose by sheafification. The ordinary compositor normalization and its
exact-derived degree-zero formula give the quotient pullback square. Postcompose
the projection base-change equation by the quotient identifications and apply
exchange, tensor and coefficient naturality. Cancel the two reduction isomorphisms
to obtain the inverse square; exchange need not be invertible. -/
theorem baseChange_compatibility (n : ℕ) :
    (pullback d g).map (reductionMap d f aY aX K n) ≫
      baseChangeTarget d f aX K sq aX' n =
    baseChangeSource d f aY K sq aY' n ≫
      reductionMap d f' aY' aX' ((pullback d g').obj K) n ∧
    baseChangeTarget d f aX K sq aX' n ≫
      inverse d f' aY' aX' ((pullback d g').obj K) n =
    (pullback d g).map (inverse d f aY aX K n) ≫
      baseChangeSource d f aY K sq aY' n := by
  let theta := proEtaleAmbientRingedPullbackComparison sq
    (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq)
  have hq : theta.inv.app (quotient d Y n) ≫
      (pullback d f').map (quotientDerivedPullback d g n).hom ≫
        (quotientDerivedPullback d f' n).hom =
      (pullback d g').map (quotientDerivedPullback d f n).hom ≫
        (quotientDerivedPullback d g' n).hom := by
    let cR := eqToIso (congrArg
      (proEtaleRingDerivedPullback (g' ≫ f) (ring d Y) (ring d X'))
      (coefficients_comp d g' f).symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison g' f (ring d Y) (ring d X)
          (ring d X') (coefficients d f) (coefficients d g')
    let cL := eqToIso (congrArg
      (proEtaleRingDerivedPullback (f' ≫ g) (ring d Y) (ring d X'))
      (coefficients_comp d f' g).symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison f' g (ring d Y) (ring d Y')
          (ring d X') (coefficients d g) (coefficients d f')
    have hc : cR ≪≫ theta.symm = eqToIso (congrArg (pullback d) sq.w) ≪≫ cL := by
      apply Iso.ext
      apply NatTrans.ext
      funext P
      simp only [cR, cL, theta, proEtaleAmbientRingedPullbackComparison,
        Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
        Category.assoc, Iso.hom_inv_id_app_assoc, eqToIso.hom, eqToIso.inv,
        eqToHom_app, eqToHom_trans_assoc]
      rfl
    have ht : (eqToIso (congrArg (pullback d) sq.w)).hom.app (quotient d Y n) ≫
        (quotientDerivedPullback d (f' ≫ g) n).hom =
          (quotientDerivedPullback d (g' ≫ f) n).hom := by
      have transport (kR kL : X' ⟶ Y) (hw : kR = kL) :
          (eqToIso (congrArg (pullback d) hw)).hom.app (quotient d Y n) ≫
            (quotientDerivedPullback d kL n).hom =
              (quotientDerivedPullback d kR n).hom := by
        cases hw
        simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      exact transport _ _ sq.w
    apply (cancel_epi (cR.hom.app (quotient d Y n))).mp
    have he := congrArg (fun e ↦ e.hom.app (quotient d Y n)) hc
    change cR.hom.app (quotient d Y n) ≫ theta.inv.app (quotient d Y n) =
      (eqToIso (congrArg (pullback d) sq.w)).hom.app (quotient d Y n) ≫
        cL.hom.app (quotient d Y n) at he
    simp only [← Category.assoc]
    rw [he]
    simp only [Category.assoc]
    rw [quotientDerivedPullback_compositor d f' g n, ht,
      quotientDerivedPullback_compositor d g' f n]
  have h := proEtaleProjectionFormula_baseChange sq
    (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq) aY aX aY' aX' K (quotient d Y n)
  have forward : (pullback d g).map (reductionMap d f aY aX K n) ≫
      baseChangeTarget d f aX K sq aX' n =
    baseChangeSource d f aY K sq aY' n ≫
      reductionMap d f' aY' aX' ((pullback d g').obj K) n := by
    have hp := projection_naturality d f' aY' aX' ((pullback d g').obj K)
      (quotientDerivedPullback d g n).hom
    have hb := reduction_square_algebra
      (C := @DerivedCategory (proEtaleRingModules X (ring d X)) _
        (@SheafOfModules.instAbelian _ _ _ _
          SheafOfModules.hasSheafify_coefficientUniverse
          SheafOfModules.wEqualsLocallyBijective_coefficientUniverse) _)
      (D := @DerivedCategory (proEtaleRingModules Y (ring d Y)) _
        (@SheafOfModules.instAbelian _ _ _ _
          SheafOfModules.hasSheafify_coefficientUniverse
          SheafOfModules.wEqualsLocallyBijective_coefficientUniverse) _)
      (C' := @DerivedCategory (proEtaleRingModules X' (ring d X')) _
        (@SheafOfModules.instAbelian _ _ _ _
          SheafOfModules.hasSheafify_coefficientUniverse
          SheafOfModules.wEqualsLocallyBijective_coefficientUniverse) _)
      (D' := @DerivedCategory (proEtaleRingModules Y' (ring d Y')) _
        (@SheafOfModules.instAbelian _ _ _ _
          SheafOfModules.hasSheafify_coefficientUniverse
          SheafOfModules.wEqualsLocallyBijective_coefficientUniverse) _)
      (proEtaleRingDerivedPullback f (ring d Y) (ring d X) (coefficients d f))
        (proEtaleRingDerivedDirectImage f (ring d Y) (ring d X) (coefficients d f))
        (proEtaleRingDerivedPullback f' (ring d Y') (ring d X') (coefficients d f'))
        (proEtaleRingDerivedDirectImage f' (ring d Y') (ring d X') (coefficients d f'))
        (proEtaleRingDerivedPullback g (ring d Y) (ring d Y') (coefficients d g))
        (proEtaleRingDerivedPullback g' (ring d X) (ring d X') (coefficients d g'))
      aY.tensor aX.tensor aY'.tensor aX'.tensor
      (proEtaleAmbientRingedExchange sq (ring d X) (ring d Y) (ring d X') (ring d Y')
        (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
        (coefficients_square d f sq))
      (proEtaleCanonicalTensorComparison g (ring d Y) (ring d Y')
        (coefficients d g) aY aY').hom
      (proEtaleCanonicalTensorComparison g' (ring d X) (ring d X')
        (coefficients d g') aX aX').hom
      K (quotient d Y n) (quotient d X n) (quotient d Y' n) (quotient d X' n)
      (quotientDerivedPullback d f n).hom (quotientDerivedPullback d g n).hom
      (quotientDerivedPullback d f' n).hom (quotientDerivedPullback d g' n).hom
      ((proEtaleAmbientRingedPullbackComparison sq (ring d X) (ring d Y) (ring d X') (ring d Y')
        (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
        (coefficients_square d f sq)).inv.app (quotient d Y n))
      (proEtaleProjectionFormulaMate f (ring d Y) (ring d X) (coefficients d f)
        aY aX K (quotient d Y n))
      (proEtaleProjectionFormulaMate f' (ring d Y') (ring d X') (coefficients d f')
        aY' aX' ((proEtaleRingDerivedPullback g' (ring d X) (ring d X') (coefficients d g')).obj K)
          (quotient d Y' n))
      (proEtaleProjectionFormulaMate f' (ring d Y') (ring d X') (coefficients d f')
        aY' aX' ((proEtaleRingDerivedPullback g' (ring d X) (ring d X') (coefficients d g')).obj K)
          ((proEtaleRingDerivedPullback g (ring d Y) (ring d Y') (coefficients d g)).obj (quotient d
            Y n))) hq hp
      h
    perfect_projection_exact hb
  refine ⟨forward, ?_⟩
  have := (reductionMap_isIso d f aY aX K n).2
  have := (reductionMap_isIso d f' aY' aX' ((pullback d g').obj K) n).2
  have hi := inverse_square (C := derived d Y')
    ((pullback d g).map (reductionMap d f aY aX K n))
    (reductionMap d f' aY' aX' ((pullback d g').obj K) n)
    (baseChangeSource d f aY K sq aY' n)
    (baseChangeTarget d f aX K sq aX' n) forward
  simpa only [inverse, reductionIso, asIso_inv, Functor.map_inv] using hi.symm

end BaseChange

set_option linter.flexible false in
/-- Proper morphisms give precisely the identity-compactification formula and inverse,
after the displayed quotient pullback identification.
Source: blueprint order 1275, first proof; identity-compactification lemma, order 1272
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: identity-compactification identifies j_!, Lj^*, theta_1 and their constraints
with identities, so the ordered formula is the same projection mate. Compose with
the canonical quotient pullback identification for the forward equation and with
its inverse for the reverse equation. Uniqueness of inverse identifies rho_n. -/
theorem identityCompactification_compatibility [IsProper f] (n : ℕ) :
    reductionMap d f aY aX K n =
      IdentityProjectionCompactification.forward f (ring d Y) (ring d X)
        (coefficients d f) aY aX K (quotient d Y n) ≫
      (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom)) ∧
    inverse d f aY aX K n =
      (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).inv)) ≫
      IdentityProjectionCompactification.backward f (ring d Y) (ring d X)
        (coefficients d f) aY aX K (quotient d Y n)
        (reductionMap_isIso d f aY aX K n).1 := by
  have : IsIso (projection d f aY aX K (quotient d Y n)) :=
    (perfect_projection_formula d f aY aX K).2.2.2 _
      (reductionMap_isIso d f aY aX K n).1
  constructor
  · dsimp only [IdentityProjectionCompactification.forward,
      IdentityProjectionCompactification.theta]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  · let q := quotientDerivedPullback d f n
    let e := (directImage d f).mapIso (aX.tensor.mapIso ((Iso.refl K).prod q))
    have hp : IsIso (projection d f aY aX K (quotient d Y n)) := this
    change inv (projection d f aY aX K (quotient d Y n) ≫ e.hom) =
      e.inv ≫ _
    rw [IsIso.inv_comp]
    have he : inv e.hom = e.inv := IsIso.inv_eq_of_hom_inv_id e.hom_inv_id
    rw [he]
    congr 1
    change inv (projection d f aY aX K (quotient d Y n)) = _
    dsimp only [IdentityProjectionCompactification.backward,
      IdentityProjectionCompactification.rho]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]


end AlgebraicGeometry.Scheme.PerfectProjection
