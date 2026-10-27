/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all Sheaf.Paper.FiniteEtaleLocallyFreeModels

/-!
# Inverse image of lisse coefficient modules

Source: blueprint, coefficient-heart common-stratification proof (2), and Stacks
Tags 098C, 04J0, 03D7, 03DB and 03EK (blueprint: lem-sfb-lisse-module-inverse-image).

Slice restrictions use the recorded internal/sectionwise module equivalence, which keeps
sections, actions and restriction maps. Finite free modules are coproducts indexed by
`ULift (Fin r)`; the lift changes only the index universe, not the rank.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Base change of a specified finite-free trivializing cover gives a pro-etale cover
with the same finite-free ranks on the actual slice sites.
Source: blueprint common-stratification proof (2); Stacks Tags 098C and 04J0
(blueprint: lem-sfb-lisse-module-inverse-image).

Proof:
1. The original family is fpqc and weakly etale. Fpqc coverings and weakly etale
   morphisms are stable under arbitrary base change, so the displayed family covers T.
2. The coefficient map alpha_h is invertible. The internal-module operations transport
   equivalence identifies the prescribed upperStar with ordinary ringed-site pullback.
   The sectionwise equivalence preserves restrictions, regular modules and finite sums.
3. Localize the ringed-site morphism at U_i and its base change. The ringed localization
   comparison identifies pullback of the slice restriction with restriction of pullback.
4. The localized pullback is a left adjoint, hence preserves finite coproducts.
   It sends the regular module R to S tensor_A A, identified with S by multiplication,
   with inverse s mapped to s tensor 1. Balancing gives the two inverse identities.
5. Apply localized pullback to tau_i and compose these comparisons. This gives the
   required isomorphism with the same Fin (r i), including rank zero and empty schemes.
-/
theorem lisseModuleInverseImage_trivializations
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} (h : T ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S))
    {I : Type v} (U : I → S.ProEt)
    (_hU : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage S)
    (r : I → ℕ)
    (_τ : ∀ i : I,
      ((sectionModuleFunctor (Scheme.ProEt.topology S) (condensedRingObj Λ.X S)).obj M).over
          (U i) ≅ SheafOfModules.free (ULift.{u + 1} (Fin (r i)))) :
    (Presieve.ofArrows (fun i ↦ pullback (U i).hom h)
        (fun i ↦ pullback.snd (U i).hom h) ∈ Scheme.proetalePrecoverage T) ∧
      ∀ i : I, Nonempty
        (((sectionModuleFunctor (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)).obj
            ((CondensedRing.upperStar Λ.X h).obj M)).over
              (Scheme.ProEt.mk (pullback.snd (U i).hom h)) ≅
          SheafOfModules.free (ULift.{u + 1} (Fin (r i)))) := by
  classical
  refine ⟨?_, ?_⟩
  · exact Scheme.proetalePrecoverage.mem_coverings_of_isPullback
      (fun i ↦ (U i).hom) _hU h _ (fun i ↦ pullback.fst (U i).hom h)
      (fun i ↦ (IsPullback.of_hasPullback (U i).hom h).flip)
  · intro i
    let F := InternalModuleOperations.siteMap h
    let : F.IsContinuous (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) :=
      InternalModuleOperations.siteMap_continuous h
    let : PreservesFiniteLimits F :=
      inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h))
    let a := InternalModuleOperations.coefficientMap Λ.X h
    let N := (InternalModuleOperations.equivalence Λ.X S).functor.obj M
    let : (SheafOfModules.pushforward.{u + 1} a).IsRightAdjoint :=
      (InternalModuleOperations.adjunction Λ.X h).isRightAdjoint
    let hc := Scheme.ProEt.coverPreserving_overPullback h
    let := SheafOfModules.RingedSitePullback.local_continuous.{u + 1, u} (U := F) hc (U i)
    let b := SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} a (U i)
    let := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0}
      (U := Over.post F) b
    let : RepresentablyFlat (Over.post (X := U i) F) := flat_of_preservesFiniteLimits _
    let : (Over.post (X := U i) F).Final := final_of_representablyFlat _
    let e := (InternalModuleOperations.adjunction Λ.X h).leftAdjointUniq
      (SheafOfModules.pullbackPushforwardAdjunction a)
    exact ⟨(SheafOfModules.overFunctor (InternalModuleOperations.ring Λ.X T)
        (F.obj (U i))).mapIso ((InternalModuleOperations.upperComparison Λ.X h).app M) ≪≫
      (SheafOfModules.overFunctor (InternalModuleOperations.ring Λ.X T)
        (F.obj (U i))).mapIso (e.app N) ≪≫
      ((SheafOfModules.RingedSitePullback.localLeftIso.{u + 1, u, 0} a (U i)).app N).symm ≪≫
      (SheafOfModules.pullback b).mapIso (_τ i) ≪≫
      SheafOfModules.pullbackObjFreeIso b (ULift.{u + 1} (Fin (r i)))⟩

/-- Inverse image along any scheme morphism preserves lisse coefficient modules.
Source: blueprint common-stratification proof (2)
(blueprint: lem-sfb-lisse-module-inverse-image).

Proof: take a pro-etale finite-free trivializing cover witnessing lisseness. Apply the
preceding base-change and slice-trivialization assertion, and interpret the resulting
slice isomorphisms through the internal/sectionwise module equivalence. The base-changed
cover and the unchanged natural-number ranks witness lisseness of upperStar M. The
slice site at a weakly etale U is equivalent to the small pro-etale site of U, so this
is exactly the recorded IsLisseCoefficientModule predicate. No condition on h, Lambda,
connectedness or Noetherianity enters, and the empty cover and rank zero are allowed.
-/
theorem isLisseCoefficientModule_upperStar
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} (h : T ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S))
    (_hM : IsLisseCoefficientModule Λ.X M) :
    IsLisseCoefficientModule Λ.X ((CondensedRing.upperStar Λ.X h).obj M) := by
  exact CondensedRing.locFree_pullback Λ.X h M _hM

end AlgebraicGeometry.ProEtale
