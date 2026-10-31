/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.SixFunctors.ListedCoefficientCtf
import WeilConjectures.SixFunctors.ScalarDirectImageElementaryCases

/-! # Coefficient comparison for ordinary direct image

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.md and its proof; Stacks Project, Tag 0F12.
(blueprint: det-prop-scalar-six-direct-image).

The morphism is the published counit mate of the normalized scalar pullback comparison.
The ambient coherence statements have no constructibility or boundedness hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarSixChange
attribute [local irreducible] scalarDirectImageMate


set_option maxHeartbeats 800000 in
-- Keep the finite coefficient induction and derived-functor coherence in one declaration.
/-- For every listed coefficient map the specified direct-image comparison is invertible
on bounded constructible objects of finite Tor amplitude, with both outputs in that
subcategory. Its naturality, composition, unit and counit equations hold on ambient
ordinary unbounded derived categories.

Source: blueprint latest, det-prop-scalar-six-direct-image, clauses (1)--(2),
and its proof, Formal properties, Preservation and the coefficient cases; Stacks 0F12.
(blueprint: det-prop-scalar-six-direct-image).

Proof:
1. Apply lem-sfb-scalar-direct-image-mate-coherence to scalarDirectImageMate.
The mate is the unit, then direct image of the inverse normalized pullback square,
then direct image of scalar extension of the counit. Its coherence theorem gives
naturality, composition and exactly the two displayed adjunction identities.
2. The morphism is finite type by lemma-nagata-finite-type-to-separated-target.
Its diagonal is the base change of the closed diagonal of X over k, hence closed
by lem-weil-pbc-closed-immersion-base-change. It is separated by
 def-weil-proper-morphism and qcqs by def-weil-closed-immersion,
def-weil-finite-type-morphism and def-weil-quasi-separated-morphism.
Apply det-thm-sf-ctf-stability-direct-images (3) and det-prop-scalar-six-ctf (3)
in the two orders to put both outputs in the required subcategory.
3. For finite A to B use lem-sfb-finite-ring-relative-scalar-comparison, whose
B-linear isomorphism is the specified counit mate; no flatness is required.
4. For integral and field finite extensions, sk-prop-sfb-cartesian-coefficients (2)
makes the coefficient sheaf finite free; lem-sp-finite-free-direct-image-coherence
identifies its invertible mate with this one. For continuous O_E to finite A use
lem-sfb-integral-finite-scalar-perfect-model and its pulled-back two-term model.
5. The input is bounded, hence bounded below. For O_E to E and E to Qbar apply
lem-sfb-localized-direct-image-comparison and lem-sfb-qlbar-direct-image-comparison.
Their ambient derived comparisons are this mate, by the adjunction of
 def-sfb-module-derived-pushpull-adjunction and det-prop-scalar-six-pullback (1).
6. Iterate the coefficient-pasting identity of
lem-sfb-scalar-direct-image-mate-coherence. Every intermediate input remains
bounded constructible of finite Tor amplitude by det-prop-scalar-six-ctf (3).
The identity case is the triangle identity. This proves (1); step 1 proves (2). -/
theorem scalarSixDirectImage
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left),
      (constantModelBoundedConstructible Λ.X X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K) ∧
      (constantModelBoundedConstructible Λ'.X Y.left
          ((scalarSixChange a Y.left).obj ((RootCoordinateFace.lower Λ.X f.left).obj K)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((scalarSixChange a Y.left).obj ((RootCoordinateFace.lower Λ.X f.left).obj K))) ∧
      (constantModelBoundedConstructible Λ'.X Y.left
          ((RootCoordinateFace.lower Λ'.X f.left).obj ((scalarSixChange a X.left).obj K)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((RootCoordinateFace.lower Λ'.X f.left).obj ((scalarSixChange a X.left).obj K)))) ∧
    (∀ (K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left))
      (h : K ⟶ K'),
      (scalarSixChange a Y.left).map ((RootCoordinateFace.lower Λ.X f.left).map h) ≫
          (scalarDirectImageMate a f.left).app K' =
        (scalarDirectImageMate a f.left).app K ≫
          (RootCoordinateFace.lower Λ'.X f.left).map ((scalarSixChange a X.left).map h)) ∧
    (∀ (W : Over (Spec (.of k)))
      [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
      (g : Y ⟶ W) (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)),
      (scalarDirectImageMate a (f.left ≫ g.left)).app K ≫
          (RootCoordinateFace.lowerComp Λ'.X f.left g.left).hom.app
            ((scalarSixChange a X.left).obj K) =
        (scalarSixChange a W.left).map
            ((RootCoordinateFace.lowerComp Λ.X f.left g.left).hom.app K) ≫
          (scalarDirectImageMate a g.left).app ((RootCoordinateFace.lower Λ.X f.left).obj K) ≫
          (RootCoordinateFace.lower Λ'.X g.left).map
            ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y.left),
      (scalarSixChange a Y.left).map ((RootCoordinateFace.adjunction Λ.X f.left).unit.app N) ≫
          (scalarDirectImageMate a f.left).app ((scalarSixPull Λ f.left).obj N) =
        (RootCoordinateFace.adjunction Λ'.X f.left).unit.app
            ((scalarSixChange a Y.left).obj N) ≫
          (RootCoordinateFace.lower Λ'.X f.left).map
            ((scalarDirectImagePullbackData.theta a f.left).inv.app N)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left),
      (scalarSixPull Λ' f.left).map ((scalarDirectImageMate a f.left).app K) ≫
          (RootCoordinateFace.adjunction Λ'.X f.left).counit.app
            ((scalarSixChange a X.left).obj K) =
        (scalarDirectImagePullbackData.theta a f.left).inv.app
            ((RootCoordinateFace.lower Λ.X f.left).obj K) ≫
          (scalarSixChange a X.left).map
            ((RootCoordinateFace.adjunction Λ.X f.left).counit.app K)) := by
  classical
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  let : f.left.IsOver (Spec (.of k)) := ⟨Over.w f⟩
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have hpush (Γ : ScalarSixRing.{u})
      (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X)
      (K : DerivedCategory (ModuleRingedComparison.internalModules Γ.X X.left))
      (hK : constantModelBoundedConstructible Γ.X X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) :
      constantModelBoundedConstructible Γ.X Y.left
          ((RootCoordinateFace.lower Γ.X f.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((RootCoordinateFace.lower Γ.X f.left).obj K) :=
    (constructibleFiniteTor_stability_direct_images (hcd := hcd) ell k Γ.X hΓ f.left).2.2.2.1 K hK
  obtain ⟨hfin, hint, hfield, hloc, hclosure, hintfin, hid⟩ :=
    scalarDirectImageElementaryCases ell k f
  have hinv : ∀ {Γ Γ' : ScalarSixRing.{u}} (b : Γ ⟶ Γ'),
      ListedCoefficientMap ell b →
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules Γ.X X.left),
      (constantModelBoundedConstructible Γ.X X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate b f.left).app K) := by
    intro Γ Γ' b hb
    induction hb with
    | finite A B hA hB φ b hb => exact hfin A B hA hB φ b hb
    | integers E F h b hb => exact hint E F h b hb
    | fields E F h b hb => exact hfield E F h b hb
    | localization E b hb => exact hloc E b hb
    | algebraicClosure E b hb => exact hclosure E b hb
    | integralFinite E A hA b hb => exact hintfin E A hA b hb
    | algebraicClosureIdentity => exact fun K _ ↦ hid K
    | @comp Γ Γ' Γ'' b c hb hc ihb ihc =>
      intro K hK
      have := ihb K hK
      have hchanged := (listedCoefficientCtf ell b hb).2.2 k X K hK
      have := ihc ((scalarSixChange b X.left).obj K) hchanged
      have heq := (scalarDirectImageMateCoherence b f.left (𝟙 Y.left)).2.2.2.2 Γ'' c K
      have hcomp : IsIso
          ((scalarSixTower b c Y.left).hom.app ((RootCoordinateFace.lower Γ.X f.left).obj K) ≫
            (scalarDirectImageMate (b ≫ c) f.left).app K) := by
        rw [heq]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((scalarSixTower b c Y.left).hom.app ((RootCoordinateFace.lower Γ.X f.left).obj K)) _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨hΛ, hΛ', hchange⟩ := listedCoefficientCtf ell a _ha
    exact ⟨hinv a _ha K hK, hchange k Y _ (hpush Λ hΛ K hK),
      hpush Λ' hΛ' _ (hchange k X K hK)⟩
  · exact (scalarDirectImageMateCoherence a f.left (𝟙 Y.left)).1
  · intro W _ _ _ g K
    exact (scalarDirectImageMateCoherence a f.left g.left).2.1 K
  · exact (scalarDirectImageMateCoherence a f.left (𝟙 Y.left)).2.2.1
  · exact (scalarDirectImageMateCoherence a f.left (𝟙 Y.left)).2.2.2.1

end AlgebraicGeometry.ProEtale.CondensedRing
