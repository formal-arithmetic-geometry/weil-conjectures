/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module
public import Sheaf.SixFunctors.IntegralKernelTateComparison
public import Sheaf.Paper.RationalP1AmbientComposites
public import Sheaf.Paper.DiagonalCoefficientDiagrams
/-! # The fixed integral diagonal unit and trace counit

Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
attribute [local instance 20000] CategoryTheory.Mod.derivedMonoidalCategory
/-- The prescribed twist-shift is the twist in the ambient diagonal formulas.
Source: the positive integral Tate-line convention in paragraph (1).
(blueprint: def-integral-kernel-unit-counit). -/
def integralAmbientTwistIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullTwistShift ℓ E f 1 ≅
      moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
        RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) X
          (spIntegralTwist X ℓ E) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let e := (DerivedCategory.singleFunctor (Modules Λ X) 0).mapIso
    (positiveTateLineIso ℓ E X)
  exact Functor.isoWhiskerLeft (moduleObjectDerivedPullback Λ f)
    (Functor.isoWhiskerRight ((curriedTensor _).flip.mapIso e) (shiftFunctor _ (2 : ℤ)))


/-- A pair of transformations on the two specified restricted functors.
Source: paragraph (1), displayed unit and counit.
(blueprint: def-integral-kernel-unit-counit). -/
def IntegralUnitCounitType
    (Y : Scheme.{u})
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K)) : Type (u + 2) :=
  (𝟭 _ ⟶ restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⋙
    restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq) ×
  (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq ⋙
    restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr ⟶ 𝟭 _)

/-- Componentwise normalization by the four-arrow diagonal insertion and inverse
projection followed by the trace. Every map is fixed; only invertibility proofs are
existential. Source: paragraph (1), formulas v, B and e.
(blueprint: def-integral-kernel-unit-counit). -/
def IntegralUnitCounitNormalized
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) (a : IntegralUnitCounitType ℓ E Y hq hr) : Prop :=
  (∀ M, ∃ hb hp,
    HEq ((a.1.app M).hom ≫
      (integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveLine Y ↘ Y)).obj M.obj))
      (RationalP1.unitComponent (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E)
        (by
          simpa only [traceTate] using
            (integralShiftedLinePullIso ℓ E (RationalP1.secondProjection Y))) M.obj hb hp)) ∧
  (∀ K, ∃ hp,
    HEq (a.2.app K).hom
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y ↘ Y)).map
          ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).hom.app K.obj) ≫
      RationalP1.counitComponent (Profinite.padicIntegersRingObj ℓ E.val) Y
        (fun X ↦ spIntegralTwist X ℓ E) (family.integral E) K.obj hp))

/-- The fixed diagonal and trace formulas form a unique natural pair.
Source: paragraph (1), construction of eta and epsilon.
(blueprint: lem-integral-unit-counit-construction).
Proof: proper base change inverts the self-square exchange on the localizing closure.
The proper projection formula inverts the q projection and the p2 twisted projection;
the shifted integral line belongs to the closure. The Cartesian Tate comparison fixes
its endpoints. Compose the section comparison, inverse diagonal tensor comparison,
diagonal class, inverse twisted projection, and inverse exchange to form eta.
For epsilon, invert the q projection and contract with the normalized trace.
Naturality of every factor proves naturality of these pastes. Fullness restricts them
using hq and hr. Extensionality of natural transformations and the two component
normalizations prove uniqueness; only invertibility proofs are existential. -/
theorem integralUnitCounit_existsUnique
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) :
    ∃! a : IntegralUnitCounitType ℓ E Y hq hr,
      IntegralUnitCounitNormalized ℓ E Y hq hr family a := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
