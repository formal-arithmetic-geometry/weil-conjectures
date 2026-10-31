/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelKunneth
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelScalarTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelSectionEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.IntegralKernelTraceTransport
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitFactorization
public import WeilConjectures.AlgebraicGeometry.RationalP1.SectionEvaluationCongruence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralTateLineConstructible
/-! # Ambient integral first contraction -/
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
open RationalP1
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

private theorem kernel_ambient_contraction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (u : M ⟶ (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)))
    (hu : UnitComponentNormalized Λ Y L d e M u)
    (v : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
    (hv : CounitComponentNormalized Λ Y L d
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) v)
    (h₁ : IsIso (projectionMap Λ (firstProjection Y) M
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (ht : firstTraceExchange Λ Y _ _ e ≫
      firstNativeFunctional Λ Y L d _ d.trace₁ ≫
        (singleUnitIso Λ (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
        (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫ (secondTraceUnitIso Λ Y).hom)
    (hk : ∀ T : DerivedCategory (Modules Λ (ProjectiveLine Y)),
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let B := moduleObjectDerivedPullback Λ (secondProjection Y)
    let e := nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
      (firstProjection Y) (secondProjection Y) (square Y)
    let e' := (mateEquiv
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
      (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ (square Y)).inv)).natTrans
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
      R.map ((e.app M ▷ T) ≫
        projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ e'.app T) ≫ projectionMap Λ (firstProjection Y) M (B.obj T))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map u ≫ v =
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((ρ_ M).inv ≫ (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map d.delta ≫ d.trace₁ ≫
          (singleUnitIso Λ (ProjectiveLine Y)).hom)) ≫ (ρ_ M).hom) := by
  obtain ⟨hb, hp, hunit⟩ := unit_factorization_generic Λ Y L d e M u hu
  have htransport := kernel_first_trace_transport Λ Y L d e M v hv hb hp h₁ ht hk
  let N := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let A := moduleObjectDerivedPullback Λ (firstProjection Y)
  let a := firstKernelInsertion Λ Y M N d.delta
  let tail : U.obj (A.obj M ⊗ N) ⟶
      (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          (R.obj M)) :=
    U.map (X := A.obj M ⊗ N)
        (tensorShiftIso Λ (diagonalSurface Y)
          (L (diagonalSurface Y)) (A.obj M)).hom ≫
      @inv _ _ _ _ (twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y))
        (e) (A.obj M)) hp ≫
      (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
        (by
          dsimp only [R, U, A]
          unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
          exact @inv _ _ _ _
            ((condensedAmbientExchange Λ (square Y)).app M) hb)
  have hu : u = a ≫ tail := by
    dsimp only [R, U, A, N, a, tail, id]
    section_evaluation_exact hunit
  have ht' : R.map tail ≫ v =
      firstTerminalFunctional Λ Y L d
        M N d.trace₁ h₁ := by
    simpa only [R, U, A, N, tail, id] using htransport
  calc
    R.map u ≫ v = R.map (a ≫ tail) ≫ v := by rw [hu]
    _ = R.map a ≫ (R.map tail ≫ v) := by rw [Functor.map_comp, Category.assoc]
    _ = R.map a ≫ firstTerminalFunctional Λ Y L
        d M N d.trace₁ h₁ :=
      congrArg (fun f => R.map a ≫ f) ht'
    _ = _ := kernel_section_evaluation Λ Y L d
      M N d.delta d.trace₁ h₁

theorem integralKernel_first_ambient_formula
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (family : Family ℓ Y) (href : IntegralFamilyReference ℓ Y family) :
    (∀ (M : DerivedCategory
        (Modules (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)))
      (_hM : localizingClosure (constantModelBoundedConstructible
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)) M)
      (u : M ⟶ (twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
        (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
          ((moduleObjectDerivedPullback
            (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M)))
      (v : (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
        ((twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
            ((moduleObjectDerivedPullback
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
              ((moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M))) ⟶
        (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M)
      (_hu : RationalP1.UnitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        (by simpa only [traceTate] using
          (integralShiftedLinePullIso ℓ E (secondProjection Y))) M u)
      (_hv : RationalP1.CounitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M) v),
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map u ≫ v =
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map
        ((ρ_ M).inv ≫ (M ◁
          ((singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y)).inv ≫ (family.integral E).support₁.hom ≫
            (family.integral E).R₁.R.map (family.integral E).delta ≫
            (family.integral E).trace₁ ≫
            (singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y)).hom)) ≫ (ρ_ M).hom)) := by
  intro M hM u v hu hv
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let L := fun X : Scheme.{u} ↦ spIntegralTwist X ℓ E
  obtain ⟨hY, aY, aP, aW, δ, ⟨reference⟩⟩ := href
  let := aY
  let := aP
  let := aW
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : IsProper (firstProjection Y) := by unfold firstProjection; infer_instance
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType (firstProjection Y)
  let : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) := by
    change LocallyOfFiniteType ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) := by
    change QuasiCompact ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) := by
    change IsSeparated ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    infer_instance
  let : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) := by
    change LocallyOfFiniteType
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k)))
    infer_instance
  let : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) := by
    change QuasiCompact (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫
      (Y ↘ Spec (.of k)))
    infer_instance
  let : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) := by
    change IsSeparated (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫
      (Y ↘ Spec (.of k)))
    infer_instance
  let : (firstProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  let : ∀ x : Y, Invertible (ℓ : Y.residueField x) := fun x ↦
    (residueIsUnit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
      Y (Y ↘ Spec (.of k)) x).invertible
  have hP : IsUnit (ℓ : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  let N := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
    (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
  have hline : constantModelBoundedConstructible Λ (diagonalSurface Y) N := by
    let : (boundedConstructible (condensedRingObj Λ (diagonalSurface Y))).IsTriangulated :=
      isTriangulated_boundedConstructible_ellAdic_padicIntegers
        (diagonalSurface Y) ℓ E.val
    have hz := integralTateLine_constructible ℓ E (diagonalSurface Y) 1
    have hi := (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).mapIso
      (positiveTateLineIso ℓ E (diagonalSurface Y))
    have hz' := (boundedConstructible (condensedRingObj Λ (diagonalSurface Y))).prop_of_iso
      hi hz
    have hs := (boundedConstructible (condensedRingObj Λ (diagonalSurface Y))).le_shift
      (2 : ℤ) _ hz'
    rw [← (adicConstructibilityPredicateComparison ℓ (diagonalSurface Y) Λ
      (IsEllAdicCoefficient.integral E.val)).2]
    exact hs
  have hN : localizingClosure (constantModelBoundedConstructible Λ (diagonalSurface Y)) N :=
    fun Q _ hQ ↦ hQ _ hline
  have h₁ := integral_kernel_projection_isIso ℓ E k (firstProjection Y) M N hM hN
  have hscalar := integral_kernel_scalar_trace ℓ E Y δ family reference hY hP
  have h := kernel_ambient_contraction
    (Profinite.padicIntegersRingObj ℓ E.val) Y
    (fun X ↦ spIntegralTwist X ℓ E) (family.integral E)
    (by simpa only [traceTate] using
      integralShiftedLinePullIso ℓ E (secondProjection Y))
    M u hu v hv h₁ (by
      section_evaluation_exact hscalar) (by
      section_evaluation_exact
        (kernel_native_kunneth (Profinite.padicIntegersRingObj ℓ E.val) Y M))
  section_evaluation_exact h

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
