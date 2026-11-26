/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionFunctors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBrownAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralTateLineConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralProjectiveLineAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralAffinePurityInduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralTensorInverseImage
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Integral purity for the projective line and affine space

The twists use the published integral Tate line and its signed powers. The sectionwise
module equivalence transports that line into the same internal-module category as Brown's
adjunction. All functors below use ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

private theorem twistedPull_constructible (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ)
    (hline : boundedConstructible (condensedRingObj
      (Profinite.padicIntegersRingObj ℓ E.val) X)
        ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))))
    (K : IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y)
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
      ((pullTwistShift ℓ E f d).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have eY := (adicConstructibilityPredicateComparison ℓ Y Λ
    (IsEllAdicCoefficient.integral E.val)).2
  have eX := (adicConstructibilityPredicateComparison ℓ X Λ
    (IsEllAdicCoefficient.integral E.val)).2
  rw [← eY] at hK
  rw [← eX]
  let : IsNoetherian X := ⟨⟩
  let : (boundedConstructible (condensedRingObj Λ X)).IsTriangulated :=
    isTriangulated_boundedConstructible_ellAdic_padicIntegers X ℓ E.val
  have ht := integralTensorInverseImage ℓ E k f
  have h := ht.2.1 _ _ (ht.1 K hK).1 hline
  exact (boundedConstructible (condensedRingObj Λ X)).le_shift _ _ h

private theorem twistedPull_localizing {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hbc : ∀ K, constantModelBoundedConstructible
      (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K)) :
    ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let T := (DerivedCategory.singleFunctor C 0).obj (tateLine ℓ E X (d : ℤ))
  let F := IntegralCompactSupport.pull Λ f ⋙ (curriedTensor (DerivedCategory C)).flip.obj T
  let P := IntegralCompactSupport.localizing Λ X
  have hP := (localizingClosure_exists Λ X
    (constantModelBoundedConstructible Λ X)).2.2.2.1
  let : P.IsTriangulated := hP.1
  let : P.IsClosedUnderIsomorphisms := hP.2.1
  let : (IntegralCompactSupport.pull Λ f).CommShift ℤ :=
    unboundedLocalizingPullbackCommShift Λ f
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  let : (IntegralCompactSupport.pull Λ f).IsTriangulated :=
    Functor.isTriangulated_of_iso e
  let : (IntegralCompactSupport.pull Λ f).IsLeftAdjoint :=
    (derivedUpperStarLowerStarAdjunction Λ f).isLeftAdjoint
  let : BraidedCategory (DerivedCategory C) := (DerivedCategory.nonempty_braidedCategory C).some
  let : ((curriedTensor (DerivedCategory C)).flip.obj T).CommShift ℤ :=
    DerivedCategory.commShiftTensorRight C T
  let : F.CommShift ℤ := by dsimp only [F]; infer_instance
  let : ((curriedTensor (DerivedCategory C)).flip.obj T).IsTriangulated :=
    DerivedCategory.isTriangulated_tensorRight C T
  have : F.IsTriangulated := by dsimp only [F]; infer_instance
  have : F.IsLeftAdjoint := by dsimp [F]; infer_instance
  intro K hK
  have hF : P ((shiftFunctor _ (2 * (d : ℤ))).obj (F.obj K)) := by
    apply P.le_shift
    apply hK (P.inverseImage F)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hmem
      let := hD
      have h := hP.2.2 (D ⋙ F) inferInstance hmem
      exact P.prop_of_iso (preservesColimitIso F D).symm h
    · intro L hL
      have h := (localizingClosure_exists Λ X
        (constantModelBoundedConstructible Λ X)).2.2.2.2.1 _ (hbc L hL)
      exact (P.prop_shift_iff_of_isStableUnderShift (F.obj L) (2 * (d : ℤ))).mp h
  exact hF

private noncomputable def liftIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun A ↦ P.isoMk (e.app A)) (by
    intro A B m
    apply ObjectProperty.hom_ext
    exact e.hom.naturality m)

private noncomputable def space (k : Type u) [Field k] (T : Scheme.{u})
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    IntegralCompactSupport.Spaces k :=
  ⟨Over.mk (T ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (T ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (T ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (T ↘ Spec (.of k)))⟩⟩

private noncomputable def properImageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] :
    IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
        (Compactification.ofIsProper f) ≅
      IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f :=
  Functor.isoWhiskerRight
      (derivedOpenImmersionLowerShriekId (Profinite.padicIntegersRingObj ℓ E.val) X) _ ≪≫
    Functor.leftUnitor _

private theorem properPush_localizing (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let fs : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let c : Compactification.QuasiCompactObjects f :=
    ⟨Compactification.ofIsProper f, inferInstanceAs (QuasiCompact (𝟙 X))⟩
  obtain ⟨pres, _, _, _⟩ := IntegralCompactSupport.integralLocalizingCompactSupport ℓ E k
  have hP := (localizingClosure_exists Λ Y
    (constantModelBoundedConstructible Λ Y)).2.2.2.1
  let : (IntegralCompactSupport.localizing Λ Y).IsClosedUnderIsomorphisms := hP.2.1
  intro K hK
  exact (IntegralCompactSupport.localizing Λ Y).prop_of_iso
    ((properImageIso ℓ E f).app K) (pres.maps_localizing (f := fs) c K hK)

private theorem properBrownComparison (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K))
    (G : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (adj : restrictedPush ℓ E f hr ⊣ G) : brownComparison ℓ E f G := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let fs : space k X ⟶ space k Y := ObjectProperty.homMk (f.asOver (Spec (.of k)))
  let cp : Compactification.QuasiCompactObjects f :=
    ⟨Compactification.ofIsProper f, inferInstanceAs (QuasiCompact (𝟙 X))⟩
  obtain ⟨_, φ, _, _⟩ := IntegralCompactSupport.integralLocalizingCompactSupport ℓ E k
  intro c h J hJ
  obtain ⟨adjJ⟩ := hJ
  let e : IntegralCompactSupport.lowerShriek Λ c.obj.obj h ≅ restrictedPush ℓ E f hr :=
    liftIso (IntegralCompactSupport.localizing Λ Y)
      (φ fs c.obj cp ≪≫ Functor.isoWhiskerLeft
        (IntegralCompactSupport.localizing Λ X).ι (properImageIso ℓ E f))
  exact ⟨(adjJ.ofNatIsoLeft e).rightAdjointUniq adj⟩

@[instance_reducible]
private noncomputable def residueUnits (k : Type u) [Field k]
    [Fact (ringChar k ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    ∀ x : X, Invertible (ℓ : X.residueField x) := by
  have hl : (ℓ : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ ℓ)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ℓ.Prime) hz)
  intro x
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation x).hom
  exact (show IsUnit (ℓ : X.residueField x) by
    simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hl).map φ).invertible

/-- Projective-line adjunction, affine-space purity, and preservation of Dbc by both
explicit candidate right adjoints, on exactly Loc(Dbc) for condensed integral coefficients. -/
theorem integralRestrictionLine (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (d : ℕ) :
    ∃ (hq : ∀ K, IntegralCompactSupport.localizing
          (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
          ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
      (hp : ∀ K, IntegralCompactSupport.localizing
          (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (AffineSpace (ULift.{u} (Fin d)) Y)
          ((pullTwistShift ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d).obj K))
      (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
          ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K)),
      Nonempty (restrictedPush ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) hr ⊣
        restrictedPull ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1 hq) ∧
      brownComparison ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)
        (restrictedPull ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1 hq) ∧
      brownComparison ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
        (restrictedPull ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d hp) ∧
      (∀ K, constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
          ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K)) ∧
      (∀ K, constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
          (AffineSpace (ULift.{u} (Fin d)) Y)
          ((pullTwistShift ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d).obj K)) := by
  let P := ProjectiveSpace (ULift.{u} (Fin 2)) Y
  let A := AffineSpace (ULift.{u} (Fin d)) Y
  let q : P ⟶ Y := P ↘ Y
  let p : A ⟶ Y := A ↘ Y
  let : P.Over (Spec (.of k)) := inferInstance
  let : A.Over (Spec (.of k)) := inferInstance
  let : LocallyOfFiniteType (P ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (q ≫ Y ↘ Spec (.of k)))
  let : QuasiCompact (P ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (q ≫ Y ↘ Spec (.of k)))
  let : IsSeparated (P ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (q ≫ Y ↘ Spec (.of k)))
  let : LocallyOfFiniteType (A ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ Y ↘ Spec (.of k)))
  let : QuasiCompact (A ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (p ≫ Y ↘ Spec (.of k)))
  let : IsSeparated (A ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (p ≫ Y ↘ Spec (.of k)))
  let : ∀ x : P, Invertible (ℓ : P.residueField x) := residueUnits ℓ k P
  let : ∀ x : A, Invertible (ℓ : A.residueField x) := residueUnits ℓ k A
  have hqc := twistedPull_constructible ℓ E k q 1
    (integralTateLine_constructible ℓ E P 1)
  have hpc := twistedPull_constructible ℓ E k p d
    (integralTateLine_constructible ℓ E A (d : ℤ))
  have hq := twistedPull_localizing ℓ E q 1 hqc
  have hp := twistedPull_localizing ℓ E p d hpc
  have hr := properPush_localizing ℓ E k q
  obtain ⟨adjq⟩ := integralProjectiveLine_adjunction ℓ E k Y hq hr
  refine ⟨hq, hp, hr, ⟨adjq⟩, properBrownComparison ℓ E k q hr _ adjq, ?_, hqc, hpc⟩
  intro c h J hJ
  obtain ⟨adjJ⟩ := hJ
  obtain ⟨adjp⟩ := integralAffinePurity_induction ℓ E k Y d hp c h
  exact ⟨adjJ.rightAdjointUniq adjp⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
