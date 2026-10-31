/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Convert
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondInsertion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondScalarTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondTraceReordering
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
/-! # Ambient transport step for the second integral contraction -/
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

private theorem localizing_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {A B : IntegralCompactSupport.Ambient Λ X} (e : A ≅ B)
    (h : IntegralCompactSupport.localizing Λ X A) :
    IntegralCompactSupport.localizing Λ X B := by
  intro P hP hgen
  let := hP.2.1
  exact P.prop_of_iso e (h P hP hgen)

private theorem diagonalIntegral {C : Type*} [Category C] [MonoidalCategory C]
    (M U S T : C) (e : U ≅ 𝟙_ C)
    (s : U ⟶ S) (d : S ⟶ T) (t : T ⟶ U)
    (h : s ≫ d ≫ t = 𝟙 U) :
    (ρ_ M).inv ≫ (M ◁ (e.inv ≫ s ≫ d ≫ t ≫ e.hom)) ≫
      (ρ_ M).hom = 𝟙 M := by
  have hs := congrArg (fun f ↦ e.inv ≫ f ≫ e.hom) h
  simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id] at hs
  simp only [hs, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- Apply integration to the generic insertion and trace assembly. -/
private theorem ambient_second_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (f : (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶ M)
    (J : M ⊗ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    (hi : (pushSectionIso Λ Y).hom.app M ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (diagonalClassMap Λ Y L d M) =
      (ρ_ M).inv ≫
        (M ◁
          ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
            d.R₂.R.map d.delta ≫
            (secondDiagramPushIso Λ Y L d).hom.app
              (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
                (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) ≫ J)
    (ht : SecondTraceEquation Λ Y L d e M f J)
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    : unitComponent Λ Y L d e M hb hp ≫ f = 𝟙 M := by
  have h := assemble_second_unit Λ Y L d e M f J hi ht hb hp
  exact h.trans (diagonalIntegral M _ _ _ (singleUnitIso Λ (ProjectiveLine Y))
    _ _ _ d.integration₂)

private theorem transport_second_triangle_unit
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (R : D ⥤ C) (e : F ≅ G) (K : C)
    (η₀ : F.obj K ⟶ F.obj (R.obj (F.obj K)))
    (η₁ : G.obj K ⟶ F.obj (R.obj (G.obj K)))
    (ε : R.obj (F.obj K) ⟶ K)
    (u₁ : G.obj K ⟶ G.obj (R.obj (G.obj K)))
    (c : R.obj (G.obj K) ⟶ K)
    (hn : e.hom.app K ≫ η₁ = η₀ ≫ F.map (R.map (e.hom.app K)))
    (hu : η₁ ≫ e.hom.app (R.obj (G.obj K)) = u₁)
    (he : ε = R.map (e.hom.app K) ≫ c)
    (ht : u₁ ≫ G.map c = 𝟙 (G.obj K)) :
    (η₀ ≫ F.map ε) ≫ e.hom.app K = e.hom.app K := by
  calc
    (η₀ ≫ F.map ε) ≫ e.hom.app K =
        (η₀ ≫ F.map (R.map (e.hom.app K))) ≫ F.map c ≫ e.hom.app K := by
      rw [he, F.map_comp]
      simp only [Category.assoc]
    _ = (e.hom.app K ≫ η₁) ≫ F.map c ≫ e.hom.app K := by rw [← hn]
    _ = e.hom.app K ≫ ((η₁ ≫ e.hom.app (R.obj (G.obj K))) ≫ G.map c) := by
      rw [e.hom.naturality c]
      simp only [Category.assoc]
    _ = e.hom.app K := by rw [hu, ht, Category.comp_id]

private theorem postcomp_identity {C : Type*} [Category C]
    {A B X Y : C} (v f : A ⟶ B) (x : A ⟶ X) (y : X ⟶ Y) (z : Y ⟶ A)
    (hv : v = f) (hj : x ≫ y ≫ z = 𝟙 A) : v = x ≫ y ≫ z ≫ f := by
  calc
    v = f := hv
    _ = (𝟙 A) ≫ f := (Category.id_comp f).symm
    _ = (x ≫ y ≫ z) ≫ f := congrArg (fun t ↦ t ≫ f) hj.symm
    _ = x ≫ y ≫ z ≫ f := by simp only [Category.assoc]

/-- Transfer scalar exchange invertibility along equality of the line object. -/
private theorem secondExchange_isIso_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (M N : IntegralCompactSupport.Ambient Λ (ProjectiveLine Y)) (hMN : M = N)
    (h : IsIso (secondPretraceExchangeMap Λ Y M)) :
    IsIso (secondPretraceExchangeMap Λ Y N) := by
  cases hMN
  exact h

/-- The native integral ambient triangle, assembled independently of restriction. -/
private theorem integral_second_ambient_triangle
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (family : Family l Y)
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y))
    (ε : (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine
      Y ↘ Y)).obj
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj K)) ⟶ K)
    (_hε : CounitComponentNormalized (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦
      spIntegralTwist X l E)
      (family.integral E) K ε)
    (hx : IsIso (integralSecondTraceExchange l E Y))
    (ht : integralSecondTraceExchange l E Y ≫
      (secondDiagramPushIso (Profinite.padicIntegersRingObj l E.val) Y
        (fun X ↦ spIntegralTwist X l E) (family.integral E)).inv.app
          (traceTate l E (diagonalSurface Y)) ≫
      (family.integral E).trace₂ ≫
      (singleUnitIso (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
        (ProjectiveLine Y ↘ Y)).map
          (trace (Profinite.padicIntegersRingObj l E.val) Y
            (fun X ↦ spIntegralTwist X l E) (family.integral E) ≫
              (singleUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom) ≫
        (secondTraceUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom) :
    let Λ := Profinite.padicIntegersRingObj l E.val
    let L := fun X ↦ spIntegralTwist X l E
    let d := family.integral E
    let G := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
      twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
    let M := G.obj K
    ∀ hb hp, unitComponent Λ Y L d
      (integralShiftedLinePullIso l E (secondProjection Y)) M hb hp ≫ G.map ε = 𝟙 M := by
  intro Λ L d G M hb hp
  have hi := integralKernel_second_insertion l E Y family K
  have htr := integralKernel_second_trace_reordering l E Y family K ε _hε hx ht
  exact ambient_second_unit Λ Y L d
    (integralShiftedLinePullIso l E (secondProjection Y)) M
    (G.map ε) (integralSecondForwardProjection l E Y K) hi htr hb hp

/-- The normalized integral unit and counit obey the ambient second triangle.
The proof combines insertion, trace reordering, integration, and naturality. -/
private theorem integral_second_restricted_triangle
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
    (family : Family ℓ Y) (_href : IntegralFamilyReference ℓ Y family)
    (a : IntegralUnitCounitType ℓ E Y hq hr)
    (_hnorm : IntegralUnitCounitNormalized ℓ E Y hq hr family a) : ∀ K,
      (a.1.app ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K) ≫
        (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).map (a.2.app K)).hom ≫
        ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).app K.obj).hom =
      ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).app K.obj).hom := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have htrace := integral_reference_second_scalar_trace_cached ℓ E k Y family _href
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let L := fun X ↦ spIntegralTwist X ℓ E
  let d := family.integral E
  let lineIso := integralShiftedLinePullIso ℓ E (secondProjection Y)
  let F := pullTwistShift ℓ E (ProjectiveLine Y ↘ Y) 1
  let e := integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)
  let P := IntegralCompactSupport.localizing Λ Y
  let Q := IntegralCompactSupport.localizing Λ (ProjectiveLine Y)
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let G := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
    twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
  have hG : ∀ Z, P Z → Q (G.obj Z) := by
    intro Z hZ
    exact localizing_iso Λ (ProjectiveLine Y) (e.app Z) (hq Z hZ)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  have hT : Q T :=
    line_localizing_of_preservation Λ (ProjectiveLine Y ↘ Y) (L (ProjectiveLine Y)) hG
  let MT : Q.FullSubcategory := ⟨_, hT⟩
  have hbT := (_hnorm.1 MT).choose
  have hb' : IsIso ((condensedAmbientExchange Λ (square Y)).app MT.obj) := by
    convert (config := { closePre := false, closePost := false }) hbT using 0
    model_congr
  have hx₀ := secondPretraceExchangeMap_isIso Λ Y MT.obj hb'
  have hx := secondExchange_isIso_transport Λ Y MT.obj T rfl hx₀
  have hx' : IsIso (integralSecondTraceExchange ℓ E Y) := by
    unfold integralSecondTraceExchange
    refine IsIso.comp_isIso' ?_ ?_
    · convert (config := { closePre := false, closePost := false }) hx using 0
      model_congr
    · infer_instance
  intro K
  let M : Q.FullSubcategory := ⟨G.obj K.obj, hG K.obj K.property⟩
  have hu : ∃ b p, HEq ((a.1.app M).hom ≫ e.hom.app (R.obj M.obj))
      (unitComponent Λ Y L d lineIso (G.obj K.obj) b p) := by
    convert (config := { closePre := false, closePost := false }) (_hnorm.1 M) using 0
    model_congr
  obtain ⟨b, p, hη⟩ := hu
  have he : ∃ w, HEq (a.2.app K).hom
      (R.map (e.hom.app K.obj) ≫ counitComponent Λ Y L d K.obj w) := by
    convert (config := { closePre := false, closePost := false }) (_hnorm.2 K) using 0
    model_congr
  obtain ⟨w, hε⟩ := he
  let ε := model_argument% (integral_second_ambient_triangle ℓ E Y family K.obj
    (counitComponent Λ Y L d K.obj w))
  have htε := integral_second_ambient_triangle ℓ E Y family K.obj ε
    (by
      refine ⟨w, ?_⟩
      model_congr)
    (by
      convert (config := { closePre := false, closePost := false }) hx' using 0
      model_congr)
    (by
      convert (config := { closePre := false, closePost := false }) htrace using 0
      model_congr)
    (by
      convert (config := { closePre := false, closePost := false }) b using 0
      model_congr)
    (by
      convert (config := { closePre := false, closePost := false }) p using 0
      model_congr)
  have ht : unitComponent Λ Y L d lineIso (G.obj K.obj) b p ≫
      G.map (counitComponent Λ Y L d K.obj w) = 𝟙 (G.obj K.obj) := by
    convert (config := { closePre := false, closePost := false }) htε using 0
    model_congr
  let j : (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K ⟶ M :=
    ObjectProperty.homMk (e.hom.app K.obj)
  have hn : e.hom.app K.obj ≫ (a.1.app M).hom =
      (a.1.app ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K)).hom ≫
        F.map (R.map (e.hom.app K.obj)) := by
    simpa only [j, restrictedPull, restrictedPush, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift,
      ObjectProperty.ι_map, Functor.comp_map, Functor.comp_obj, Functor.id_map,
      Functor.id_obj, R, IntegralCompactSupport.push, moduleDerivedPushforward,
      moduleObjectDerivedPushforward] using congrArg (fun t ↦ t.hom) (a.1.naturality j)
  have hfinal := transport_second_triangle_unit F G R e K.obj
    (a.1.app ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K)).hom
    (a.1.app M).hom (a.2.app K).hom
    (unitComponent Λ Y L d lineIso (G.obj K.obj) b p)
    (counitComponent Λ Y L d K.obj w) hn
    (eq_of_heq hη) (eq_of_heq hε) ht
  simpa only [Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom, restrictedPull,
    ObjectProperty.lift, ObjectProperty.homMk_hom, Functor.comp_map,
    ObjectProperty.ι_map] using hfinal

/-- The second contraction equation after transport along the canonical ambient twist
comparison. This is the transport substep of the integral kernel calculation.
Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
(blueprint: lem-integral-kernel-second-contraction-postcomp). -/
theorem integralKernel_second_contraction_postcomp
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
    (family : Family ℓ Y) (_href : IntegralFamilyReference ℓ Y family)
    (a : IntegralUnitCounitType ℓ E Y hq hr)
    (_hnorm : IntegralUnitCounitNormalized ℓ E Y hq hr family a) :
       (∀ K,
            (a.1.app ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K) ≫
        (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).map (a.2.app K)).hom ≫
        ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).app K.obj).hom =
           (ρ_ (((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj)).inv ≫
        ((((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj) ◁
          ((RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y)).inv ≫ (family.integral E).support₂.hom ≫
            (family.integral E).R₂.R.map (family.integral E).delta ≫
            (family.integral E).trace₂ ≫
            (RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y)).hom)) ≫
        (ρ_ (((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj)).hom ≫
        ((integralAmbientTwistIso ℓ E (ProjectiveLine Y ↘ Y)).app K.obj).hom) := by
  intro K
  apply postcomp_identity
  · exact integral_second_restricted_triangle ℓ E k Y hq hr family _href a _hnorm K
  · exact diagonalIntegral _ _ _ _
      (singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y))
      _ _ _ (family.integral E).integration₂

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
