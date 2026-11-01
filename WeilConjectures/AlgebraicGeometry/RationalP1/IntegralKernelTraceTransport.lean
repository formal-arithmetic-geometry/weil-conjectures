/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstSectionKernelComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeNormalizedSelfSquareProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveProjectionNaturalityRight
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ProjectionScalarEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1TensorShiftNaturality

/-! # Trace transport with arbitrary condensed coefficients -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] projectionModuleAbelian projectionModuleHasDerived
  projectionModuleCategory projectionCoefficientMonObj projectionSheafMonoidal
  projectionModuleMonoidal
attribute [local instance 20001] CategoryTheory.traceSheafSymmetric
attribute [local instance 30000] internalMonoidal
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] projectionMap projectionMateMap tensorShiftIso twist

private theorem kernel_scalar_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (K : DerivedCategory (Modules Λ Y))
    (t : K ⟶ 𝟙_ (DerivedCategory (Modules Λ Y))) :
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M K ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((M ◁ ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map t ≫
          (secondTraceUnitIso Λ Y).hom)) ≫ (ρ_ M).hom) =
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M ◁ t) ≫
        (ρ_ ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)).hom := by
  have h := normalized_projection_evaluation Λ Y
    (projectionMate_existsUnique Λ).exists.choose
    (projectionMate_existsUnique Λ).exists.choose_spec
    (secondTraceUnitIso Λ Y) (native_unit_comparison Λ Y) M K t
  unfold projectionMateMap internalMonoidal internalTensorBundle nativeTensorBundle
    projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact h

private theorem kernel_push_map_id
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (A : DerivedCategory (Modules Λ X)) :
    (moduleObjectDerivedPushforward Λ g).map (𝟙 A) =
      𝟙 ((moduleObjectDerivedPushforward Λ g).obj A) := by
  have h := (moduleObjectDerivedPushforward Λ g).map_id A
  unfold projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact h

private theorem kernel_twist_map_id
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X)
    (A : DerivedCategory (Modules Λ X)) :
    (twist Λ X L).map (𝟙 A) = 𝟙 ((twist Λ X L).obj A) := by
  have h := (twist Λ X L).map_id A
  unfold projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact h

-- Coefficient naturality with the fixed native category caches.

private theorem kernel_projection_naturality_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    (K : DerivedCategory (Modules Λ S))
    {N N' : DerivedCategory (Modules Λ X)} (n : N ⟶ N') :
    (K ◁ (moduleObjectDerivedPushforward Λ g).map n) ≫ projectionMap Λ g K N' =
      projectionMap Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (((moduleObjectDerivedPullback Λ g).obj K) ◁ n) := by
  have h := projectionMap_naturality_right Λ g K n
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
    projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact h

private theorem kernel_path_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    {V W : DerivedCategory (Modules Λ (diagonalSurface Y))} (w : V ⟶ W) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map w) ≫
        (firstPathComparison Λ Y).hom.app W =
      (firstPathComparison Λ Y).hom.app V ≫
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
          ((moduleObjectDerivedPushforward Λ (firstProjection Y)).map w) := by
  have h := (firstPathComparison Λ Y).hom.naturality w
  simp only [Functor.comp_map] at h
  unfold projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact h

private theorem kernel_push_map_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (g : X ⟶ S)
    {A B C : DerivedCategory (Modules Λ X)} (f : A ⟶ B) (h : B ⟶ C) :
    (moduleObjectDerivedPushforward Λ g).map (f ≫ h) =
      (moduleObjectDerivedPushforward Λ g).map f ≫
        (moduleObjectDerivedPushforward Λ g).map h := by
  have hc := (moduleObjectDerivedPushforward Λ g).map_comp f h
  unfold projectionModuleCategory projectionModuleAbelian projectionModuleHasDerived at *
  exact hc

-- Evaluate an inverse tail from its forward evaluation, using only cancellation.

private theorem kernel_inverse_terminal_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X B : Scheme.{u}} (g : X ⟶ B)
    {S V : DerivedCategory (Modules Λ B)}
    {A C D : DerivedCategory (Modules Λ X)}
    (q : S ⟶ (moduleObjectDerivedPushforward Λ g).obj A) [IsIso q]
    (j : A ⟶ C) [IsIso j] (h : C ⟶ D) (s : D ⟶ A)
    (t : (moduleObjectDerivedPushforward Λ g).obj C ⟶ V) (w : S ⟶ V)
    (hc : j ≫ h ≫ s = 𝟙 A)
    (ht : q ≫ (moduleObjectDerivedPushforward Λ g).map j ≫ t = w) :
    (moduleObjectDerivedPushforward Λ g).map h ≫
      (moduleObjectDerivedPushforward Λ g).map s ≫ inv q ≫ w = t := by
  apply (cancel_epi ((moduleObjectDerivedPushforward Λ g).map j)).1
  apply (cancel_epi q).1
  rw [ht]
  rw [← reassoc_of% (kernel_push_map_comp Λ g j h),
    ← reassoc_of% (kernel_push_map_comp Λ g (j ≫ h) s), hc,
    kernel_push_map_id, Category.id_comp, IsIso.hom_inv_id_assoc]

private theorem kernel_projection_extension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (x : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T) ⟶
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj T))
    (he : firstTraceExchange Λ Y T N e = x ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e.hom) :
    ((M ◁ x) ≫ projectionMap Λ (firstProjection Y) M
      ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj T)) ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom) =
      (M ◁ firstTraceExchange Λ Y T N e) ≫ projectionMap Λ (firstProjection Y) M N := by
  let P := moduleObjectDerivedPushforward Λ (firstProjection Y)
  let A := moduleObjectDerivedPullback Λ (firstProjection Y)
  let B := moduleObjectDerivedPullback Λ (secondProjection Y)
  have hproj := kernel_projection_naturality_right Λ (firstProjection Y) M e.hom
  have hcoef : (M ◁ x) ≫ (M ◁ P.map e.hom) =
      M ◁ firstTraceExchange Λ Y T N e := by
    as_aux_lemma =>
      have hc := (whiskerLeft_comp M x (P.map e.hom)).symm.trans
        (congrArg (fun z ↦ M ◁ z) he.symm)
      coefficient_finish hc
  calc
    _ = (M ◁ x) ≫ (projectionMap Λ (firstProjection Y) M (B.obj T) ≫
        P.map (A.obj M ◁ e.hom)) := Category.assoc _ _ _
    _ = (M ◁ x) ≫ ((M ◁ P.map e.hom) ≫
        projectionMap Λ (firstProjection Y) M N) :=
      congrArg (fun z ↦ (M ◁ x) ≫ z) hproj.symm
    _ = ((M ◁ x) ≫ (M ◁ P.map e.hom)) ≫
        projectionMap Λ (firstProjection Y) M N := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z ↦ z ≫ projectionMap Λ (firstProjection Y) M N) hcoef

private theorem kernel_path_extension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (b : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let P := moduleObjectDerivedPushforward Λ (firstProjection Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let B := moduleObjectDerivedPullback Λ (secondProjection Y)
    let Q := projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T
    Q ≫ R.map ((b ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
        U.map (A.obj M ◁ e.hom)) ≫
        (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) =
      (Q ≫ R.map ((b ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
        (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T)) ≫
        R.map (P.map (A.obj M ◁ e.hom)) := by
  have hpath := kernel_path_naturality Λ Y
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom)
  simp only [kernel_push_map_comp, Category.assoc]
  rw [hpath]

private theorem kernel_native_paste
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (b : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))
    (x : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T) ⟶
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj T))
    (he : firstTraceExchange Λ Y T N e = x ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map e.hom)
    (hk :
      let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
      let A := moduleObjectDerivedPullback Λ (firstProjection Y)
      let B := moduleObjectDerivedPullback Λ (secondProjection Y)
      projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
        R.map ((b ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T) ≫
        (firstPathComparison Λ Y).hom.app (A.obj M ⊗ B.obj T) =
      projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
        R.map ((M ◁ x) ≫ projectionMap Λ (firstProjection Y) M (B.obj T))) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
      R.map ((b ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
        U.map (A.obj M ◁ e.hom)) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ firstTraceExchange Λ Y T N e) ≫
        projectionMap Λ (firstProjection Y) M N) := by
  dsimp only at hk ⊢
  have hleft := kernel_path_extension Λ Y M T N e b
  have hright := kernel_projection_extension Λ Y M T N e x he
  calc
    _ = ((projectionMap Λ (ProjectiveLine Y ↘ Y) ((moduleObjectDerivedPushforward Λ (ProjectiveLine
      Y ↘ Y)).obj M) T) ≫ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map ((b ▷ T) ≫
      projectionMateMap Λ (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection
      Y)).obj M) T) ≫
        (firstPathComparison Λ Y).hom.app ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M
          ⊗ (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T)) ≫
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
          ((moduleObjectDerivedPushforward Λ (firstProjection Y)).map ((moduleObjectDerivedPullback
          Λ (firstProjection Y)).obj M ◁ e.hom)) := hleft
    _ = (projectionMateMap Λ (ProjectiveLine Y ↘ Y) M ((moduleObjectDerivedPushforward Λ
      (ProjectiveLine Y ↘ Y)).obj T) ≫
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map ((M ◁ x) ≫ projectionMap Λ
          (firstProjection Y) M ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj T))) ≫
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
          ((moduleObjectDerivedPushforward Λ (firstProjection Y)).map ((moduleObjectDerivedPullback
          Λ (firstProjection Y)).obj M ◁ e.hom)) :=
      congrArg (fun z ↦ z ≫ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((moduleObjectDerivedPushforward Λ (firstProjection Y)).map ((moduleObjectDerivedPullback Λ
        (firstProjection Y)).obj M ◁ e.hom))) hk
    _ = _ := by
      rw [Category.assoc, ← kernel_push_map_comp Λ (ProjectiveLine Y ↘ Y)]
      exact congrArg
        (fun z ↦ projectionMateMap Λ (ProjectiveLine Y ↘ Y) M ((moduleObjectDerivedPushforward Λ
          (ProjectiveLine Y ↘ Y)).obj T) ≫ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘
          Y)).map z) hright

private theorem kernel_coefficient_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (hk :
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
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let b := (nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
      (firstProjection Y) (secondProjection Y) (square Y)).app M
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫
      R.map ((b ▷ T) ≫ projectionMateMap Λ (secondProjection Y) (A.obj M) T ≫
        U.map (A.obj M ◁ e.hom)) ≫
      (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
      R.map ((M ◁ firstTraceExchange Λ Y T N e) ≫
        projectionMap Λ (firstProjection Y) M N) := by
  let x : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
    ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T) ⟶
    (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj ((moduleObjectDerivedPullback Λ
    (secondProjection Y)).obj T) := by
    unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
    exact (mateEquiv
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
      (TwoSquare.mk _ _ _ _
        (condensedAmbientPullbackComparison Λ (square Y)).inv)).natTrans.app T
  have hK : (projectionMap Λ (ProjectiveLine Y ↘ Y) ((moduleObjectDerivedPushforward Λ
    (ProjectiveLine Y ↘ Y)).obj M) T) ≫ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘
    Y)).map ((((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) ▷ T) ≫
      projectionMateMap Λ (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection
        Y)).obj M) T) ≫
      (firstPathComparison Λ Y).hom.app
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ (moduleObjectDerivedPullback Λ
          (secondProjection Y)).obj T) =
    projectionMateMap Λ (ProjectiveLine Y ↘ Y) M ((moduleObjectDerivedPushforward Λ (ProjectiveLine
      Y ↘ Y)).obj T) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map ((M ◁ x) ≫ projectionMap Λ
        (firstProjection Y) M
        ((moduleObjectDerivedPullback Λ (secondProjection Y)).obj T)) := by
    have h := hk
    coefficient_finish h
  have he : firstTraceExchange Λ Y T N e = x ≫ (moduleObjectDerivedPushforward Λ (firstProjection
    Y)).map e.hom := by
    as_aux_lemma =>
      unfold firstTraceExchange x
      coefficient_congr
  exact kernel_native_paste Λ Y M T N e ((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y)
    (firstProjection Y) (secondProjection Y) (square Y)).app M) x he hK

private theorem kernel_terminal_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (f : (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N ⟶
      unit Λ (ProjectiveLine Y))
    (t : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T ⟶
      𝟙_ (DerivedCategory (Modules Λ Y)))
    (h₁ : IsIso (projectionMap Λ (firstProjection Y) M N))
    (ht : firstTraceExchange Λ Y T N e ≫ f ≫
        (singleUnitIso Λ (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map t ≫
        (secondTraceUnitIso Λ Y).hom)
    (J : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⊗ T ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N))
    (hK :
      let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
      let A := moduleObjectDerivedPullback Λ (firstProjection Y)
      projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫ R.map J ≫
          (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) =
        projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
          R.map ((M ◁ firstTraceExchange Λ Y T N e) ≫
            projectionMap Λ (firstProjection Y) M N)) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫ R.map J ≫
        (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) ≫
        R.map (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) h₁ ≫
          (M ◁ f) ≫ (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom) =
      (R.obj M ◁ t) ≫ (ρ_ (R.obj M)).hom := by
  let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let W := @inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) h₁ ≫
    (M ◁ f) ≫ (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom
  have hW : ((M ◁ firstTraceExchange Λ Y T N e) ≫
      projectionMap Λ (firstProjection Y) M N) ≫ W =
      (M ◁ (F.map t ≫ (secondTraceUnitIso Λ Y).hom)) ≫ (ρ_ M).hom := by
    dsimp only [W]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, ht]
  have h := congrArg (fun z ↦ z ≫ R.map W) hK
  simp only [Category.assoc] at h
  rw [← R.map_comp, hW] at h
  have hscalar := kernel_scalar_evaluation Λ Y M (R.obj T) t
  have heval := h.trans hscalar
  simpa only [W, Category.assoc] using heval

private theorem kernel_native_terminal_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N)
    (f : d.R₁.R.obj N ⟶
      unit Λ (ProjectiveLine Y))
    (t : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T ⟶
      𝟙_ (DerivedCategory (Modules Λ Y)))
    (h₁ : IsIso (projectionMap Λ (firstProjection Y) M N))
    (ht : firstTraceExchange Λ Y T N e ≫ firstNativeFunctional Λ Y L d N f ≫
        (singleUnitIso Λ (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map t ≫
        (secondTraceUnitIso Λ Y).hom)
    (J : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⊗ T ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N))
    (hK :
      let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
      let A := moduleObjectDerivedPullback Λ (firstProjection Y)
      projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫ R.map J ≫
          (firstPathComparison Λ Y).hom.app (A.obj M ⊗ N) =
        projectionMateMap Λ (ProjectiveLine Y ↘ Y) M (R.obj T) ≫
          R.map ((M ◁ firstTraceExchange Λ Y T N e) ≫
            projectionMap Λ (firstProjection Y) M N)) :
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    projectionMap Λ (ProjectiveLine Y ↘ Y) (R.obj M) T ≫ R.map J ≫
        firstTerminalFunctional Λ Y L d M N f h₁ =
      (R.obj M ◁ t) ≫ (ρ_ (R.obj M)).hom := by
  have h := kernel_terminal_evaluation Λ Y M T N e
    (firstNativeFunctional Λ Y L d N f) t h₁ ht J hK
  simp only [firstTerminalFunctional]
  coefficient_finish h

/-- Trace-functional transport conditional on the two Kunneth paths, with no section
insertion or diagonal class. Source: the first projective-line triangle
(blueprint: lem-integral-kernel-trace-transport).
Proof: expand the twisted second projection and apply tensorShiftIso naturality.
Use hk at the shifted line, then naturality of firstPathComparison and the first
projection in its coefficient to insert e. Postcompose with the first functional.
The scalar trace hypothesis changes this to the q functional; the normalized
projection evaluation removes its right coefficient. Cancel the invertible q,
second, exchange and first maps, and reinsert the tensor-shift isomorphisms and the
normalized counit. No integration identity is used in this intermediate step. -/
theorem kernel_first_trace_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (v : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
    (hv : CounitComponentNormalized Λ Y L d
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) v)
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
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
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let U := moduleObjectDerivedPushforward Λ (secondProjection Y)
    let A := moduleObjectDerivedPullback Λ (firstProjection Y)
    let N := ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧
    R.map (U.map (X := A.obj M ⊗ N)
        (tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) (A.obj M)).hom ≫
      @inv _ _ _ _ (twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e (A.obj M)) hp ≫
      (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
        (by
          dsimp only [R, U, A]
          unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
          exact @inv _ _ _ _ ((condensedAmbientExchange Λ (square Y)).app M) hb)) ≫ v =
      firstTerminalFunctional Λ Y L d M N d.trace₁ h₁ := by
  have hb_eq : ((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) = secondPretraceExchangeMap Λ Y M := by
    as_aux_lemma =>
      unfold nativeSelfSquareExchange secondPretraceExchangeMap
      rfl
  have : IsIso ((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) := by
    rw [hb_eq]
    exact secondPretraceExchangeMap_isIso Λ Y M hb
  have := hp
  have := h₁
  obtain ⟨hq, hv⟩ := hv
  have := hq
  have hv' := eq_of_heq hv
  subst v
  have hJ : ((((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) ▷ (((DerivedCategory.singleFunctor (Modules Λ
    (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ
    (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y)))
    ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom)) = (tensorShiftIso Λ
    (ProjectiveLine Y) (L (ProjectiveLine Y))
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj ((moduleObjectDerivedPushforward Λ
        (ProjectiveLine Y ↘ Y)).obj M))).hom ≫
      (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map ((nativeSelfSquareExchange Λ
        (ProjectiveLine Y ↘ Y) (firstProjection Y) (secondProjection Y) (square Y)).app M) ≫
      twistProjectionMap Λ (secondProjection Y)
        (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e ((moduleObjectDerivedPullback Λ
          (firstProjection Y)).obj M) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map (tensorShiftIso Λ (diagonalSurface
        Y) (L (diagonalSurface Y))
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).inv := by
    as_aux_lemma =>
      rw [← reassoc_of% (tensorShiftIso_naturality Λ (ProjectiveLine Y)
        (L (ProjectiveLine Y)) ((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection
          Y) (secondProjection Y) (square Y)).app M))]
      simp only [tensorHom_id, twistProjectionMap, Category.assoc,
        Iso.hom_inv_id_assoc, Functor.map_comp]
      simp only [← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
  have : IsIso ((((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) ▷ (((DerivedCategory.singleFunctor (Modules Λ
    (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ
    (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y)))
    ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom)) := by
    rw [hJ]
    infer_instance
  have hK := kernel_coefficient_naturality Λ Y M (((DerivedCategory.singleFunctor (Modules Λ
    (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) (((DerivedCategory.singleFunctor
    (Modules Λ (diagonalSurface Y)) 0).obj (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) e (hk
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y)))
    ⟦(2 : ℤ)⟧))
  have hterminal : (projectionMap Λ (ProjectiveLine Y ↘ Y) ((moduleObjectDerivedPushforward Λ
    (ProjectiveLine Y ↘ Y)).obj M) (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y))
    0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y
    ↘ Y)).map ((((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) ▷ (((DerivedCategory.singleFunctor (Modules Λ
    (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ
    (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y)))
    ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom)) ≫ firstTerminalFunctional Λ
    Y L d M (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj (L
    (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁ h₁ =
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M ◁ (trace Λ Y L d ≫
        (singleUnitIso Λ Y).hom)) ≫
        (ρ_ ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)).hom := by
    have h := kernel_native_terminal_evaluation Λ Y L d M (((DerivedCategory.singleFunctor
      (Modules Λ
      (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) (((DerivedCategory.singleFunctor
      (Modules Λ (diagonalSurface Y)) 0).obj (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) e
      d.trace₁
      (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) h₁ ht ((((nativeSelfSquareExchange Λ (ProjectiveLine
        Y ↘ Y) (firstProjection Y) (secondProjection Y) (square Y)).app M) ▷
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine
        Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ (secondProjection Y) ((moduleObjectDerivedPullback Λ
        (firstProjection Y)).obj M) (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y))
        0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ
        (secondProjection Y)).map ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
        e.hom)) hK
    coefficient_finish h
  have hbi : (kernelAmbientInverse% Λ Y M hb) = inv ((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘
    Y) (firstProjection Y) (secondProjection Y) (square Y)).app M) := by
    as_aux_lemma =>
      symm
      apply IsIso.inv_eq_of_hom_inv_id
      dsimp only [nativeSelfSquareExchange]
      unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
      have h := @IsIso.hom_inv_id _ _ _ _
        ((condensedAmbientExchange Λ (square Y)).app M) hb
      coefficient_finish h
  have hJH : ((((nativeSelfSquareExchange Λ (ProjectiveLine Y ↘ Y) (firstProjection Y)
    (secondProjection Y) (square Y)).app M) ▷ (((DerivedCategory.singleFunctor (Modules Λ
    (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ
    (secondProjection Y) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine Y)))
    ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁ e.hom)) ≫
    ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map (tensorShiftIso Λ (diagonalSurface
    Y) (L (diagonalSurface Y)) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).hom ≫
    inv (twistProjectionMap Λ (secondProjection Y) (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ≫ (twist Λ (ProjectiveLine Y) (L
    (ProjectiveLine Y))).map (kernelAmbientInverse% Λ Y M hb)) ≫
      (tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj ((moduleObjectDerivedPushforward
          Λ (ProjectiveLine Y ↘ Y)).obj M))).inv = 𝟙 _ := by
    as_aux_lemma =>
      rw [hJ]
      rw [hbi]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        kernel_push_map_id, kernel_twist_map_id, Category.id_comp,
        IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Iso.hom_inv_id]
  have hgoal : (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
    ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map (tensorShiftIso Λ (diagonalSurface
    Y) (L (diagonalSurface Y)) ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).hom ≫
    inv (twistProjectionMap Λ (secondProjection Y) (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ≫ (twist Λ (ProjectiveLine Y) (L
    (ProjectiveLine Y))).map (kernelAmbientInverse% Λ Y M hb)) ≫ counitComponent Λ Y L d
    ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) hq =
      firstTerminalFunctional Λ Y L d M (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface
        Y)) 0).obj (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁ h₁ := by
    dsimp only [counitComponent]
    rw [← whiskerLeft_comp_assoc]
    have hf := kernel_inverse_terminal_evaluation Λ (ProjectiveLine Y ↘ Y)
      (S := (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M ⊗
        (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
            (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
      (V := (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)
      (A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⊗
          (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
            (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
      (C := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      (D := (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)))
      (projectionMap Λ (ProjectiveLine Y ↘ Y) ((moduleObjectDerivedPushforward Λ
      (ProjectiveLine Y ↘ Y)).obj M) (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine
      Y)) 0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ((((nativeSelfSquareExchange Λ
      (ProjectiveLine Y ↘ Y) (firstProjection Y) (secondProjection Y) (square Y)).app M) ▷
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj (L (ProjectiveLine
      Y))) ⟦(2 : ℤ)⟧)) ≫ projectionMateMap Λ (secondProjection Y) ((moduleObjectDerivedPullback Λ
      (firstProjection Y)).obj M) (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y))
      0).obj (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫ (moduleObjectDerivedPushforward Λ
      (secondProjection Y)).map ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
      e.hom)) ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map (tensorShiftIso Λ
      (diagonalSurface Y) (L (diagonalSurface Y)) ((moduleObjectDerivedPullback Λ (firstProjection
      Y)).obj M)).hom ≫ inv (twistProjectionMap Λ (secondProjection Y) (L (ProjectiveLine Y)) (L
      (diagonalSurface Y)) e ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ≫ (twist
      Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map (kernelAmbientInverse% Λ Y M hb))
      (tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y))
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M))).inv
      (firstTerminalFunctional Λ Y L d M (((DerivedCategory.singleFunctor (Modules Λ
        (diagonalSurface Y)) 0).obj (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁ h₁)
      (((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M ◁ (trace Λ Y L d ≫
        (singleUnitIso Λ Y).hom)) ≫
        (ρ_ ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)).hom)
      (by coefficient_finish hJH) (by coefficient_finish hterminal)
    coefficient_finish hf
  coefficient_finish hgoal

end AlgebraicGeometry.ProEtale.RationalP1
