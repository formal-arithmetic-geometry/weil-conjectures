/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixNormalizedImmersion
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement

/-! # Normalized scalar comparison for locally closed immersions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 20000 in
-- This formal calculation should not unfold the concrete localization model.
private theorem scalarSixSupportedMap_ext
    {A B : Type*} [Category A] [Category B] (E : A ⥤ B) [E.Full]
    (R : B ⥤ A) (rho : E ⋙ R ≅ 𝟭 A) {M N : A} {Z : B}
    (e : Z ≅ E.obj M) (f g : Z ⟶ E.obj N) (h : R.map f = R.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  let f' := E.preimage (e.inv ≫ f)
  let g' := E.preimage (e.inv ≫ g)
  have hh : R.map (E.map f') = R.map (E.map g') := by
    simp only [f', g', E.map_preimage, Functor.map_comp, h]
  have hn := rho.hom.naturality f'
  have hm := rho.hom.naturality g'
  simp only [Functor.comp_map, Functor.id_map] at hn hm
  have hfg : f' = g' := by
    apply (cancel_epi (rho.hom.app M)).mp
    exact hn.symm.trans ((congrArg (fun z ↦ z ≫ rho.hom.app N) hh).trans hm)
  simpa only [f', g', E.map_preimage] using congrArg E.map hfg

private theorem scalarSixInverseTowerSquare
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R₀ : B₀ ⥤ A₀) (R₁ : B₁ ⥤ A₁) (R₂ : B₂ ⥤ A₂)
    (S₀₁ : A₀ ⥤ A₁) (S₁₂ : A₁ ⥤ A₂) (S₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (q₀₁ : R₀ ⋙ S₀₁ ≅ T₀₁ ⋙ R₁) (q₁₂ : R₁ ⋙ S₁₂ ≅ T₁₂ ⋙ R₂)
    (q₀₂ : R₀ ⋙ S₀₂ ≅ T₀₂ ⋙ R₂)
    (tA : S₀₁ ⋙ S₁₂ ≅ S₀₂) (tB : T₀₁ ⋙ T₁₂ ≅ T₀₂) (K : B₀)
    (h : tA.hom.app (R₀.obj K) ≫ q₀₂.hom.app K =
      S₁₂.map (q₀₁.hom.app K) ≫ q₁₂.hom.app (T₀₁.obj K) ≫
        R₂.map (tB.hom.app K)) :
    R₂.map (tB.hom.app K) ≫ q₀₂.inv.app K =
      q₁₂.inv.app (T₀₁.obj K) ≫ S₁₂.map (q₀₁.inv.app K) ≫
        tA.hom.app (R₀.obj K) := by
  have hh := congrArg (fun z ↦ q₁₂.inv.app (T₀₁.obj K) ≫
    S₁₂.map (q₀₁.inv.app K) ≫ z ≫ q₀₂.inv.app K) h
  simp only [Category.assoc, Iso.hom_inv_id_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at hh
  rw [S₁₂.map_id ((T₀₁ ⋙ R₁).obj K)] at hh
  simp only [Functor.comp_obj, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Category.comp_id] at hh
  exact hh.symm

set_option maxHeartbeats 20000 in
-- This formal calculation should not unfold the concrete localization model.
private theorem scalarSixNormalizedTower
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (E₂ : A₂ ⥤ B₂) [E₂.Full]
    (R₀ : B₀ ⥤ A₀) (R₁ : B₁ ⥤ A₁) (R₂ : B₂ ⥤ A₂)
    (rho₀ : E₀ ⋙ R₀ ≅ 𝟭 A₀) (rho₁ : E₁ ⋙ R₁ ≅ 𝟭 A₁)
    (rho₂ : E₂ ⋙ R₂ ≅ 𝟭 A₂)
    (S₀₁ : A₀ ⥤ A₁) (S₁₂ : A₁ ⥤ A₂) (S₀₂ : A₀ ⥤ A₂)
    (T₀₁ : B₀ ⥤ B₁) (T₁₂ : B₁ ⥤ B₂) (T₀₂ : B₀ ⥤ B₂)
    (q₀₁ : R₀ ⋙ S₀₁ ≅ T₀₁ ⋙ R₁) (q₁₂ : R₁ ⋙ S₁₂ ≅ T₁₂ ⋙ R₂)
    (q₀₂ : R₀ ⋙ S₀₂ ≅ T₀₂ ⋙ R₂)
    (d₀₁ : E₀ ⋙ T₀₁ ≅ S₀₁ ⋙ E₁) (d₁₂ : E₁ ⋙ T₁₂ ≅ S₁₂ ⋙ E₂)
    (d₀₂ : E₀ ⋙ T₀₂ ≅ S₀₂ ⋙ E₂)
    (tA : S₀₁ ⋙ S₁₂ ≅ S₀₂) (tB : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (n₀₁ : ∀ M, R₁.map (d₀₁.hom.app M) ≫ rho₁.hom.app (S₀₁.obj M) =
      q₀₁.inv.app (E₀.obj M) ≫ S₀₁.map (rho₀.hom.app M))
    (n₁₂ : ∀ M, R₂.map (d₁₂.hom.app M) ≫ rho₂.hom.app (S₁₂.obj M) =
      q₁₂.inv.app (E₁.obj M) ≫ S₁₂.map (rho₁.hom.app M))
    (n₀₂ : ∀ M, R₂.map (d₀₂.hom.app M) ≫ rho₂.hom.app (S₀₂.obj M) =
      q₀₂.inv.app (E₀.obj M) ≫ S₀₂.map (rho₀.hom.app M))
    (hq : ∀ K, tA.hom.app (R₀.obj K) ≫ q₀₂.hom.app K =
      S₁₂.map (q₀₁.hom.app K) ≫ q₁₂.hom.app (T₀₁.obj K) ≫ R₂.map (tB.hom.app K))
    (M : A₀) :
    tB.hom.app (E₀.obj M) ≫ d₀₂.hom.app M =
      T₁₂.map (d₀₁.hom.app M) ≫ d₁₂.hom.app (S₀₁.obj M) ≫
        E₂.map (tA.hom.app M) := by
  have hqi (K : B₀) := scalarSixInverseTowerSquare R₀ R₁ R₂
    S₀₁ S₁₂ S₀₂ T₀₁ T₁₂ T₀₂ q₀₁ q₁₂ q₀₂ tA tB K (hq K)
  let e : T₁₂.obj (T₀₁.obj (E₀.obj M)) ≅ E₂.obj (S₀₂.obj M) :=
    tB.app (E₀.obj M) ≪≫ d₀₂.app M
  apply scalarSixSupportedMap_ext E₂ R₂ rho₂ (N := S₀₂.obj M) e
  apply (cancel_mono (rho₂.hom.app (S₀₂.obj M))).mp
  have hrho := rho₂.hom.naturality (tA.hom.app M)
  have hnat := q₁₂.inv.naturality (d₀₁.hom.app M)
  have ht := tA.hom.naturality (rho₀.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hrho hnat ht
  simp only [Functor.map_comp, Category.assoc]
  rw [n₀₂ M, hrho, reassoc_of% n₁₂ (S₀₁.obj M),
    reassoc_of% hnat]
  rw [← S₁₂.map_comp_assoc, n₀₁ M, S₁₂.map_comp, Category.assoc,
    ht, reassoc_of% hqi (E₀.obj M)]

/-- Conjugate a comparison through the fixed presentations of its two extensions. -/
private def scalarSixConjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E F : A ⥤ B} {E' F' : C ⥤ D} (e : E ≅ F) (e' : E' ≅ F')
    (S : A ⥤ C) (T : B ⥤ D) (beta : E ⋙ T ≅ S ⋙ E') : F ⋙ T ≅ S ⋙ F' :=
  Functor.isoWhiskerRight e.symm T ≪≫ beta ≪≫ Functor.isoWhiskerLeft S e'

private theorem scalarSixConjugate_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E F : A ⥤ B} {E' F' : C ⥤ D} (e : E ≅ F) (e' : E' ≅ F')
    (S : A ⥤ C) (T : B ⥤ D) (beta : E ⋙ T ≅ S ⋙ E') (M : A) :
    T.map (e.hom.app M) ≫ (scalarSixConjugate e e' S T beta).hom.app M =
      beta.hom.app M ≫ e'.hom.app (S.obj M) := by
  simp only [scalarSixConjugate, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom]
  exact Iso.map_hom_inv_id_assoc (e.app M) T _

private theorem scalarSixDerivedEquivalence_full
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.Full :=
  e.mapDerivedCategory.fullyFaithfulFunctor.full

private theorem scalarSixDerivedEquivalence_inverse_full
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    e.inverse.mapDerivedCategory.Full :=
  e.mapDerivedCategory.symm.fullyFaithfulFunctor.full

private theorem scalarSixForward_full (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (scalarSixForward Λ X).Full := by
  have : (ModuleRingedComparison.equivalence Λ.X X).functor.Additive :=
    ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).1
  have : (ModuleRingedComparison.equivalence Λ.X X).inverse.Additive :=
    ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).2.1
  unfold scalarSixForward
  exact scalarSixDerivedEquivalence_full (ModuleRingedComparison.equivalence Λ.X X)

private theorem scalarSixBackward_full (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (scalarSixBackward Λ X).Full := by
  have : (ModuleRingedComparison.equivalence Λ.X X).functor.Additive :=
    ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).1
  have : (ModuleRingedComparison.equivalence Λ.X X).inverse.Additive :=
    ((InternalModuleOperations.internal_module_operations_transport Λ.X).1 X).2.1
  unfold scalarSixBackward
  exact scalarSixDerivedEquivalence_inverse_full (ModuleRingedComparison.equivalence Λ.X X)

attribute [local irreducible] scalarSixChange scalarSixPull scalarSixTower
  scalarSixExtension scalarSixRestriction
  scalarSixImmersion
  scalarSixOpenIso scalarSixClosedIso scalarSixExtensionComp scalarSixPullSection
  Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars


set_option maxHeartbeats 65000 in
-- Bound elaboration while keeping the localization construction folded.
/-- Normalized scalar comparison for the published locally closed extension.

Source: blueprint det-prop-scalar-six-pullback.proof.md, (2), and the extension square
in (3); Stacks, Modules on Sites, Tags 03DI and 03DJ; Pro-etale Cohomology, Tags 09BM
and 09AH. (blueprint: lem-sfb-scalar-six-immersion-comparison).

Proof: take the normalized single-arrow immersion comparison, its geometric compositor,
and its specified open value from `scalarSixNormalizedImmersion_exists`. Conjugating its
closed specialization with the published `scalarSixClosedIso` constructs the required
closed witness. The closed equation is functoriality followed by cancellation of an
isomorphism and its inverse.

The fixed ordinary module equivalence and its inverse are additive. Their derived
functors are therefore full, and the published derived extension is full by D.full.
Thus `scalarSixExtension` is full. An extension E with invertible restriction
rho : E followed by R isomorphic to the identity has injective R.map on morphisms
between extension images: lift both morphisms by fullness and use naturality of rho.
The same holds when the source is merely isomorphic to an extension image.

Apply this detection to the two sides of the beta tower equation. Restrict them and
postcompose with rho. The three normalization equations, naturality of rho and theta,
and the inverse form of C.tower identify the restricted paths. Cancellation and
supported detection give exactly the asserted beta tower equation. Together with the
retained single-arrow data this supplies every clause of `ScalarSixExtensionData`. -/
theorem scalarSixExtensionData_exists
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    (k : Type u) [Field k] (O : ScalarSixOpenComparison E G k) :
    ScalarSixExtensionData E D G C k O := by
  obtain ⟨B⟩ := scalarSixNormalizedImmersion_exists E hE D G C k O
  refine ⟨{ normalized := B
            closed := fun {_ _} a {_ _} _ _ _ _ _ _ i _ ↦
              scalarSixConjugate (scalarSixClosedIso E G _ i) (scalarSixClosedIso E G _ i)
                (scalarSixChange a _) (scalarSixChange a _) (B.beta a i)
            closedNormalization := ?_
            tower := ?_ }⟩
  · intro Λ Λ' a S X _ _ _ _ _ _ i _ M
    exact scalarSixConjugate_normalization (scalarSixClosedIso E G Λ i)
      (scalarSixClosedIso E G Λ' i) (scalarSixChange a S.left)
      (scalarSixChange a X.left) (B.beta a i) M
  · intro Λ Λ' Λ'' a b S X _ _ _ _ _ _ f _ M
    have hD := D.full (scalarSixImmersion G Λ'' f)
    have hF := scalarSixForward_full Λ'' S.left
    have hB := scalarSixBackward_full Λ'' X.left
    have : (scalarSixExtension E G Λ'' f).Full := by
      unfold scalarSixExtension
      exact @Functor.Full.comp _ _ _ _ _ _ _ _ hF
        (@Functor.Full.comp _ _ _ _ _ _ _ _ hD hB)
    apply scalarSixNormalizedTower
      (scalarSixExtension E G Λ f) (scalarSixExtension E G Λ' f)
      (scalarSixExtension E G Λ'' f)
      (scalarSixPull Λ f.left) (scalarSixPull Λ' f.left) (scalarSixPull Λ'' f.left)
      (scalarSixRestriction E D G Λ f) (scalarSixRestriction E D G Λ' f)
      (scalarSixRestriction E D G Λ'' f)
      (scalarSixChange a S.left) (scalarSixChange b S.left)
      (scalarSixChange (a ≫ b) S.left)
      (scalarSixChange a X.left) (scalarSixChange b X.left)
      (scalarSixChange (a ≫ b) X.left)
      (C.theta a f.left) (C.theta b f.left) (C.theta (a ≫ b) f.left)
      (B.beta a f) (B.beta b f) (B.beta (a ≫ b) f)
      (scalarSixTower a b S.left) (scalarSixTower a b X.left)
      (B.normalization a f) (B.normalization b f) (B.normalization (a ≫ b) f) ?_ M
    exact fun K ↦ C.tower a b f.left K


end AlgebraicGeometry.ProEtale.CondensedRing
