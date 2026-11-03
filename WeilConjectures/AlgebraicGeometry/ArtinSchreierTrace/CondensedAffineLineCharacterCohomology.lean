/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.FourierTransform.ArtinSchreierCohomology
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-! # Ordinary cohomology of a linear Artin–Schreier character

Source: latest blueprint, sec-fourier-transform/sk-lem-wft-character-integral,
lem-fd-cohomology-affine-line-character, statement and proof
(blueprint: lem-fd-cohomology-affine-line-character).

The input sheaf is the image of the specified prime-cover projector. Cohomology is
right derived global sections in the category of actual condensed coefficient modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- The global function ax on the geometric affine line. This is a specialization
of the scalar-section construction and the existing affine-space coordinate.
Source: blueprint lem-fd-cohomology-affine-line-character, the cover of ax
(blueprint: lem-fd-cohomology-affine-line-character). -/
abbrev geometricAffineLinearFunction (k K : Type u) [Field k] [Field K] [Algebra k K]
    (a : k) : Γ(AffineSpace PUnit (Spec (.of K)), ⊤) :=
  scalar K (AffineSpace PUnit (Spec (.of K))) (algebraMap k K a) *
    AffineSpace.coord (Spec (.of K)) PUnit.unit

private theorem connected_coefficient_pull_bijective
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (f : X ⟶ Spec (.of K)) :
    Function.Bijective (fun s : MonObj.Γ
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))) ↦
        MonObj.Γ.map (ProEtale.condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f)
          (MonObj.Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} f) s)) := by
  classical
  open ProEtale in
    let eS := padicAlgClSectionRingEquiv ℓ (Spec (.of K))
    let eX := padicAlgClSectionRingEquiv ℓ X
    have hcomp : Function.Bijective
        (finiteIntermediateFieldValuedComp (ℓ := ℓ) f) := by
      let x₀ : X := Classical.arbitrary X
      constructor
      · intro a b h
        apply Subtype.ext
        apply ContinuousMap.ext
        intro y
        have hy : f x₀ = y := Subsingleton.elim _ _
        have hh := congrArg (fun c : PadicAlgCl.finiteIntermediateFieldValued ℓ X ↦
          c.1 x₀) h
        simpa only [finiteIntermediateFieldValuedComp_apply, hy] using hh
      · intro a
        obtain ⟨E, hE, ha⟩ := a.property
        refine ⟨⟨ContinuousMap.const _ (a.1 x₀), E, hE, fun _ ↦ ha x₀⟩, ?_⟩
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        exact (TotallyDisconnectedSpace.eq_of_continuous a.1 a.1.continuous x x₀).symm
    have hn (a : PadicAlgCl.finiteIntermediateFieldValued ℓ (Spec (.of K))) :
        MonObj.Γ.map (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f)
          (MonObj.Γ.mapFunctor (upperStar Ab.{u + 1} f) (eS a)) =
            eX (finiteIntermediateFieldValuedComp f a) :=
      Γ_map_condensedPullbackHom_padicAlgClSectionRingHom ℓ f a
    constructor
    · intro s t h
      obtain ⟨a, rfl⟩ := eS.surjective s
      obtain ⟨b, rfl⟩ := eS.surjective t
      exact congrArg eS (hcomp.1 (eX.injective ((hn a).symm.trans (h.trans (hn b)))))
    · intro t
      obtain ⟨b, rfl⟩ := eX.surjective t
      obtain ⟨a, rfl⟩ := hcomp.2 b
      exact ⟨eS a, hn a⟩

private theorem adjunction_postcomp_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    (adj : F ⊣ G) (U A : C) (V B : D) (e₀ : F.obj U ≅ V) (α : F.obj A ⟶ B)
    (hp : Function.Bijective (fun t : U ⟶ A ↦ e₀.inv ≫ F.map t ≫ α)) :
    Function.Bijective (fun t : U ⟶ A ↦ t ≫ (adj.homEquiv _ _) α) := by
  let e : (U ⟶ G.obj B) ≃ (V ⟶ B) :=
    (adj.homEquiv _ _).symm.trans (Iso.homCongr e₀ (Iso.refl B))
  have he (t : U ⟶ A) :
      e (t ≫ (adj.homEquiv _ _) α) = e₀.inv ≫ F.map t ≫ α := by
    change e₀.inv ≫ (adj.homEquiv _ _).symm (t ≫ (adj.homEquiv _ _) α) ≫ 𝟙 B = _
    rw [Category.comp_id, Adjunction.homEquiv_naturality_left_symm,
      Equiv.symm_apply_apply]
  constructor
  · intro t s h
    exact hp.1 ((he t).symm.trans ((congrArg e h).trans (he s)))
  · intro t
    obtain ⟨s, hs⟩ := hp.2 (e t)
    exact ⟨s, e.injective ((he s).trans hs)⟩

private theorem global_pull_hom_bijective
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] (A : C) [MonObj A] (B : D) [MonObj B]
    (α : F.obj A ⟶ B) [IsMonHom α]
    (hpΓ : Function.Bijective (fun t : MonObj.Γ A ↦
      MonObj.Γ.map α (MonObj.Γ.mapFunctor F t))) :
    Function.Bijective (fun t : 𝟙_ C ⟶ A ↦
      Functor.LaxMonoidal.ε F ≫ F.map t ≫ α) := by
  have he (t : MonObj.Γ A) :
      (MonObj.Γ.map α (MonObj.Γ.mapFunctor F t)).hom =
        Functor.LaxMonoidal.ε F ≫ F.map t.hom ≫ α := by
    rw [MonObj.Γ.map_hom, MonObj.Γ.mapFunctor_hom, Category.assoc]
  constructor
  · intro t s h
    exact congrArg MonObj.Γ.hom (hpΓ.1 (MonObj.Γ.ext
      ((he (MonObj.Γ.ofHom t)).trans (h.trans (he (MonObj.Γ.ofHom s)).symm))))
  · intro t
    obtain ⟨s, hs⟩ := hpΓ.2 (MonObj.Γ.ofHom t)
    exact ⟨s.hom, (he s).symm.trans (congrArg MonObj.Γ.hom hs)⟩

private theorem monoidal_adjunction_unit_bijective
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [F.Additive]
    (adj : F ⊣ G) (A : C) [MonObj A] (B : D) [MonObj B]
    (α : F.obj A ⟶ B) [IsMonHom α]
    (hp : Function.Bijective (fun t : MonObj.Γ A ↦
      MonObj.Γ.map α (MonObj.Γ.mapFunctor F t))) :
    Function.Bijective (fun t : 𝟙_ C ⟶ A ↦ t ≫ adj.unit.app A ≫ G.map α) := by
  have h := adjunction_postcomp_bijective F G adj _ A _ B
    (Functor.Monoidal.εIso F).symm α (global_pull_hom_bijective F A B α hp)
  simpa only [Adjunction.homEquiv_unit] using h

private theorem postcomp_bijective_of_iso
    {C : Type*} [Category C] {U V A B : C} (e : U ≅ V) (g : A ⟶ B)
    (hb : Function.Bijective (fun t : U ⟶ A ↦ t ≫ g)) :
    Function.Bijective (fun t : V ⟶ A ↦ t ≫ g) := by
  constructor
  · intro s t h
    apply (cancel_epi e.hom).1
    apply hb.1
    simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) h
  · intro b
    obtain ⟨a, ha⟩ := hb.2 (e.hom ≫ b)
    refine ⟨e.inv ≫ a, ?_⟩
    change (e.inv ≫ a) ≫ g = b
    change a ≫ g = e.hom ≫ b at ha
    rw [Category.assoc, ha, ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem terminal_sections_bijective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [HasWeakSheafify J Ab.{u + 1}]
    {T : C} (hT : IsTerminal T) {A B : Sheaf J Ab.{u + 1}} (g : A ⟶ B)
    (hb : Function.Bijective (fun t :
      (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A ↦ t ≫ g)) :
    Function.Bijective (g.hom.app (Opposite.op T)) := by
  let d (N : Sheaf J Ab.{u + 1}) :
      ((constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ N) ≃
        N.obj.obj (Opposite.op T) :=
    (((constantSheafAdj J Ab.{u + 1} hT).homAddEquiv _ N).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toEquiv
  have hd (t :
      (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ A) :
      d B (t ≫ g) = g.hom.app (Opposite.op T) (d A t) := by rfl
  constructor
  · intro x y h
    obtain ⟨s, rfl⟩ := (d A).surjective x
    obtain ⟨t, rfl⟩ := (d A).surjective y
    exact congrArg (d A) (hb.1 ((d B).injective
      ((hd s).trans (h.trans (hd t).symm))))
  · intro y
    obtain ⟨t, rfl⟩ := (d B).surjective y
    obtain ⟨s, rfl⟩ := hb.2 t
    exact ⟨d A s, (hd s).symm⟩

private theorem terminal_unit_sections_bijective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {T : C} (hT : IsTerminal T) {A B : Sheaf J Ab.{u + 1}} (g : A ⟶ B)
    (hb : Function.Bijective (fun t : 𝟙_ (Sheaf J Ab.{u + 1}) ⟶ A ↦ t ≫ g)) :
    Function.Bijective (g.hom.app (Opposite.op T)) := by
  apply terminal_sections_bijective J hT g
  apply postcomp_bijective_of_iso (Functor.Monoidal.εIso (presheafToSheaf J Ab.{u + 1}))
  exact hb

private theorem coefficient_push_bijective_of_pull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hp : Function.Bijective (fun s : MonObj.Γ (ProEtale.condensedRingObj Λ Y) ↦
      MonObj.Γ.map (ProEtale.condensedPullbackHom Λ f)
        (MonObj.Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} f) s))) :
    Function.Bijective ((ProEtale.condensedPushforwardHom Λ f).hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 Y)))) := by
  have hb := monoidal_adjunction_unit_bijective
    (ProEtale.upperStar Ab.{u + 1} f) (ProEtale.lowerStar Ab.{u + 1} f)
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (ProEtale.condensedRingObj Λ Y) (ProEtale.condensedRingObj Λ X)
    (ProEtale.condensedPullbackHom Λ f) hp
  apply terminal_unit_sections_bijective (Scheme.ProEt.topology Y)
    (Scheme.ProEt.isTerminalMkId _)
  simpa only [ProEtale.condensedPushforwardHom, Adjunction.unitAlgHom] using hb

private theorem connected_coefficient_push_bijective
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (f : X ⟶ Spec (.of K)) :
    Function.Bijective
      ((ProEtale.condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) f).hom.app
        (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
  exact coefficient_push_bijective_of_pull (Profinite.padicAlgClRingObj ℓ) f
    (connected_coefficient_pull_bijective ℓ K X f)

@[irreducible] private def coefficientUnitMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.regular (ProEtale.condensedRingObj Λ Y) ⟶
      (ProEtale.CondensedRing.lowerStar Λ f).obj
        (Mod.regular (ProEtale.condensedRingObj Λ X)) :=
  Mod.Hom.mk' (ProEtale.condensedPushforwardHom Λ f) (by
    change μ[ProEtale.condensedRingObj Λ Y] ≫ ProEtale.condensedPushforwardHom Λ f =
      ProEtale.condensedRingObj Λ Y ◁ ProEtale.condensedPushforwardHom Λ f ≫
        ProEtale.condensedPushforwardHom Λ f ▷
          (ProEtale.lowerStar Ab.{u + 1} f).obj (ProEtale.condensedRingObj Λ X) ≫
            μ[(ProEtale.lowerStar Ab.{u + 1} f).obj (ProEtale.condensedRingObj Λ X)]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

private theorem coefficientUnitMap_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coefficientUnitMap Λ f).hom = ProEtale.condensedPushforwardHom Λ f := by
  unfold coefficientUnitMap
  rfl

private theorem derived_zero_evaluation_iso
    {C D A : Type*} [Category C] [Category D] [Category A]
    [Abelian C] [Abelian D] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (E : D ⥤ A) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (M : C) :
    Nonempty ((DerivedCategory.homologyFunctor A 0).obj
      (E.mapDerivedCategory.obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M))) ≅
          E.obj (F.obj M)) := by
  exact ⟨(E.mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    E.mapIso (F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.app M)⟩

private theorem derived_zero_iso_of_comparisons
    {C D A : Type*} [Category C] [Category D] [Category A]
    [Abelian C] [Abelian D] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (E : D ⥤ A) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (M : C) (N : D) (Q : A)
    (e₁ : Nonempty (E.obj N ≅ E.obj (F.obj M))) (e₂ : Nonempty (E.obj N ≅ Q)) :
    Nonempty ((DerivedCategory.homologyFunctor A 0).obj
      ((F.rightDerivedFunctor ⋙ E.mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor C 0).obj M)) ≅ Q) := by
  obtain ⟨d⟩ := derived_zero_evaluation_iso F E M
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  exact ⟨d ≪≫ e₁.symm ≪≫ e₂⟩

private theorem field_fiber_map_bijective
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    {M N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (ProEtale.padicAlgClRingObj (Spec (.of K)) ℓ)} (m : M ⟶ N)
    (hm : Function.Bijective (m.hom.hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))) :
    Function.Bijective ((ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ).map m) := by
  exact hm

private theorem lifted_module_iso (R : Type) [Field R]
    (M : ModuleCat.{u + 1} R) (c : M ≃ₗ[R] R) :
    Nonempty (M ≅ ModuleCat.of R (ULift.{u + 1} R)) := by
  let e : M ≃ₗ[R] ULift.{u + 1} R :=
    { toFun := fun x ↦ ULift.up (c x)
      invFun := fun x ↦ c.symm x.down
      left_inv := fun x ↦ c.symm_apply_apply x
      right_inv := fun x ↦ ULift.ext _ _ (c.apply_symm_apply x.down)
      map_add' := fun x y ↦ congrArg ULift.up (c.map_add x y)
      map_smul' := fun r x ↦ congrArg ULift.up (c.map_smul r x) }
  exact ⟨e.toModuleIso⟩

private theorem coefficient_unit_evaluation_iso_of_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {R : Type*} [Ring R]
    (E : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y) ⥤ ModuleCat.{u + 1} R)
    (hE : ∀ {M N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ Y)} (m : M ⟶ N),
      Function.Bijective (m.hom.hom.app (Opposite.op (Scheme.ProEt.mk (𝟙 Y)))) →
        Function.Bijective (E.map m))
    (hb : Function.Bijective ((ProEtale.condensedPushforwardHom Λ f).hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 Y))))) :
    Nonempty (E.obj (Mod.regular (ProEtale.condensedRingObj Λ Y)) ≅
      E.obj ((ProEtale.CondensedRing.lowerStar Λ f).obj
        (Mod.regular (ProEtale.condensedRingObj Λ X)))) := by
  have hm : Function.Bijective (E.map (coefficientUnitMap Λ f)) := by
    apply hE
    rw [coefficientUnitMap_hom]
    exact hb
  exact ⟨(LinearEquiv.ofBijective (E.map (coefficientUnitMap Λ f)).hom hm).toModuleIso⟩

private theorem field_unit_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (a : X ⟶ Spec (.of K)) :
    Nonempty ((ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj
      (Mod.regular (ProEtale.padicAlgClRingObj (Spec (.of K)) ℓ)) ≅
      (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj
        ((ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a).obj
          (Mod.regular (ProEtale.padicAlgClRingObj X ℓ)))) := by
  apply coefficient_unit_evaluation_iso_of_bijective (Profinite.padicAlgClRingObj ℓ) a
    (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ)
  · intro M N m hm
    exact field_fiber_map_bijective ℓ K m hm
  · exact connected_coefficient_push_bijective ℓ K X a

private theorem field_regular_module_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K] :
    Nonempty ((ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj
      (Mod.regular (ProEtale.padicAlgClRingObj (Spec (.of K)) ℓ)) ≅
        ModuleCat.of (PadicAlgCl ℓ) (ULift.{u + 1} (PadicAlgCl ℓ))) := by
  exact lifted_module_iso (PadicAlgCl ℓ) _
    (ProEtale.CondensedQbarGeometricEvaluation.fieldRegularCoordinates K ℓ)

private theorem ordinary_sections_eq_composite
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) :
    WeilConjectures.condensedQbarOrdinarySections ℓ K a =
      (ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a).rightDerivedFunctor ⋙
        (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ).mapDerivedCategory := rfl

private theorem connected_unit_zero_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (a : X ⟶ Spec (.of K)) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ℓ)) 0).obj
      ((WeilConjectures.condensedQbarOrdinarySections ℓ K a).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (ProEtale.padicAlgClRingObj X ℓ)))) ≅
      ModuleCat.of (PadicAlgCl ℓ) (ULift.{u + 1} (PadicAlgCl ℓ))) := by
  let F := ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a
  let E := ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ
  let M := Mod.regular (ProEtale.padicAlgClRingObj X ℓ)
  let N := Mod.regular (ProEtale.padicAlgClRingObj (Spec (.of K)) ℓ)
  let Q := ModuleCat.of (PadicAlgCl ℓ) (ULift.{u + 1} (PadicAlgCl ℓ))
  have h := derived_zero_iso_of_comparisons F E M N Q
    (field_unit_iso ℓ K X a) (field_regular_module_iso ℓ K)
  have he := ordinary_sections_eq_composite ℓ K a
  change WeilConjectures.condensedQbarOrdinarySections ℓ K a =
    F.rightDerivedFunctor ⋙ E.mapDerivedCategory at he
  have hc := congrArg (fun G ↦ G.obj ((DerivedCategory.singleFunctor _ 0).obj M)) he
  exact (congrArg (fun Z ↦ Nonempty
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ℓ)) 0).obj Z ≅ Q))
      hc).mpr h

end AlgebraicGeometry.ArtinSchreierTrace
