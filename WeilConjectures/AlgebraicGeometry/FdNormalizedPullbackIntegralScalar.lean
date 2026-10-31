/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FdCoefficientComparisonSystem
public import WeilConjectures.AlgebraicGeometry.FdPullbackAugmentationCounitMatching
import WeilConjectures.AlgebraicGeometry.FdScalarRoosComparisonIntertwining
import WeilConjectures.AlgebraicGeometry.FdPullbackRoosMatchingUniqueness
import WeilConjectures.AlgebraicGeometry.FdCoefficientScalarCompletionIdentification

/-! # Integral scalar coherence for fixed normalized pullback components

Source: trace-definition auxiliary whole-tower argument, as recorded in the parent
comparison node; Stacks 0941 and 099N
(blueprint: lem-fd-normalized-pullback-integral-scalar). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

private theorem scalar_levelConstant_hom (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  let := d.quotientFinite
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b


private theorem scalar_coefficientMap (T : Scheme.{u})
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T := by
  have hq (n : ℕ) : pbcQuotientInclusion.{u} l Ω h n =
      pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) n := by
    rfl
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n =
      AdicCoefficients.coefficientMap T
        (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) n) := by
    dsimp only [pbcFiniteScalarMap]
    rw [hq]
    apply (Iso.inv_comp_eq (pbcLevelConstantComparison T (pbcStageDatum l Ω E) n)).mpr
    rw [scalar_levelConstant_hom, scalar_levelConstant_hom]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    rw [hf]
    exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n


private theorem conjugated_inverse_square
    {J : Type*} [Category J] {A B C D E F G H : J}
    (b : B ≅ A) (c : C ≅ B) (u : C ≅ D) (v : E ≅ F)
    (t : G ≅ F) (a : H ≅ A) (ct : G ≅ H) (f : D ⟶ E)
    (h : f ≫ v.hom ≫ t.inv = u.inv ≫ c.hom ≫ b.hom ≫ a.inv ≫ ct.inv) :
    b.inv ≫ c.inv ≫ u.hom ≫ f = a.inv ≫ ct.inv ≫ t.hom ≫ v.inv := by
  have hh := congrArg (fun z ↦ b.inv ≫ c.inv ≫ u.hom ≫ z ≫ t.hom ≫ v.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using hh

private theorem transport_scalar_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (S S' : A ⥤ B) (T T' : C ⥤ D) (hs : S = S') (ht : T = T')
    (G : C ⥤ A) (F : D ⥤ B) (alpha : T' ⋙ F ≅ G ⋙ S')
    (X : C) (Y : A) (Z W : B) (V : D) (b : G.obj X ⟶ Y)
    (s : S.obj Y ⟶ Z) (s' : S'.obj Y ⟶ Z) (hu : HEq s s')
    (f : Z ⟶ W) (t : T.obj X ⟶ V) (t' : T'.obj X ⟶ V) (hv : HEq t t')
    (d : F.obj V ⟶ W)
    (h : S'.map b ≫ s' ≫ f = alpha.inv.app X ≫ F.map t' ≫ d) :
    ∃ a : T ⋙ F ≅ G ⋙ S, HEq a.hom alpha.hom ∧
      HEq (S.map b ≫ s ≫ f) (a.inv.app X ≫ F.map t ≫ d) := by
  subst S'
  subst T'
  refine ⟨alpha, HEq.rfl, ?_⟩
  apply heq_of_eq
  simpa only [eq_of_heq hu, eq_of_heq hv] using h

/-- The completion-conjugated scalar square holds for the selected finite
components whenever their Roos matching uses the same realization system.
Source: trace-definition whole-tower argument, steps 8--10; Stacks 0941 and 099N
(blueprint: lem-fd-normalized-pullback-integral-scalar).

Proof: choose the common strict-tower models at E and L. Their ambient maps and
the inverses of the selected finite ambient maps have the same composite with
the quotient augmentation: both give the actual PBC completion unit. Naturality
and invertibility of the framework augmentation on complete inputs identify
these maps. fdScalarPullbackRealizationIdentification identifies the ordinary
scalar/tower map with the actual PBC scalar comparison, keeping both completion
units. fdScalarRoosIntegralIntertwining gives the equality before completion and
its conjugate by chi. Substitute the two ambient identifications. The chi field
of each coefficient datum identifies its scalar comparison with precisely the
quotient/zero-coordinate completion map on good representatives. Naturality and
localization extend this identification to every constructible object. Cancel
the adjacent chi and inverse chi factors, and invert b to obtain the displayed
inverse-b equation. The alpha witness is pbcScalarCompletedPullIso transported
along the canonical coefficient-presentation equalities; its hom is HEq to
that actual map. These transports account for the HEq in the equation.
No quotient transition is inverted; equality of fields and ramified extensions
use the same whole-tower argument. Zero objects and identity scheme maps give
the corresponding naturality equations. -/
theorem fdNormalizedPullbackIntegralScalar (R : IntegralComparisonSystem.{u} l)
    (C : ∀ (T : Scheme.{u}) [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))],
      FdCoefficientComparison l Ω T)
    (P : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
      [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
      (h : U ≅ T), FdPullbackSystem l Ω (C U) (C T) h)
    (_matching : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
      [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
      (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
      FdPullbackRoosMatching l Ω (C U) (C T) h E R ((P h).finite E)) :
    ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
    ∃ alpha : pbcAmbientScalarExtension l Ω T e ⋙
        pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L) ≅
      pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω U e,
    HEq alpha.hom
      (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom).hom ∧
    HEq
      ((pbcAmbientScalarExtension l Ω U e).map
          (((P h).finite E).ambient.hom.app K) ≫
        ((C U).integral_scalar e).hom.app
          ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom).obj K) ≫
        (integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).map
          (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom K).hom.hom)
      (alpha.inv.app
          ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj) ≫
        (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L)).map
          (((C T).integral_scalar e).hom.app K) ≫
        ((P h).finite L).ambient.hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T).obj K)) := by
  intro U T _ _ _ _ _ _ h E L e K
  obtain ⟨bE⟩ := fdPullbackCommonStrictTowerModels l (pbcFiniteField.{u} l Ω E)
    Fact.out Fact.out Fact.out Fact.out h
  obtain ⟨bL⟩ := fdPullbackCommonStrictTowerModels l (pbcFiniteField.{u} l Ω L)
    Fact.out Fact.out Fact.out Fact.out h
  obtain ⟨cU, cT, _⟩ := fdScalarPullbackRealizationIdentification l Ω E L e R h
  obtain ⟨hC, hS, hF, hord, hcomp⟩ := fdScalarRoosIntegralIntertwining l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω e) h cU cT bE bL K
  have hbE := fdPullbackRoosMatching_uniqueness l Ω (C U) (C T) h E R
    ((P h).finite E) (_matching h E) bE K
  have hbL := fdPullbackRoosMatching_uniqueness l Ω (C U) (C T) h L R
    ((P h).finite L) (_matching h L) bL
    ((sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T).obj K)
  have hsU := fdCoefficientScalar_completionIdentification l Ω U (C U) e cU
    ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom).obj K)
  have hsT := fdCoefficientScalar_completionIdentification l Ω T (C T) e cT K
  let alpha := pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom
  have hsq : (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) U).map
        (((P h).finite E).ambient.hom.app K) ≫
      (cU.derivedIso.inv.app ((integralDerivedPullback l
          (pbcFiniteField.{u} l Ω E) h.hom).obj K.obj) ≫
        (integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).map
          (scalarCompletionIso l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) U _ hF).hom) ≫
      (integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).map
        (integralPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) h.hom K).hom.hom =
    alpha.inv.app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj) ≫
      (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L)).map
        (cT.derivedIso.inv.app K.obj ≫
          (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
            (scalarCompletionIso l (pbcFiniteField.{u} l Ω E)
              (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T
              K.obj K.property.1).hom) ≫
      ((P h).finite L).ambient.hom.app
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T).obj K) := by
    rw [hbE, hbL]
    let chiU := (integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).mapIso
      (scalarCompletionIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) U _ hF)
    let chiT := (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L)).mapIso
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).mapIso
        (scalarCompletionIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T
          K.obj K.property.1))
    let b := (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) U).mapIso
        (bE.actual_ambient.app K)
    let c := cU.derivedIso.app
      ((integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom).obj K.obj)
    let ct := (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω L)).mapIso
      (cT.derivedIso.app K.obj)
    have hc := conjugated_inverse_square b c chiU
      (bL.actual_ambient.app ⟨_, hS⟩) chiT
      (alpha.app ((integralDetailedTransport T l
        (pbcFiniteField.{u} l Ω E)).obj K.obj)) ct
      ((integralDetailedTransport U l (pbcFiniteField.{u} l Ω L)).map
        (scalarPullbackCompleted l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e)
          h.hom K.obj K.property.1 hF).hom) hcomp
    simpa only [b, c, ct, chiU, chiT, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, integralPullbackScalarComparison,
      constructibleIntegralPullback, sfConstructibleIntegralScalarExtension,
      ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj,
      ObjectProperty.lift, pbcStageDatum, ObjectProperty.isoMk,
      ObjectProperty.homMk_hom, Category.assoc] using hc
  exact transport_scalar_square _ _ _ _
    (congrArg pbcDerivedExtend (scalar_coefficientMap l Ω U e))
    (congrArg pbcDerivedExtend (scalar_coefficientMap l Ω T e))
    _ _ alpha _ _ _ _ _ _ _ _ hsU _ _ _ hsT _ hsq

end WeilConjectures
