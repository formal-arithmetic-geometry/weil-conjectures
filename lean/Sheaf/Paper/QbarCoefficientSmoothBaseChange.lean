/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.AmbientCompleteCoefficientCategories
public import Sheaf.Paper.ECoefficientSmoothBaseChange
public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.Tactic.Choose
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import Sheaf.Paper.FiniteStageRationalExchangeCoherence

/-! # Smooth base change with algebraically closed ℓ-adic coefficients

Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).

The presentation specifies the finite-stage exchange and tensor comparisons.
Its descent through both ambient Karoubi layers retains the canonical arrow
and independence of the finite stage and admissible lattice.
No constructible landing of the ambient direct images is included.

## Main definitions

* `IntegralComparisons`: scalar comparisons fixed by the published tensor maps.
* `Presentation`: the completed composites and canonical compatible exchange.
* `Presentation.exchange`: descent through the ambient pair and Karoubi categories.

## Main statements

* `qbarCoefficientSmoothBaseChange`: invertibility and stage/lattice independence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme


private theorem karoubiComponentIsIso {A : Type*} [Category A]
    {B : Type*} [Category B] {F G : A ⥤ B} (alpha : F ⟶ G) (K : A)
    [IsIso (alpha.app K)] :
    IsIso (((Idempotents.functorExtension₂ A B).map alpha).app
      ((Idempotents.toKaroubi A).obj K)) := by
  let c := Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso A B
  have hn := congr_app (c.hom.naturality alpha) K
  change _ ≫ ((c.app G).hom.app K) =
    ((c.app F).hom.app K) ≫ (Idempotents.toKaroubi B).map (alpha.app K) at hn
  exact IsIso.of_isIso_fac_right hn


private theorem karoubiComponentIsIso_afterExtension
    {A B C : Type*} [Category A] [Category B] [Category C]
    (J : A ⥤ B) {F G : B ⥤ C} (alpha : F ⟶ G) (X : A)
    [IsIso (alpha.app (J.obj X))] :
    IsIso (((Idempotents.functorExtension₂ B C).map alpha).app
      (((Idempotents.functorExtension₂ A B).obj J).obj
        ((Idempotents.toKaroubi A).obj X))) := by
  let c := ((Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso A B).app J).app X
  exact (NatTrans.isIso_app_iff_of_iso
    ((Idempotents.functorExtension₂ B C).map alpha) c).mpr
    (karoubiComponentIsIso alpha (J.obj X))


private theorem componentIsIso_of_heq {A : Type*} [Category A]
    {B : Type*} [Category B] {F G F' G' : A ⥤ B}
    (alpha : F ⟶ G) (beta : F' ⟶ G') (hF : F = F') (hG : G = G')
    (h : HEq alpha beta) (K : A) (hi : IsIso (beta.app K)) : IsIso (alpha.app K) := by
  subst F'
  subst G'
  cases h
  exact hi


private theorem cancelMappedInverse
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} (i : X ≅ Y) {Z W : B} (p : Z ⟶ F.obj X)
    (q : Z ⟶ W) (r : W ⟶ F.obj Y) (h : HEq p (q ≫ r ≫ F.map i.inv)) :
    p ≫ F.map i.hom = q ≫ r := by
  rw [eq_of_heq h]
  simp only [Category.assoc, ← F.map_comp, i.inv_hom_id, F.map_id, Category.comp_id]

private theorem stageExchangeOnNestedInput
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    (S : StageSystem C) (T : StageSystem D)
    (F G : StageSystem.Morphism S T) (alpha : StageSystem.Morphism.Hom F G)
    {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) (H : B ⥤ S.PairCategory) (X : A) (Q : S.PairCategory)
    (heq : H.obj (J.obj X) = Q) (h : IsIso ((alpha.τ Q.stage).app Q.obj)) :
    IsIso ((Functor.whiskerLeft
      ((J ⋙ Idempotents.toKaroubi _) ⋙ (Idempotents.functorExtension₂ _ _).obj H)
      ((Idempotents.functorExtension₂ _ _).map
        (StageSystem.Morphism.descNatTrans alpha))).app X) := by
  have hpair := StageSystem.Morphism.isIso_descNatTrans_app alpha Q h
  have hQ := karoubiComponentIsIso (StageSystem.Morphism.descNatTrans alpha) Q
  let c := ((Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app H).app
    (J.obj X)
  apply (NatTrans.isIso_app_iff_of_iso
    ((Idempotents.functorExtension₂ _ _).map (StageSystem.Morphism.descNatTrans alpha)) c).mpr
  cases heq
  exact hQ

private theorem stageExchangeOnRawRepresentative
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A C D : I → Type*} [catA : ∀ i, Category (A i)] [catC : ∀ i, Category (C i)]
    [catD : ∀ i, Category (D i)]
    (S : StageSystem A) (SA : StageSystem (fun i ↦ Idempotents.Karoubi (A i)))
    (SC : StageSystem (fun i ↦ Idempotents.Karoubi (C i)))
    (SD : StageSystem (fun i ↦ Idempotents.Karoubi (D i)))
    (J : S.PairCategory ⥤ SA.PairCategory) (H : SA.PairCategory ⥤ SC.PairCategory)
    (incl : ∀ i, A i ⥤ C i) (F G : SC.Morphism SD)
    (alpha : StageSystem.Morphism.Hom F G)
    (rawF rawG : ∀ i, C i ⥤ D i) (eta : ∀ i, rawF i ⟶ rawG i)
    (hF : ∀ i, F.Φ i = (Idempotents.functorExtension₂ (C i) (D i)).obj (rawF i))
    (hG : ∀ i, G.Φ i = (Idempotents.functorExtension₂ (C i) (D i)).obj (rawG i))
    (ha : ∀ i, HEq (alpha.τ i)
      ((Idempotents.functorExtension₂ (C i) (D i)).map (eta i)))
    (hobj : ∀ (i : I) (X : A i), H.obj (J.obj ⟨i, X⟩) =
      (⟨i, ((Idempotents.functorExtension₂ (A i) (C i)).obj (incl i)).obj
        ((Idempotents.toKaroubi (A i)).obj X)⟩ : SC.PairCategory))
    (i : I) (X : A i) (K : S.PairCategory)
    (t : (⟨i, X⟩ : S.PairCategory) ≅ K) (hraw : IsIso ((eta i).app ((incl i).obj X))) :
    IsIso ((Functor.whiskerLeft
      ((J ⋙ Idempotents.toKaroubi _) ⋙ (Idempotents.functorExtension₂ _ _).obj H)
      ((Idempotents.functorExtension₂ _ _).map
        (StageSystem.Morphism.descNatTrans alpha))).app K) := by
  have := hraw
  apply (NatTrans.isIso_app_iff_of_iso _ t).mp
  refine stageExchangeOnNestedInput SC SD F G alpha J H ⟨i, X⟩
    ⟨i, ((Idempotents.functorExtension₂ (A i) (C i)).obj (incl i)).obj
      ((Idempotents.toKaroubi (A i)).obj X)⟩ (hobj i X) ?_
  refine componentIsIso_of_heq (alpha.τ i)
    ((Idempotents.functorExtension₂ (C i) (D i)).map (eta i))
    (hF i) (hG i) (ha i) _ ?_
  exact karoubiComponentIsIso_afterExtension (incl i) (eta i) X


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descendedComponentAtStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C D : I → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    (S : StageSystem C) (T : StageSystem D)
    (F G : StageSystem.Morphism S T) (alpha : StageSystem.Morphism.Hom F G)
    (Q : S.PairCategory) (M : I) (a : Q.stage ≤ M) :
    (StageSystem.Morphism.descNatTrans alpha).app Q =
      StageSystem.PairCategory.mkHom (X := F.functor.obj Q) (Y := G.functor.obj Q) M a a
        ((F.β a).hom.app Q.obj ≫
          (alpha.τ M).app ((S.T a).obj Q.obj) ≫ (G.β a).inv.app Q.obj) := by
  rw [StageSystem.Morphism.descNatTrans_app, StageSystem.ι_map_eq (S := T) a]
  congr 1
  have hc := congrArg (fun z ↦ z ≫ (G.β a).inv.app Q.obj) (alpha.comm a Q.obj)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Functor.comp_obj, StageSystem.PairCategory.toStage] using hc


private theorem normalizeStageComparisons
    {I : Type*} [Preorder I] {C D : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (D i)]
    (S : StageSystem C) (T : StageSystem D) (F : StageSystem.Morphism S T)
    (phi : ∀ i, C i ⥤ D i) (h : ∀ i, F.Φ i = phi i) :
    ∃ b : ∀ {i j} (a : i ≤ j), phi i ⋙ T.T a ≅ S.T a ⋙ phi j,
      (∀ {i j} (a : i ≤ j) (K : C i),
        HEq ((b a).hom.app K) ((F.β a).hom.app K)) ∧
      (∀ {i j} (a : i ≤ j),
        HEq ((Idempotents.functorExtension₂ _ _).mapIso (b a))
          ((Idempotents.functorExtension₂ _ _).mapIso (F.β a))) := by
  rcases F with ⟨psi, b, coh⟩
  dsimp only at h
  have hp := funext h
  subst psi
  exact ⟨b, fun _ _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩

namespace AlgebraicGeometry.Scheme

namespace QbarCoefficientSmoothBaseChange

/-- The finite-stage completed pullback/direct-image composite for the square.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothLeftStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g))

/-- The finite-stage direct-image/pullback composite for the square.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothRightStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h))

/-- The canonical finite-stage smooth exchange transformation.
Source: blueprint master, sec-smooth-base-change/sk-rem-rest, order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
abbrev smoothExchangeStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) :
  smoothLeftStage l Ω E sq ⟶ smoothRightStage l Ω E sq :=
  (Idempotents.functorExtension₂ _ _).map
    (WeilConjectures.sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)


end QbarCoefficientSmoothBaseChange

open WeilConjectures

namespace QbarCoefficientSmoothBaseChange

section Models
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U V : Scheme.{u}} (q : U ⟶ V)

/-- The right-adjoint comparison is the mate of the normalized ordinary tensor comparison.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def pushModel :
    sbcAmbientPush l E q ≅ pbcActualDerivedPush q (pbcIntegralDatum l E) :=
  conjugateIsoEquiv
    (proEtaleRingDerivedAdjunction q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q))
    (pbcActualDerivedAdjunction q (pbcIntegralDatum l E)) (sbcOrdinaryDerivedIso l E q)

/-- Transport the existing strict-tower/reflector comparison through reassociation.
Its unit normalization is exactly pbcActualCompletedPullback_tower: the strict
quotient augmentation is preserved, rather than an arbitrary completion isomorphism.
Source: sketch32, lines 1191--1228 and 1291--1321; Stacks 099N
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def pullModel :
    sbcPull l E q ⋙ ObjectProperty.ι (IsPbcComplete l E U) ≅
      ObjectProperty.ι (IsPbcComplete l E V) ⋙
        pbcActualCompletedPull q (pbcIntegralDatum l E) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (IsPbcComplete l E V))
      (Functor.associator (completedReductionTower V (pbcIntegralDatum l E))
        (completedTowerPullback q (pbcIntegralDatum l E))
        (completedTowerRlim (pbcIntegralDatum l E) U)).symm ≪≫
    (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) q).exists.choose
end Models

section Scalar
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)
  {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)

private theorem levelComparison_hom (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison W d n).hom =
      @AdicCoefficients.constantComparison W (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings W d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison W d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two recorded coefficient maps have the same finite projections, hence agree.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).
Proof: both coefficient maps send a continuous quotient section to its image under
pbcFiniteFieldInclusion. The finite projections agree by quotient induction.
Uniqueness of the completed coefficient limit map gives equality; applying the
fixed derived extension construction gives this equality of tensor functors. -/
theorem tensorModel_eq (W : Scheme.{u}) :
    pbcAmbientScalarExtension l Ω W a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W := by
  apply congrArg pbcDerivedExtend
  apply (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W).unique
  · intro n
    unfold pbcCompletedScalarMap
    rw [(pbcCompletedScalarMap_exists l Ω W a).exists.choose_spec n]
    congr 1
    unfold pbcFiniteScalarMap
    rw [← cancel_epi (pbcLevelConstantComparison W (pbcStageDatum l Ω E) n).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [levelComparison_hom, levelComparison_hom]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  · exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W).exists.choose_spec

/-- Transport between the two identical finite-projection-normalized tensors.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def tensorModel (W : Scheme.{u}) := eqToIso (tensorModel_eq l Ω a W)

/-- The specified scalar mate equation for an integral direct-image comparison.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def IntegralPushNormalization (push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) U,
    HEq (push.hom.app K).hom
      ((tensorModel l Ω a V).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V).map
          ((pushModel l (pbcFiniteField.{u} l Ω E) q).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (pushModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((tensorModel l Ω a U).inv.app K.obj))

/-- The unit-normalized tensor equation for an integral completed-pullback comparison.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def IntegralPullNormalization (pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) V,
    HEq (pull.hom.app K).hom
      ((tensorModel l Ω a U).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).map
          ((pullModel l (pbcFiniteField.{u} l Ω E) q).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((tensorModel l Ω a V).inv.app K.obj) ≫
        (pullModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))

/-- The canonical integral comparisons, specified by the published scalar mate and
unit-normalized completed tensor comparison. Their underlying equations determine
both isomorphisms uniquely. This packages the construction in proof step 1.
Source: sketch32, lines 1191--1228 and 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
structure IntegralComparisons where
  push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q
  pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q
  push_eq : IntegralPushNormalization l Ω q a push
  pull_eq : IntegralPullNormalization l Ω q a pull

attribute [local irreducible] Functor.rightDerivedFunctor

private theorem integralNormalizations_of_coherence
    (pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
          pbcAmbientCompleteIntegralTransition l Ω V a ≅
        pbcAmbientCompleteIntegralTransition l Ω U a ⋙
          sbcPush l (pbcFiniteField.{u} l Ω M) q)
    (pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
          pbcAmbientCompleteIntegralTransition l Ω U a ≅
        pbcAmbientCompleteIntegralTransition l Ω V a ⋙
          sbcPull l (pbcFiniteField.{u} l Ω M) q)
    (rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
      (pbcAmbientCompleteRawSystem l Ω V))
    (rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω V)
      (pbcAmbientCompleteRawSystem l Ω U))
    (hc : FiniteStageRationalExchange.HasOperationCoherence l Ω q pPush pPull rPush rPull) :
    ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralPushNormalization l Ω q a (pPush a) ∧
        IntegralPullNormalization l Ω q a (pPull a) := by
  rcases hc with ⟨tU, tV, push, hpush, pull, hpull, hp, hq, _⟩
  have hpush' (E : Padic.FiniteCoefficientFields l Ω) :
      push E = pushModel l (pbcFiniteField.{u} l Ω E) q := by
    unfold pushModel
    exact hpush E
  have hpull' (E : Padic.FiniteCoefficientFields l Ω) :
      pull E = pullModel l (pbcFiniteField.{u} l Ω E) q := by
    unfold pullModel
    exact hpull E
  intro E M a
  constructor
  · unfold IntegralPushNormalization
    intro K
    simp only [← hpush' E, ← hpush' M]
    have htU : tensorModel l Ω a U = eqToIso (tU a) := by
      unfold tensorModel
      rfl
    have htV : tensorModel l Ω a V = eqToIso (tV a) := by
      unfold tensorModel
      rfl
    simp only [htU, htV]
    exact @hp E M a K
  · unfold IntegralPullNormalization
    intro K
    simp only [← hpull' E, ← hpull' M]
    have htU : tensorModel l Ω a U = eqToIso (tU a) := by
      unfold tensorModel
      rfl
    have htV : tensorModel l Ω a V = eqToIso (tV a) := by
      unfold tensorModel
      rfl
    simp only [htU, htV]
    exact @hq E M a K

end Scalar


section Descent
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- Normalization of the left rational comparison by the two integral comparisons.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def LeftBetaNormalization
    (cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a)
    (cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a)
    (leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (leftBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf a).pull.hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map ((cg a).push.hom.app K))

/-- Normalization of the right rational comparison by the two integral comparisons.
Source: sketch32, lines 1291--1321
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
@[irreducible] def RightBetaNormalization
    (ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a)
    (ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a)
    (rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (rightBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch a).push.hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map ((ce a).pull.hom.app K))

/-- A presentation of the specified ambient exchange and its scalar descent.
The integral comparisons are fixed by the actual scalar mate and completion units.
The raw comparison equations localize precisely their composites, also when E=M:
the published integral/raw comparisons retain the tensor unit in that case.
The stage operations and transformation are exactly their Karoubi extensions.
These are witnesses supplied by the theorem, not extra assumptions on K.
Source: sketch32, lines 1191--1228, 1291--1338 and 1439--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
structure Presentation where
  cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a
  cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a
  ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a
  ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a
  leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)
  rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)
  leftBeta_eq : LeftBetaNormalization l Ω cf cg leftBeta
  rightBeta_eq : RightBetaNormalization l Ω ch ce rightBeta
  F : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  G : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  F_eq : ∀ E, F.Φ E = smoothLeftStage l Ω E sq
  G_eq : ∀ E, G.Φ E = smoothRightStage l Ω E sq
  F_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (F.β a) ((Idempotents.functorExtension₂ _ _).mapIso (leftBeta a))
  G_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (G.β a) ((Idempotents.functorExtension₂ _ _).mapIso (rightBeta a))
  alpha : StageSystem.Morphism.Hom F G
  alpha_eq : ∀ E, HEq (alpha.τ E) (smoothExchangeStage l Ω E sq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentation_of_coherence
    (hc : FiniteStageRationalExchange.HasCoherence l Ω sq) :
    Nonempty (Presentation l Ω sq) := by
  choose fp fl frp frl gp gl grp grl hp hl hrp hrl ep el erp erl hf hg hh he
    F G hF hG _ _ _ _ _ _ nF nG _ _ kF kG hkF hkG _ _ bkF bkG _ _ ka hka using hc
  have cfNorm : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralPushNormalization l Ω f a (fp a) ∧
        IntegralPullNormalization l Ω f a (fl a) :=
    integralNormalizations_of_coherence l Ω f fp fl frp frl hf
  let cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralComparisons l Ω f a :=
    fun {E M} a ↦ ⟨fp a, fl a, (cfNorm a).1, (cfNorm a).2⟩
  have cgNorm : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralPushNormalization l Ω g a (gp a) ∧
        IntegralPullNormalization l Ω g a (gl a) :=
    integralNormalizations_of_coherence l Ω g gp gl grp grl hg
  let cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralComparisons l Ω g a :=
    fun {E M} a ↦ ⟨gp a, gl a, (cgNorm a).1, (cgNorm a).2⟩
  have chNorm : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralPushNormalization l Ω h a (hp a) ∧
        IntegralPullNormalization l Ω h a (hl a) :=
    integralNormalizations_of_coherence l Ω h hp hl hrp hrl hh
  let ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralComparisons l Ω h a :=
    fun {E M} a ↦ ⟨hp a, hl a, (chNorm a).1, (chNorm a).2⟩
  have ceNorm : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralPushNormalization l Ω e a (ep a) ∧
        IntegralPullNormalization l Ω e a (el a) :=
    integralNormalizations_of_coherence l Ω e ep el erp erl he
  let ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
      IntegralComparisons l Ω e a :=
    fun {E M} a ↦ ⟨ep a, el a, (ceNorm a).1, (ceNorm a).2⟩
  obtain ⟨betaF, betaF_app, betaF_kar⟩ := normalizeStageComparisons
    (pbcAmbientCompleteRawSystem l Ω T) (pbcAmbientCompleteRawSystem l Ω X) F _ hF
  obtain ⟨betaG, betaG_app, betaG_kar⟩ := normalizeStageComparisons
    (pbcAmbientCompleteRawSystem l Ω T) (pbcAmbientCompleteRawSystem l Ω X) G _ hG
  refine ⟨{
    cf := cf
    cg := cg
    ch := ch
    ce := ce
    leftBeta := betaF
    rightBeta := betaG
    leftBeta_eq := ?_
    rightBeta_eq := ?_
    F := kF
    G := kG
    F_eq := by
      intro E
      unfold smoothLeftStage
      exact (hkF E).trans (congrArg ((Idempotents.functorExtension₂ _ _).obj) (hF E))
    G_eq := by
      intro E
      unfold smoothRightStage
      exact (hkG E).trans (congrArg ((Idempotents.functorExtension₂ _ _).obj) (hG E))
    F_beta := fun a ↦ (bkF a).trans (betaF_kar a).symm
    G_beta := fun a ↦ (bkG a).trans (betaG_kar a).symm
    alpha := ka
    alpha_eq := by
      intro E
      unfold smoothExchangeStage smoothLeftStage smoothRightStage
      exact hka E }⟩
  · unfold LeftBetaNormalization
    intro E M a K
    refine cancelMappedInverse
      (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g))
      ((pbcAmbientCompleteIntegralComparison l Ω T a).app K) _ _ _
      ?_
    exact (betaF_app a ((pbcAmbientCompleteLocalization l Ω T E).obj K)).trans (@nF E M a K)
  · unfold RightBetaNormalization
    intro E M a K
    refine cancelMappedInverse
      (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h))
      ((pbcAmbientCompleteIntegralComparison l Ω T a).app K) _ _ _
      ?_
    exact (betaG_app a ((pbcAmbientCompleteLocalization l Ω T E).obj K)).trans (@nG E M a K)

namespace Presentation
variable (P : Presentation l Ω sq)

/-- Extend the descended exchange to the ambient outer Karoubi envelope.
The Mathlib extension sandwiches components by both images of the outer projector.
Source: sketch32, lines 1412--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def ambientExchange :
    (Idempotents.functorExtension₂ _ _).obj P.F.functor ⟶
      (Idempotents.functorExtension₂ _ _).obj P.G.functor :=
  (Idempotents.functorExtension₂ _ _).map (StageSystem.Morphism.descNatTrans P.alpha)

/-- The exchange on the recorded raw Qbar category, using its published inclusion
through the finite-stage and outer identity projectors.
Source: sketch32, lines 1412--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def exchange :=
  Functor.whiskerLeft
    (pbcRawQbarToComplete l Ω T ⋙ pbcConstructibleCompleteQbarInclusion l Ω T)
    P.ambientExchange

/-- The representative at any finite overfield, with the canonical scalar conjugations.
This includes the identity extension and computes the component on every ambient pair.
Source: sketch32, lines 1291--1338 and 1439--1455
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch). -/
def atStage (Q : (pbcAmbientCompleteSystem l Ω T).PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (a : Q.stage ≤ M) :
    P.F.functor.obj Q ⟶ P.G.functor.obj Q :=
  StageSystem.PairCategory.mkHom M a a
    ((P.F.β a).hom.app Q.obj ≫
      (P.alpha.τ M).app (((pbcAmbientCompleteSystem l Ω T).T a).obj Q.obj) ≫
      (P.G.β a).inv.app Q.obj)


attribute [local irreducible] pbcRationalInclusion
attribute [local irreducible] sbcRationalLeft sbcRationalRight sbcRationalExchange
attribute [local irreducible] ScalarLocalization.between ScalarLocalization.betweenNat
attribute [local irreducible] sbcPush sbcPull sbcExchange

private theorem includedRepresentativeObject
    (E : Padic.FiniteCoefficientFields l Ω) (J : pbcStageCategory l Ω T E) :
    (pbcCompletePairInclusion l Ω T).obj
      ((pbcRawPairToComplete l Ω T).obj (⟨E, J⟩ : pbcQbarCategory l Ω T)) =
      (⟨E, (pbcConstructibleCompleteInclusion l Ω T E).obj
        ((Idempotents.toKaroubi _).obj J)⟩ :
        (pbcAmbientCompleteSystem l Ω T).PairCategory) := by
  unfold pbcCompletePairInclusion pbcRawPairToComplete StageSystem.coefficientPairFunctor
  exact Eq.refl
    (⟨E, (pbcConstructibleCompleteInclusion l Ω T E).obj
      ((Idempotents.toKaroubi _).obj J)⟩ :
      (pbcAmbientCompleteSystem l Ω T).PairCategory)



omit [IsNoetherian T] dT iT in
private theorem coefficientInclusionFunctorFormula
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcConstructibleCompleteInclusion l Ω T E =
      (Idempotents.functorExtension₂ (pbcStageCategory l Ω T E)
        (pbcAmbientCompleteStage l Ω T E)).obj
        (pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) T) := by
  unfold pbcConstructibleCompleteInclusion
  rfl


private theorem exchangeFormula :
    exchange l Ω sq P = Functor.whiskerLeft
      (((pbcRawPairToComplete l Ω T ⋙ Idempotents.toKaroubi _) ⋙
        (Idempotents.functorExtension₂ _ _).obj (pbcCompletePairInclusion l Ω T)))
      ((Idempotents.functorExtension₂ _ _).map
        (StageSystem.Morphism.descNatTrans P.alpha)) := by
  unfold exchange ambientExchange pbcRawQbarToComplete pbcConstructibleCompleteQbarInclusion
  rfl

end Presentation
end Descent

end QbarCoefficientSmoothBaseChange

open QbarCoefficientSmoothBaseChange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  (sq : ChosenCartesianSquare h e f g)

attribute [local irreducible] pbcRationalInclusion
attribute [local irreducible] sbcRationalLeft sbcRationalRight sbcRationalExchange
attribute [local irreducible] ScalarLocalization.between ScalarLocalization.betweenNat
attribute [local irreducible] sbcPush sbcPull sbcExchange

/-- Algebraically closed-coefficient smooth base change on admissible finite-stage inputs.
All geometric hypotheses are explicit. Invertibility at other corners is obtained
from the single hypothesis on S, through the existing prime-unit pullback theorem.
The common-stage admissibility premise spells out the source's preservation condition.
No invertibility of exchange on arbitrary ambient complexes is asserted.

Source: sketch32, lines 1439--1455; blueprint order 1446
(blueprint: sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch).
Proof:
1. The integral complete operations are additive and linear and their specified exchange
is natural (lem-sbc-completed-operations-linear-natural-exchange). Transport the canonical
scalar mate and unit-normalized pullback comparison of prop-weil-pbc-scalar-extension
through the normalized models. Localize and extend to the finite-stage Karoubi categories;
the tensor-Hom and projector formulas preserve the unit, tower and exchange equations.
2. Apply lem-sbc-coherent-pair-functor-descent to these families. On a representative u
at M its functors act by beta_source ; F_M(u) ; beta_target inverse, with the analogous
formula for G. These are exactly the specified completed composites on pair categories.
3. Scalar compatibility of the integral exchange, and then localization and Karoubi
extension, give alpha.comm. Its quotient descent is the exchange with representative
[E,alpha_E]. The outer Karoubi extension is the actual projector-sandwiched map.
4. For K at E, apply sbc-thm-e-coefficient-smooth-base-change to its admissible lattice.
Include its raw exchange and inverse by the identity finite-stage projector. Both inverse
equations remain true, without identifying the raw category with its Karoubi envelope.
5. The two classes of these arrows remain inverses in the ambient pair category, and
then under the outer identity-projector inclusion. Thus the specified component at K
is invertible in the ambient complete Qbar category. No constructible landing is used.
6. alpha.comm and the tensor tower equation identify atStage with the same component
for every overfield, including E itself. Two overfields have a finite compositum, so
the quotient equality criterion gives common-stage independence. Naturality identifies
the components on isomorphic presentations. The finite-E theorem's equality with the
canonical raw exchange makes the construction independent of each admissible lattice. -/
theorem qbarCoefficientSmoothBaseChange [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (hInvS : IsUnit (l : Γ(S, ⊤))) :
    ∃ P : Presentation
        (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
        (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
        (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
        (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq,
      (∀ (K : @pbcQbarCategory l _ Ω _ _ _ T _ dT
          ⟨sbcPrimeUnitOnSource l g hInvS⟩),
        (∃ (E : Padic.FiniteCoefficientFields l Ω)
          (J : pbcStageCategory l Ω T E)
          (L : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) J),
          L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
            (sbcPrimeUnitOnSource l g hInvS) ∧
          Nonempty ((⟨E, J⟩ : @pbcQbarCategory l _ Ω _ _ _ T _ dT
            ⟨sbcPrimeUnitOnSource l g hInvS⟩) ≅ K) ∧
          (∀ (M : Padic.FiniteCoefficientFields l Ω) (a : E ≤ M),
            ∃ LM : IntegralLattice l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS)
                (((pbcScalarSystem l Ω T dT.out (sbcPrimeUnitOnSource l g hInvS)).T a).obj
                  J),
              LM.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω M) T dT.out
                (sbcPrimeUnitOnSource l g hInvS))) →
        IsIso ((Presentation.exchange
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P).app K)) ∧
      (∀ (Q : (pbcAmbientCompleteSystem l Ω T
          (hInv := ⟨sbcPrimeUnitOnSource l g hInvS⟩)).PairCategory)
        (M : Padic.FiniteCoefficientFields l Ω) (a : Q.stage ≤ M),
        (StageSystem.Morphism.descNatTrans (Presentation.alpha
          (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
          (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
          (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
          (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) P)).app Q =
          Presentation.atStage
            (iX := ⟨sbcPrimeUnitOnSource l f hInvS⟩)
            (iS := ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩)
            (iT := ⟨sbcPrimeUnitOnSource l g hInvS⟩)
            (iY := ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩) l Ω sq P Q M a) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : PbcRationalConstructible l (pbcFiniteField.{u} l Ω E) T)
        (L L' : IntegralLattice l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) K),
        L.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        L'.IsFiniteLevelEtaleAdmissible l (pbcFiniteField.{u} l Ω E) T dT.out
          (sbcPrimeUnitOnSource l g hInvS) →
        sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L =
          sbcTransportedExchange l (pbcFiniteField.{u} l Ω E) sq dT.out
            (sbcPrimeUnitOnSource l g hInvS) L') := by
  let iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) :=
    ⟨sbcPrimeUnitOnSource l f hInvS⟩
  let iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x)) :=
    ⟨sbcPrimeUnitOnSource l (𝟙 S) hInvS⟩
  let iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x)) :=
    ⟨sbcPrimeUnitOnSource l g hInvS⟩
  let iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x)) :=
    ⟨sbcPrimeUnitOnSource l (e ≫ g) hInvS⟩
  have hc : FiniteStageRationalExchange.HasCoherence
      (iX := iX) (iS := iS) (iT := iT) (iY := iY) l Ω sq :=
    (FiniteStageRationalExchange.finiteStageRationalExchangeCoherence l Ω sq).choose_spec
      |>.choose_spec |>.choose_spec
  obtain ⟨P⟩ := presentation_of_coherence l Ω sq hc
  refine ⟨P, ?_, ?_, ?_⟩
  · intro K hK
    rcases K with ⟨EK, JK⟩
    obtain ⟨E, J, L, hL, ⟨t⟩, _⟩ := hK
    have hraw : IsIso ((sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq).app
        ((pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) T).obj J)) :=
      (eCoefficientSmoothBaseChange l (pbcFiniteField.{u} l Ω E) sq
        dX.out dT.out hInvS J L hL).1
    rw [Presentation.exchangeFormula]
    refine stageExchangeOnRawRepresentative
      (A := fun E ↦ pbcStageCategory l Ω T E)
      (C := fun E ↦ pbcAmbientCompleteStage l Ω T E)
      (D := fun E ↦ pbcAmbientCompleteStage l Ω X E)
      (catA := fun E ↦ (inferInstance : Category (pbcStageCategory l Ω T E)))
      (catC := fun E ↦ (inferInstance : Category (pbcAmbientCompleteStage l Ω T E)))
      (catD := fun E ↦ (inferInstance : Category (pbcAmbientCompleteStage l Ω X E)))
      (pbcScalarSystem l Ω T dT.out iT.out) (pbcConstructibleCompleteSystem l Ω T)
      (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
      (pbcRawPairToComplete l Ω T) (pbcCompletePairInclusion l Ω T)
      (fun E ↦ pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) T)
      P.F P.G P.alpha
      (fun E ↦ sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g))
      (fun E ↦ sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h))
      (fun E ↦ sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)
      (P.F_eq) (P.G_eq) (P.alpha_eq) ?_ E J (⟨EK, JK⟩ : pbcQbarCategory l Ω T) t hraw
    intro E J
    exact (Presentation.includedRepresentativeObject l Ω E J).trans
      (congrArg (fun H ↦ (⟨E, H.obj ((Idempotents.toKaroubi _).obj J)⟩ :
        (pbcAmbientCompleteSystem l Ω T).PairCategory))
        (Presentation.coefficientInclusionFunctorFormula (T := T) l Ω E))
  · intro Q M a
    exact descendedComponentAtStage (pbcAmbientCompleteSystem l Ω T)
      (pbcAmbientCompleteSystem l Ω X) P.F P.G P.alpha Q M a
  · intro E K L L' hL hL'
    have h := eCoefficientSmoothBaseChange l (pbcFiniteField.{u} l Ω E) sq
      dX.out dT.out hInvS K L hL
    exact (h.2.2.1 L' hL').symm

end AlgebraicGeometry.Scheme
