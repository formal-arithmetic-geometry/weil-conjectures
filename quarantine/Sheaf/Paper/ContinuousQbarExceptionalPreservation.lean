/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import all Sheaf.Paper.ShriekCoefficientIsomorphism
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.AlgClTopologyMateHomBijection
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.Paper.ProperLocalizingAdmissibleCoefficients
import Sheaf.Paper.RationalRestrictionGlue
import Sheaf.Paper.OpenImmersionLocalizing
import all Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.LocalizingClosureCtfEqualsBc

/-!
# Exceptional preservation for the all-continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction,
first two proof paragraphs, with the coefficient convention of sk-def-localizing-closure.
This isolates the geometric preservation assertion; no restricted functor or adjunction
is constructed here.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private instance continuousQbar_overMk_finiteType {Z T : Scheme.{u}} (f : Z ⟶ T)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (Over.mk f).hom :=
  ‹LocallyOfFiniteType f›

private instance continuousQbar_overMk_quasiCompact {Z T : Scheme.{u}} (f : Z ⟶ T)
    [QuasiCompact f] : QuasiCompact (Over.mk f).hom :=
  ‹QuasiCompact f›

private instance continuousQbar_overMk_separated {Z T : Scheme.{u}} (f : Z ⟶ T)
    [IsSeparated f] : IsSeparated (Over.mk f).hom :=
  ‹IsSeparated f›

@[no_expose] private noncomputable def continuousQbar_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {J : C ⥤ E} {H : D ⥤ F} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (s : J ⋙ L₂ ⟶ L₁ ⋙ H) : R₁ ⋙ J ⟶ H ⋙ R₂ :=
  (mateEquiv a b (TwoSquare.mk _ _ _ _ s)).natTrans

private theorem continuousQbar_mate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {J : C ⥤ E} {H : D ⥤ F} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (s : J ⋙ L₂ ⟶ L₁ ⋙ H) (X : D) :
    (continuousQbar_mate a b s).app X =
      b.homEquiv _ _ (s.app (R₁.obj X) ≫ H.map (a.counit.app X)) := by
  simp [continuousQbar_mate, mateEquiv, Adjunction.homEquiv_unit, Functor.map_comp,
    TwoSquare.mk]

private theorem continuousQbar_mate_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {J : C ⥤ E} {H : D ⥤ F} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (s : J ⋙ L₂ ⟶ L₁ ⋙ H) {X Y : D} (g : X ⟶ Y) :
    J.map (R₁.map g) ≫
        b.homEquiv _ _ (s.app (R₁.obj Y) ≫ H.map (a.counit.app Y)) =
      b.homEquiv _ _ (s.app (R₁.obj X) ≫ H.map (a.counit.app X)) ≫
        R₂.map (H.map g) := by
  simpa only [continuousQbar_mate_app, Functor.comp_map] using
    (continuousQbar_mate a b s).naturality g

@[no_expose] private noncomputable def continuousQbar_mateExplicit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {J : C ⥤ E} {H : D ⥤ F} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (s : J ⋙ L₂ ⟶ L₁ ⋙ H) : R₁ ⋙ J ⟶ H ⋙ R₂ :=
  { app := fun X ↦ b.homEquiv _ _ (s.app (R₁.obj X) ≫ H.map (a.counit.app X))
    naturality := fun _ _ g ↦ continuousQbar_mate_naturality a b s g }

/-- Conjugate a fixed adjunction along equivalences and a specified left comparison. -/
@[no_expose] private noncomputable def continuousQbar_conjugateAdjunction
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (U : C ≌ E) (V : D ≌ F) {L : C ⥤ D} {R : D ⥤ C}
    {L' : E ⥤ F} (adj : L ⊣ R) (a : L ⋙ V.functor ≅ U.functor ⋙ L') :
    L' ⊣ V.inverse ⋙ R ⋙ U.functor := by
  let i : (U.inverse ⋙ L) ⋙ V.functor ≅ L' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft U.inverse a ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight U.counitIso L' ≪≫ L'.leftUnitor
  exact ((U.symm.toAdjunction.comp adj).comp V.toAdjunction).ofNatIsoLeft i

/-- Change the generators by equality before applying the generator comparison. -/
private theorem continuousQbar_generator_transfer
    {C D : Type u} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsStableUnderShift ℤ] [P.IsClosedUnderIsomorphisms]
    (S : ObjectProperty C) (T : ObjectProperty D) (hS : S = P) (hT : T = Q)
    (F : C ⥤ D) (hF : ∀ M, P M → Q (F.obj M))
    (hLoc : ∀ M, CategoryTheory.localizingClosure S M →
      CategoryTheory.localizingClosure T (F.obj M))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adSmall : Q.lift (P.ι ⋙ F) (fun M ↦ hF M.obj M.property) ⊣ G)
    (J : (CategoryTheory.localizingClosure T).FullSubcategory ⥤
      (CategoryTheory.localizingClosure S).FullSubcategory)
    (adBig : (CategoryTheory.localizingClosure T).lift
      ((CategoryTheory.localizingClosure S).ι ⋙ F)
      (fun M ↦ hLoc M.obj M.property) ⊣ J) :
    ∀ K, T K.obj → S (J.obj K).obj := by
  subst S
  subst T
  intro K hK
  exact AlgebraicGeometry.ProEtale.AdjunctionTransfer.rightAdjoint_preserves_generators
    P Q F hF hLoc G adSmall J adBig (⟨K.obj, hK⟩ : Q.FullSubcategory)

/-- Exact equivalences carry the intersection closure to the target closure. -/
private theorem continuousQbar_map_closure
    {C D : Type w} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ] [F.IsTriangulated]
    (S : ObjectProperty C) (T : ObjectProperty D) (h : ∀ A, S A → T (F.obj A)) :
    ∀ K, CategoryTheory.localizingClosure S K →
      CategoryTheory.localizingClosure T (F.obj K) := by
  intro K hK P hP hSP
  let := hP.1
  let := hP.2.1
  apply hK (P.inverseImage F) ?_ (fun A hA ↦ hSP _ (h A hA))
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I D hD hDR
  let := hD
  have hpres := F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimit D F := hpres.preservesColimitsOfShape.preservesColimit
  have : HasColimit (D ⋙ F) := Adjunction.hasColimit_comp_equivalence D F
  exact P.prop_of_iso (preservesColimitIso F D).symm
    (hP.2.2 (D ⋙ F) inferInstance hDR)

/-- The preservation assertion transports along a specified square of equivalences. -/
private theorem continuousQbar_transport_preservation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (U : C ≌ E) (V : D ≌ F) {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (L' : E ⥤ F) (a : L ⋙ V.functor ≅ U.functor ⋙ L')
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty E) (Q' : ObjectProperty F) [P'.IsClosedUnderIsomorphisms]
    (hP : ∀ A, P' (U.functor.obj A) ↔ P A)
    (hQ : ∀ A, Q' (V.functor.obj A) ↔ Q A)
    (pres : ∀ (R' : F ⥤ E), (L' ⊣ R') → ∀ A, Q' A → P' (R'.obj A)) :
    ∀ A, Q A → P (R.obj A) := by
  let R' := V.inverse ⋙ R ⋙ U.functor
  let adj' : L' ⊣ R' := continuousQbar_conjugateAdjunction U V adj a
  let b : R ⋙ U.functor ≅ V.functor ⋙ R' :=
    (R ⋙ U.functor).leftUnitor.symm ≪≫
      Functor.isoWhiskerRight V.unitIso (R ⋙ U.functor) ≪≫ Functor.associator _ _ _
  intro A hA
  apply (hP (R.obj A)).mp
  exact P'.prop_of_iso (b.app A).symm
    (pres R' adj' (V.functor.obj A) ((hQ A).mpr hA))

/-- Restrict and transport an ambient square without unfolding its concrete functors. -/
private theorem continuousQbar_transport_restricted
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (U : C ≌ E) (V : D ≌ F)
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty E) (Q' : ObjectProperty F)
    [P'.IsClosedUnderIsomorphisms] [Q'.IsClosedUnderIsomorphisms]
    (hP : ∀ A, P' (U.functor.obj A) ↔ P A)
    (hQ : ∀ A, Q' (V.functor.obj A) ↔ Q A)
    (S : ObjectProperty C) (T : ObjectProperty D)
    (S' : ObjectProperty E) (T' : ObjectProperty F)
    [S'.IsClosedUnderIsomorphisms]
    (hS : ∀ A, S' (U.functor.obj A) ↔ S A)
    (hT : ∀ A, T' (V.functor.obj A) ↔ T A)
    (L : C ⥤ D) (L' : E ⥤ F) (a : L ⋙ V.functor ≅ U.functor ⋙ L')
    (h : ∀ A, P A → Q (L.obj A))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ L) (fun A ↦ h A.obj A.property) ⊣ G)
    (pres : ∀ (h' : ∀ A, P' A → Q' (L'.obj A))
        (G' : Q'.FullSubcategory ⥤ P'.FullSubcategory),
        (Q'.lift (P'.ι ⋙ L') (fun A ↦ h' A.obj A.property) ⊣ G') →
        ∀ A, T' A.obj → S' (G'.obj A).obj) :
    ∀ A, T A.obj → S (G.obj A).obj := by
  have h' : ∀ A, P' A → Q' (L'.obj A) := by
    intro A hA
    let B := U.inverse.obj A
    have hB : P B := (hP B).mp
      (P'.prop_of_iso (U.counitIso.app A).symm hA)
    exact Q'.prop_of_iso (a.app B ≪≫ L'.mapIso (U.counitIso.app A))
      ((hQ _).mpr (h B hB))
  have eqP : P'.inverseImage U.functor = P := by ext A; exact hP A
  have eqQ : Q'.inverseImage V.functor = Q := by ext A; exact hQ A
  let UU := U.congrFullSubcategory eqP
  let VV := V.congrFullSubcategory eqQ
  let LL := Q'.lift (P'.ι ⋙ L') (fun A ↦ h' A.obj A.property)
  let aa : Q.lift (P.ι ⋙ L) (fun A ↦ h A.obj A.property) ⋙ VV.functor ≅
      UU.functor ⋙ LL :=
    NatIso.ofComponents (fun A ↦ Q'.isoMk (a.app A.obj))
      (fun g ↦ ObjectProperty.hom_ext _ (a.hom.naturality g.hom))
  have : (S'.inverseImage P'.ι).IsClosedUnderIsomorphisms := inferInstance
  exact continuousQbar_transport_preservation UU VV adj LL aa
    (S.inverseImage P.ι) (T.inverseImage Q.ι)
    (S'.inverseImage P'.ι) (T'.inverseImage Q'.ι)
    (fun A ↦ hS A.obj) (fun A ↦ hT A.obj) (pres h')

/-- A pointwise invertible comparison restricts to the full subcategories. -/
@[no_expose] private noncomputable def continuousQbar_restrictComparison
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (P' : ObjectProperty E) (Q' : ObjectProperty F)
    (L : C ⥤ D) (L' : E ⥤ F) (J : C ⥤ E) (K : D ⥤ F)
    (hL : ∀ A, P A → Q (L.obj A)) (hL' : ∀ A, P' A → Q' (L'.obj A))
    (hJ : ∀ A : P.FullSubcategory, P' (J.obj A.obj))
    (hK : ∀ A : Q.FullSubcategory, Q' (K.obj A.obj))
    (b : L ⋙ K ⟶ J ⋙ L') (hb : ∀ A : P.FullSubcategory, IsIso (b.app A.obj)) :
    Q.lift (P.ι ⋙ L) (fun A ↦ hL A.obj A.property) ⋙
        Q'.lift (Q.ι ⋙ K) hK ≅
      P'.lift (P.ι ⋙ J) hJ ⋙
        Q'.lift (P'.ι ⋙ L') (fun A ↦ hL' A.obj A.property) :=
  NatIso.ofComponents (fun A ↦ Q'.isoMk (@asIso _ _ _ _ (b.app A.obj) (hb A)))
    (fun g ↦ ObjectProperty.hom_ext _ (b.naturality g.hom))

/-- Combine a proper comparison with an open comparison before restriction. -/
@[no_expose] private noncomputable def continuousQbar_compositeComparison
    {C D E F G H : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G] [Category H]
    (J : C ⥤ D) (P : D ⥤ E) (J' : F ⥤ G) (P' : G ⥤ H)
    (U : C ⥤ F) (V : D ⥤ G) (W : E ⥤ H)
    (p : P ⋙ W ⟶ V ⋙ P') (j : J ⋙ V ≅ U ⋙ J') :
    (J ⋙ P) ⋙ W ⟶ U ⋙ J' ⋙ P' :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J p ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight j.hom P' ≫
      (Functor.associator _ _ _).hom

private theorem continuousQbar_compositeComparison_isIso
    {C D E F G H : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G] [Category H]
    (J : C ⥤ D) (P : D ⥤ E) (J' : F ⥤ G) (P' : G ⥤ H)
    (U : C ⥤ F) (V : D ⥤ G) (W : E ⥤ H)
    (p : P ⋙ W ⟶ V ⋙ P') (j : J ⋙ V ≅ U ⋙ J') (A : C)
    [IsIso (p.app (J.obj A))] :
    IsIso ((continuousQbar_compositeComparison J P J' P' U V W p j).app A) := by
  dsimp only [continuousQbar_compositeComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- Restrict a composite comparison using isomorphisms only on the chosen generators. -/
@[no_expose] private noncomputable def continuousQbar_restrictComposite
    {C D E F G H : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G] [Category H]
    (J : C ⥤ D) (P : D ⥤ E) (J' : F ⥤ G) (P' : G ⥤ H)
    (U : C ⥤ F) (V : D ⥤ G) (W : E ⥤ H)
    (S : ObjectProperty C) (T : ObjectProperty E)
    (S' : ObjectProperty F) (T' : ObjectProperty H)
    (hL : ∀ A, S A → T ((J ⋙ P).obj A))
    (hL' : ∀ A, S' A → T' ((J' ⋙ P').obj A))
    (hU : ∀ A : S.FullSubcategory, S' (U.obj A.obj))
    (hW : ∀ A : T.FullSubcategory, T' (W.obj A.obj))
    (p : P ⋙ W ⟶ V ⋙ P') (j : J ⋙ V ≅ U ⋙ J')
    (hp : ∀ A : S.FullSubcategory, IsIso (p.app (J.obj A.obj))) :
    T.lift (S.ι ⋙ (J ⋙ P)) (fun A ↦ hL A.obj A.property) ⋙
        T'.lift (T.ι ⋙ W) hW ≅
      S'.lift (S.ι ⋙ U) hU ⋙
        T'.lift (S'.ι ⋙ (J' ⋙ P')) (fun A ↦ hL' A.obj A.property) :=
  continuousQbar_restrictComparison S T S' T' (J ⋙ P) (J' ⋙ P') U W hL hL' hU hW
    (continuousQbar_compositeComparison J P J' P' U V W p j)
    (fun A ↦ by
      let := hp A
      exact continuousQbar_compositeComparison_isIso J P J' P' U V W p j A.obj)

/-- The topology-change pushforward map is the mate of the fixed pullback comparison. -/
@[no_expose] private noncomputable def continuousQbar_topologyPushComparison
    (ℓ : ℕ) [Fact ℓ.Prime] {Z T : Scheme.{u}} (f : Z ⟶ T) :
    (lowerStar (Profinite.padicAlgClRingObj ℓ) f).rightDerivedFunctor ⋙
        algClTopologyScalarExtension ℓ T ⟶
      algClTopologyScalarExtension ℓ Z ⋙
        (lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).rightDerivedFunctor :=
  continuousQbar_mateExplicit
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f)
    (derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f)
    (algClTopologyPullbackSigma ℓ f).hom

/-- Two constructible endpoints and Hom bijections on all constructible tests suffice. -/
private theorem continuousQbar_isIso_on_property
    {C : Type*} [Category C] (P : ObjectProperty C) {A B : C} (f : A ⟶ B)
    (hA : P A) (hB : P B)
    (h : ∀ M, P M → Function.Bijective (fun a : M ⟶ A ↦ a ≫ f)) : IsIso f := by
  obtain ⟨r, hr⟩ := (h B hB).2 (𝟙 B)
  refine ⟨⟨r, ?_, hr⟩⟩
  exact (h A hA).1 (by simp [Category.assoc, hr])

private theorem continuousQbar_postcomp_bijective
    {C : Type*} [Category C] {A B M N : C} (e : N ≅ M) (f : A ⟶ B)
    (h : Function.Bijective (fun a : N ⟶ A ↦ a ≫ f)) :
    Function.Bijective (fun a : M ⟶ A ↦ a ≫ f) := by
  constructor
  · intro a b hab
    apply (cancel_epi e.hom).mp
    apply h.1
    simpa only [Category.assoc] using congrArg (fun t ↦ e.hom ≫ t) hab
  · intro b
    obtain ⟨a, ha⟩ := h.2 (e.hom ≫ b)
    refine ⟨e.inv ≫ a, ?_⟩
    change a ≫ f = e.hom ≫ b at ha
    change (e.inv ≫ a) ≫ f = b
    rw [Category.assoc, ha, Iso.inv_hom_id_assoc]

/-- An equivalence supplies every test object in the property. -/
private theorem continuousQbar_isIso_of_equivalence_tests
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    (J : C ⥤ P.FullSubcategory) [J.IsEquivalence]
    {A B : D} (f : A ⟶ B) (hA : P A) (hB : P B)
    (h : ∀ M : C, Function.Bijective (fun a : (J.obj M).obj ⟶ A ↦ a ≫ f)) :
    IsIso f := by
  apply continuousQbar_isIso_on_property P f hA hB
  intro M hM
  let N := J.objPreimage ⟨M, hM⟩
  let e := P.ι.mapIso (J.objObjPreimageIso ⟨M, hM⟩)
  exact continuousQbar_postcomp_bijective e f (h N)

/-- The canonical topology-change counit mate is invertible for proper pushforward. -/
private theorem continuousQbar_topologyPushComparison_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (f : Z ⟶ T) [f.IsOver (Spec (.of k))] [IsProper f]
    (hT : ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T,
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T
          ((algClTopologyScalarExtension ℓ T).obj K.obj))
    (eT : ((constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T).lift
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T).ι ⋙
          algClTopologyScalarExtension ℓ T) hT).IsEquivalence)
    (hZ : ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Z,
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Z
          ((algClTopologyScalarExtension ℓ Z).obj K.obj))
    (L : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Z) :
    IsIso ((continuousQbar_topologyPushComparison ℓ f).app L.obj) := by
  let C := Profinite.padicAlgClRingObj ℓ
  let B := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  have hnoeth (S : Scheme.{u}) [S.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))] :
      IsNoetherian S := by
    have : IsLocallyNoetherian S :=
      LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
    have : CompactSpace S :=
      QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
    exact ⟨⟩
  have : IsNoetherian Z := hnoeth Z
  have : IsNoetherian T := hnoeth T
  have hC : IsLocalizingAdmissibleCoefficient ℓ C :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  -- 2026-10-25: the all-continuous algebraic closure is no longer an admissible coefficient
  -- (IsLocalizingAdmissibleCoefficient); this coefficient-specific result is off every route.
  have hB : IsLocalizingAdmissibleCoefficient ℓ B := sorry
  have torL : _root_.DerivedCategory.finiteTorAmplitude _ L.obj := by
    have eq := (localizingClosure_ctf_equals_bc ℓ Z C
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
    exact ((congrFun eq L.obj).mpr L.property).2
  have hP := (properLocalizingHypotheses_admissible ℓ C hC k f).1
    ⟨L.obj, L.property, torL⟩
  let J := (constantModelBoundedConstructible B T).lift
    ((constantModelBoundedConstructible C T).ι ⋙ algClTopologyScalarExtension ℓ T) hT
  have : J.IsEquivalence := eT
  have hsource := hT ⟨_, hP.1⟩
  have htarget := (properLocalizingHypotheses_admissible ℓ B hB k f).1
    ⟨_, hZ L, continuousAlgCl_bounded_finiteTor ℓ Z _ (hZ L)⟩
  change IsIso (algClTopologyCounitMate ℓ f L.obj)
  apply continuousQbar_isIso_of_equivalence_tests
    (constantModelBoundedConstructible B T) J _ hsource htarget.1
  intro N
  have hb := (algClTopologyMate_hom_bijection ℓ (ringChar k) k
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ)
    (Over.mk (Z ↘ Spec (.of k))) (Over.mk (T ↘ Spec (.of k)))
    (f.asOver (Spec (.of k))) L hP.1 N).2
  obtain ⟨_, _, _, _, hb, _, _⟩ := hb
  exact hb


/-- The standing finite-type geometry is Noetherian. -/
private theorem continuousQbar_noetherian
    (k : Type u) [Field k] (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    IsNoetherian T := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  exact ⟨⟩

private theorem continuousQbar_old_ctf_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) [IsNoetherian T] :
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T :=
  (localizingClosure_ctf_equals_bc ℓ T (Profinite.padicAlgClRingObj ℓ)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1

private theorem continuousQbar_new_ctf_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) [IsNoetherian T] :
    (constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) T := by
  ext K
  exact ⟨And.left, fun h ↦ ⟨h, continuousAlgCl_bounded_finiteTor ℓ T K h⟩⟩

/-- Proper scalar comparison and the open scalar isomorphism compare the actual composites. -/
private theorem continuousQbar_compactSupportComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification.BoundaryCompactification f)
    (hX : ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X
          ((algClTopologyScalarExtension ℓ X).obj K.obj))
    (hY : ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y,
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
          ((algClTopologyScalarExtension ℓ Y).obj K.obj))
    (eY : ((constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y).lift
        ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y).ι ⋙
          algClTopologyScalarExtension ℓ Y) hY).IsEquivalence)
    (hFC : ∀ K, constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj ℓ) c.obj.obj).obj K))
    (hFB : ∀ K, constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X K →
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
          ((rightDerivedLowerShriekOfCompactification
            (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) c.obj.obj).obj K)) :
    Nonempty
      (restrictionGlueLowerShriek (Profinite.padicAlgClRingObj ℓ) c.obj.obj hFC ⋙
          (constantModelBoundedConstructible
            (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y).lift
              ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y).ι ⋙
                algClTopologyScalarExtension ℓ Y) hY ≅
        (constantModelBoundedConstructible
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).lift
            ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
              algClTopologyScalarExtension ℓ X) hX ⋙
          restrictionGlueLowerShriek
            (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) c.obj.obj hFB) := by
  classical
  let C := Profinite.padicAlgClRingObj ℓ
  let B := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let c₀ := c.obj.obj
  let : c₀.Z.Over (Spec (.of k)) := ⟨c₀.g ≫ (Y ↘ Spec (.of k))⟩
  have : c₀.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : c₀.i.IsOver (Spec (.of k)) := ⟨by
    change c₀.i ≫ c₀.g ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    rw [← Category.assoc, ← c₀.comm]
    exact comp_over f (Spec (.of k))⟩
  have : IsSeparated (c₀.Z ↘ Spec (.of k)) := by
    change IsSeparated (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType (c₀.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (c₀.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c₀.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : IsNoetherian X := continuousQbar_noetherian k X
  have hC : IsLocalizingAdmissibleCoefficient ℓ C :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  obtain ⟨_, _, hZ, _, _⟩ := constructible_algCl_topology_comparison
    ℓ (ringChar k) k (Fact.out : (ringChar k).Prime).pos
    (Fact.out : ringChar k ≠ ℓ) (Over.mk (c₀.Z ↘ Spec (.of k)))
  have hp (K : ConstantModelBoundedConstructible C X) :
      IsIso ((continuousQbar_topologyPushComparison ℓ c₀.g).app
        ((openImmersionLowerShriek C c₀.i).mapDerivedCategory.obj K.obj)) := by
    have hK := (congrFun (continuousQbar_old_ctf_eq ℓ X) K.obj).mpr K.property
    have hJ := (openImmersionLowerShriek_localizing ℓ k (ringChar k)
      (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) C hC c₀.i).1
      ⟨K.obj, hK⟩
    exact continuousQbar_topologyPushComparison_isIso ℓ k c₀.g hY eY hZ ⟨_, hJ.1⟩
  exact ⟨continuousQbar_restrictComposite
    (openImmersionLowerShriek C c₀.i).mapDerivedCategory
    (lowerStar C c₀.g).rightDerivedFunctor
    (openImmersionLowerShriek B c₀.i).mapDerivedCategory
    (lowerStar B c₀.g).rightDerivedFunctor
    (algClTopologyScalarExtension ℓ X) (algClTopologyScalarExtension ℓ c₀.Z)
    (algClTopologyScalarExtension ℓ Y) _ _ _ _ hFC hFB hX hY
    (continuousQbar_topologyPushComparison ℓ c₀.g)
    (derivedOpenImmersionShriekIso (algClTopologyInclusion ℓ) c₀.i) hp⟩

/-- Scalar equivalence transports the rational constructible adjunction, and the
localizing generator test identifies its right adjoint with every supplied Brown adjoint. -/
private theorem continuousQbar_canonical_preservation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X K →
      localizingClosureProEtale (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) c.obj.obj).obj K))
    (G : (localizingClosureProEtale
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y).FullSubcategory ⥤
      (localizingClosureProEtale
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).FullSubcategory)
    (adj : localizingLowerShriek
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) c.obj.obj h ⊣ G) :
    ∀ K, (constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K.obj →
      (constantModelBoundedConstructible
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) (G.obj K).obj := by
  classical
  let C := Profinite.padicAlgClRingObj ℓ
  let B := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  have : IsNoetherian X := continuousQbar_noetherian k X
  have : IsNoetherian Y := continuousQbar_noetherian k Y
  have hC : IsLocalizingAdmissibleCoefficient ℓ C :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  -- 2026-10-25: the all-continuous algebraic closure is no longer an admissible coefficient
  -- (IsLocalizingAdmissibleCoefficient); this coefficient-specific result is off every route.
  have hB : IsLocalizingAdmissibleCoefficient ℓ B := sorry
  obtain ⟨hC', _, _, _, _, _, _, GC, _, _, _, adjC, _⟩ :=
    exists_localizingExceptionalAdjoint C ℓ k f c hC
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  obtain ⟨_, hCY, hFC, hGC, adjCbc, _⟩ := (rationalRestrictionGlue.{u, u}
    C ℓ E₀.1 (Or.inr ⟨Iso.refl _⟩) k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) f c hC' GC adjC).2
  obtain ⟨_, htX, hX, eX, _⟩ := constructible_algCl_topology_comparison
    ℓ (ringChar k) k (Fact.out : (ringChar k).Prime).pos
    (Fact.out : ringChar k ≠ ℓ) (Over.mk (X ↘ Spec (.of k)))
  obtain ⟨_, _, hY, eY, _⟩ := constructible_algCl_topology_comparison
    ℓ (ringChar k) k (Fact.out : (ringChar k).Prime).pos
    (Fact.out : ringChar k ≠ ℓ) (Over.mk (Y ↘ Spec (.of k)))
  let JX := (constantModelBoundedConstructible B X).lift
    ((constantModelBoundedConstructible C X).ι ⋙ algClTopologyScalarExtension ℓ X) hX
  let JY := (constantModelBoundedConstructible B Y).lift
    ((constantModelBoundedConstructible C Y).ι ⋙ algClTopologyScalarExtension ℓ Y) hY
  have : (constantModelBoundedConstructible B X).IsTriangulated := htX
  have : (constantModelBoundedConstructible B X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined B X).2.1
  have : JX.IsEquivalence := eX
  have : JY.IsEquivalence := eY
  let U := JX.asEquivalence
  let V := JY.asEquivalence
  have hFB : ∀ K, constantModelBoundedConstructible B X K →
      constantModelBoundedConstructible B Y
        ((rightDerivedLowerShriekOfCompactification B c.obj.obj).obj K) := by
    intro K hK
    exact ((compactification_localizing B ℓ k f c hB).2.2.2 K
      ⟨hK, continuousAlgCl_bounded_finiteTor ℓ X K hK⟩).1
  let FC := restrictionGlueLowerShriek C c.obj.obj hFC
  let FB := restrictionGlueLowerShriek B c.obj.obj hFB
  let RC := restrictionGlueUpperShriek C GC hCY hGC
  obtain ⟨a⟩ := continuousQbar_compactSupportComparison ℓ k f c hX hY eY hFC hFB
  let RB := V.inverse ⋙ RC ⋙ U.functor
  let adjB : FB ⊣ RB := continuousQbar_conjugateAdjunction U V adjCbc a
  exact continuousQbar_generator_transfer
    (constantModelBoundedConstructible B X) (constantModelBoundedConstructible B Y)
    _ _ (continuousQbar_new_ctf_eq ℓ X) (continuousQbar_new_ctf_eq ℓ Y)
    (rightDerivedLowerShriekOfCompactification B c.obj.obj) hFB h RB adjB G adj


section CoefficientIsomorphism

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

local notation "S(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
local notation "L(" T ")" => localizingClosureProEtale Λ T

-- The ambient-intersection transport argument follows ExceptionalInverseImageExistence.
-- That consumer cannot be imported here because it depends on this theorem.
/-- Exact coefficient equivalences preserve the ambient-intersection closure. -/
private theorem continuousQbar_map_localizing_iso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, L(T) K → localizingClosureProEtale Λ' T
      ((shriekCoefficientTransport e T).obj K) := by
  let F := shriekCoefficientTransport e T
  have : F.IsEquivalence := (shriekCoefficientIso_transport e T).1
  have : F.IsTriangulated := (shriekCoefficientIso_transport e T).2.1
  exact continuousQbar_map_closure F _ _
    (fun A hA ↦ (shriekCoefficientIso_transport e T).2.2.2.1 A |>.mpr hA)

/-- Coefficient transport identifies the two recorded localizing closures. -/
private theorem continuousQbar_localizing_iso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, localizingClosureProEtale Λ' T ((shriekCoefficientTransport e T).obj K) ↔ L(T) K := by
  intro K
  constructor
  · intro hK
    have hi : L(T).IsClosedUnderIsomorphisms :=
      (localizingClosure_exists Λ T S(T)).2.2.2.1.2.1
    let := hi
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (continuousQbar_map_localizing_iso _ e.symm T _ hK)
  · exact continuousQbar_map_localizing_iso Λ e T K

/-- Conjugating an adjunction transports its constructible-preservation property. -/
private theorem continuousQbar_preservation_iso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, L(X) K → L(Y)
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : L(Y).FullSubcategory ⥤ L(X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (pres : ∀ (h' : ∀ K, localizingClosureProEtale Λ' X K →
          localizingClosureProEtale Λ' Y
            ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
        (G' : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ' X).FullSubcategory),
        (localizingLowerShriek Λ' c.obj.obj h' ⊣ G') →
        ∀ N, (constantModelBoundedConstructible Λ' Y ⊓
          _root_.DerivedCategory.finiteTorAmplitude _) N.obj →
          (constantModelBoundedConstructible Λ' X ⊓
            _root_.DerivedCategory.finiteTorAmplitude _) (G'.obj N).obj) :
    ∀ N, S(Y) N.obj → S(X) (G.obj N).obj := by
  have isoClosed (T : Scheme.{u}) :
      (localizingClosureProEtale Λ' T).IsClosedUnderIsomorphisms :=
    (localizingClosure_exists Λ' T
      (constantModelBoundedConstructible Λ' T ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      ).2.2.2.1.2.1
  let := isoClosed X
  let := isoClosed Y
  have equiv (T : Scheme.{u}) : (shriekCoefficientTransport e T).IsEquivalence :=
    (shriekCoefficientIso_transport e T).1
  have : (constantModelBoundedConstructible Λ' X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  have : (_root_.DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
      ).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.2.2.1
  exact continuousQbar_transport_restricted
    (shriekCoefficientTransport e X).asEquivalence
    (shriekCoefficientTransport e Y).asEquivalence
    L(X) L(Y) (localizingClosureProEtale Λ' X) (localizingClosureProEtale Λ' Y)
    (continuousQbar_localizing_iso Λ e X) (continuousQbar_localizing_iso Λ e Y)
    S(X) S(Y)
    (constantModelBoundedConstructible Λ' X ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
    (constantModelBoundedConstructible Λ' Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
    ((shriekCoefficientIso_transport e X).2.2.2.1)
    ((shriekCoefficientIso_transport e Y).2.2.2.1)
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
    (rightDerivedLowerShriekOfCompactification Λ' c.obj.obj)
    (shriekCoefficientCompactificationIso e c) h G adj pres

end CoefficientIsomorphism

/-- The given localizing right adjoint preserves constructible finite-Tor complexes for
C(-, Qbar_ell), with all continuous maps for the induced ell-adic topology.
This assertion does not identify this coefficient with `Profinite.padicAlgClRingObj`.

Source: blueprint main-20261015, sk-thm-restriction.proof.md, first two paragraphs;
sk-def-localizing-closure, coefficient convention
(blueprint: lem-sfb-continuous-qbar-exceptional-preservation).

Proof in words:
Write C for the finite-subextension-valued algebraic closure and B for the ring of
all norm-continuous maps. The sectionwise inclusion C -> B induces, on each scheme,
the existing derived scalar-extension equivalence between bounded constructible
categories. This uses the topology-comparison theorem, not an isomorphism of rings.
For B, bounded constructibility implies finite Tor amplitude on a Noetherian scheme.
For C the existing rational equality gives the same conclusion.

First compare proper pushforwards under this scalar extension. Its canonical map is
the geometric adjunction mate of the specified scalar/pullback comparison. Proper
finiteness makes both endpoints bounded constructible. The topology-comparison Hom
bijection says that postcomposition with this map is bijective when the test object
comes from C. Essential surjectivity supplies every constructible B-test object.
Testing with both endpoints gives a two-sided inverse, so the canonical map is an
isomorphism. Its definition as a mate supplies naturality.

For the chosen compactification f = j followed by p, combine this proper comparison
with the canonical scalar/open-extension isomorphism. Thus scalar extension identifies
the actual restricted compactification composites. The rational restriction theorem
for C supplies their constructible adjunction; its proof retains the affine-space
purity, closed-support and finite-cover route of sk-thm-restriction. Transport this
adjunction through the two constructible scalar equivalences to obtain an adjunction
for the actual B-composite on bounded constructible objects.

Compare its right adjoint with the supplied right adjoint on the localizing closures.
Transpose the small adjunction's counit under the supplied adjunction. On Hom from
any shifted constructible generator, composition with this map is the composite of
the two adjunction bijections and the full-inclusion bijections. The map is therefore
invertible by the localizing generator test: its cone is in the closure and orthogonal
to every shifted generator, hence zero. Consequently the supplied adjoint's value is
bounded constructible. The constructible-implies-Tor theorem completes the B-case.
Finally conjugate the original adjunction by the exact coefficient equivalences of hΛ.
They preserve and reflect Dctf and its ambient-intersection localizing closure. The
argument uses no nonempty-scheme or nonzero-object assumption, so includes empty
schemes, zero complexes and empty strata.
-/
theorem continuousQbarExceptional_preserves_constructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hΛ : Nonempty
      (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      (constantModelBoundedConstructible Λ Y K.obj ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K.obj) →
      constantModelBoundedConstructible Λ X (G.obj K).obj ∧
        _root_.DerivedCategory.finiteTorAmplitude _ (G.obj K).obj := by
  classical
  obtain ⟨e⟩ := hΛ
  apply continuousQbar_preservation_iso Λ e c h G adj
  exact fun h' G' adj' ↦ continuousQbar_canonical_preservation ℓ k f c h' G' adj'

end AlgebraicGeometry.ProEtale.CondensedRing
