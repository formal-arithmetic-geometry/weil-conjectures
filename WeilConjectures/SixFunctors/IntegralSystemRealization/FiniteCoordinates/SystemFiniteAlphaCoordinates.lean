/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAdjunctionCoordinates
public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenData
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemNativeOperationCoordinates
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowEvaluation
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientSystemClopenLocalization

/-! # Exact pull/open square in finite coordinates
Source: Stacks 03DI and 0F7B; finite evaluation in prop-sf-pf-coherence.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
set_option maxRecDepth 4096
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor pushCoordinates shriekCoordinates pullCoordinates
  sfIntrinsicDerivedEquivalence

open CategoryTheory.Limits Opposite
open StrictTower.MateEvaluationScalars
attribute [local irreducible] constantSheaf presheafToSheaf Functor.leftAdjoint
  Functor.ofSequence Functor.ofOpSequence MorphismProperty.Over.pullback

private theorem pushforward_eq_iso
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat} {R : Sheaf K RingCat}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R} (h : φ = ψ) :
    eqToIso (congrArg (fun q ↦ SheafOfModules.pushforward q) h) =
      SheafOfModules.pushforwardCongr h := by
  subst ψ
  apply Iso.ext
  ext M V x
  rfl

private theorem ordinary_bridge_eq (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    b.ordinary f ≪≫ eqToIso (SemilinearProperOpen.push_eq
      (scalarRings l E) (scalarTransitions l E) f) =
      integralNativeOrdinaryDirectIso l E f := by
  apply Iso.ext
  ext M V x
  have hc : eqToIso (SemilinearProperOpen.push_eq
      (scalarRings l E) (scalarTransitions l E) f) =
      SheafOfModules.pushforwardCongr (SemilinearProperOpen.coefficientMap_forget_eq
        (scalarRings l E) (scalarTransitions l E) f) := by
    exact pushforward_eq_iso _
  simp only [hc, Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact b.sections f M V.unop.1 V.unop.2 x

private theorem adjointUniq_heq
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R F G : B ⥤ A} [F.IsRightAdjoint] [G.IsRightAdjoint]
    (a : L ⊣ R) (h : F = G) (e : R ≅ F) (f : R ≅ G)
    (he : HEq e f) :
    HEq ((a.ofNatIsoRight e).leftAdjointUniq (Adjunction.ofIsRightAdjoint F))
      ((a.ofNatIsoRight f).leftAdjointUniq (Adjunction.ofIsRightAdjoint G)) := by
  subst G
  cases eq_of_heq he
  rfl

private theorem iso_heq_of_comp_eq
    {A : Type*} [Category A] {X Y Z : A} (h : Y = Z) (e : X ≅ Y) (f : X ≅ Z)
    (he : e ≪≫ eqToIso h = f) : HEq e f := by
  subst Z
  exact heq_of_eq (by simpa only [eqToIso_refl, Iso.trans_refl] using he)

attribute [local irreducible] integralNativeOrdinaryDirectIso in
private theorem ordinary_bridge_heq (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (b.ordinary f) (integralNativeOrdinaryDirectIso l E f) := by
  have hh := ordinary_bridge_eq l E o b f
  have h := SemilinearProperOpen.push_eq (scalarRings l E) (scalarTransitions l E) f
  exact iso_heq_of_comp_eq h _ _ hh

private theorem derived_iso_heq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (h : G = H) (e : F ≅ G) (f : F ≅ H) (he : HEq e f) :
    HEq (Functor.mapDerivedCategoryNatIso e) (Functor.mapDerivedCategoryNatIso f) := by
  subst H
  cases eq_of_heq he
  rfl

attribute [local instance] SemilinearProperOpen.push_isRightAdjoint
  SemilinearProperOpen.pull_additive SemilinearProperOpen.pull_limits
  SemilinearProperOpen.pull_colimits VaryingRing.push_isRightAdjoint
  VaryingRing.pullAdditive VaryingRing.pullLimits VaryingRing.pullColimits
  pullbackTensorSequenceInverse_additive pullbackTensorSequenceInverse_limits
  pullbackTensorSequenceInverse_colimits

private theorem pull_bridge_heq (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (b.pull l E f) (integralNativePullIso l E f) := by
  have := SemilinearProperOpen.push_isRightAdjoint.{u} (scalarRings l E)
    (scalarTransitions l E) f
  have := VaryingRing.push_isRightAdjoint.{u} (scalarRings l E) (scalarTransitions l E) f
  have := pullbackTensorSequenceInverse_additive.{u} l E f
  have := pullbackTensorSequenceInverse_limits.{u} l E f
  have := pullbackTensorSequenceInverse_colimits.{u} l E f
  have := SemilinearProperOpen.pull_additive.{u} (scalarRings l E)
    (scalarTransitions l E) f
  have := SemilinearProperOpen.pull_limits.{u} (scalarRings l E) (scalarTransitions l E) f
  have := SemilinearProperOpen.pull_colimits.{u} (scalarRings l E) (scalarTransitions l E) f
  have := VaryingRing.pullAdditive.{u} (scalarRings l E) (scalarTransitions l E) f
  have := VaryingRing.pullLimits.{u} (scalarRings l E) (scalarTransitions l E) f
  have := VaryingRing.pullColimits.{u} (scalarRings l E) (scalarTransitions l E) f
  have hh := adjointUniq_heq (pullbackTensorSequenceAdjunction l E f)
    (SemilinearProperOpen.push_eq (scalarRings l E) (scalarTransitions l E) f)
    (b.ordinary f) (integralNativeOrdinaryDirectIso l E f)
    (ordinary_bridge_heq l E o b f)
  exact derived_iso_heq
    (F := pullbackTensorSequenceInverse l E f)
    (G := SemilinearProperOpen.pull (scalarRings l E) (scalarTransitions l E) f)
    (H := VaryingRing.pull (scalarRings l E) (scalarTransitions l E) f)
    (SemilinearProperOpen.pull_eq (scalarRings l E) (scalarTransitions l E) f) _ _ hh

private theorem leftUniq_heq
    {A B : Type*} [Category A] [Category B]
    {L L' L'' : A ⥤ B} {R F G : B ⥤ A}
    (a : L ⊣ R) (hL : L' = L'') (h : F = G)
    (e : R ≅ F) (f : R ≅ G) (he : HEq e f)
    (b : L' ⊣ F) (c : L'' ⊣ G) (hb : HEq b c) :
    HEq ((a.ofNatIsoRight e).leftAdjointUniq b)
      ((a.ofNatIsoRight f).leftAdjointUniq c) := by
  subst L'' G
  cases eq_of_heq he
  cases eq_of_heq hb
  rfl

private theorem shriek_bridge_heq (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    HEq (b.shriek l E j) (integralNativeOpenIso l E j (o.extension j)) := by
  exact leftUniq_heq (o.extension j).adj
    (SemilinearProperOpen.J_eq (scalarRings l E) (scalarTransitions l E) j)
    (SemilinearProperOpen.P_eq (scalarRings l E) (scalarTransitions l E) j)
    (b.pull l E j) (integralNativePullIso l E j) (pull_bridge_heq l E o b j)
    (SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (VaryingRing.jAdj (scalarRings l E) (scalarTransitions l E) j)
    (SemilinearProperOpen.Normalization.jadj_heq (scalarRings l E)
      (scalarTransitions l E) j)

private theorem transportAlpha_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {L₂ : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
    {L₁' L₁'' : A ⥤ B} {L₂' L₂'' : C ⥤ D}
    {G' G'' : A ⥤ C} {H' H'' : B ⥤ D}
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (e' : L₁ ≅ L₁'') (f' : L₂ ≅ L₂'') (g' : G ≅ G'') (h' : H ≅ H'')
    (a : G' ⋙ L₂' ⟶ L₁' ⋙ H') (a' : G'' ⋙ L₂'' ⟶ L₁'' ⋙ H'')
    (h₁ : L₁' = L₁'') (h₂ : L₂' = L₂'') (h₃ : G' = G'') (h₄ : H' = H'')
    (he : HEq e e') (hf : HEq f f') (hg : HEq g g') (hh : HEq h h')
    (ha : HEq a a') :
    AmbientClopen.transportAlpha e f g h a =
      AmbientClopen.transportAlpha e' f' g' h' a' := by
  subst L₁'' L₂'' G'' H''
  cases eq_of_heq he
  cases eq_of_heq hf
  cases eq_of_heq hg
  cases eq_of_heq hh
  cases eq_of_heq ha
  rfl

attribute [local irreducible] AmbientClopen.transportAlpha integralNativePullIso
  integralNativeOpenIso CanonicalBridge.pull CanonicalBridge.shriek in
private theorem realizationAlpha_native (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    AmbientClopen.realizationAlpha l E o b k r p i h =
      AmbientClopen.transportAlpha (integralNativePullIso l E r)
        (integralNativePullIso l E p) (integralNativeOpenIso l E i (o.extension i))
        (integralNativeOpenIso l E k (o.extension k))
        (VaryingRing.alpha (scalarRings l E) (scalarTransitions l E) k r p i h) := by
  exact transportAlpha_heq _ _ _ _ _ _ _ _ _ _
    (SemilinearProperOpen.P_eq (scalarRings l E) (scalarTransitions l E) r)
    (SemilinearProperOpen.P_eq (scalarRings l E) (scalarTransitions l E) p)
    (SemilinearProperOpen.J_eq (scalarRings l E) (scalarTransitions l E) i)
    (SemilinearProperOpen.J_eq (scalarRings l E) (scalarTransitions l E) k)
    (pull_bridge_heq l E o b r) (pull_bridge_heq l E o b p)
    (shriek_bridge_heq l E o b i) (shriek_bridge_heq l E o b k)
    (AmbientClopen.system_alpha_localized (scalarRings l E) (scalarTransitions l E)
      k r p i h).symm

private def pasteCoordinate
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {F : A ⥤ B} {F' : A' ⥤ B'} {F'' : A'' ⥤ B''}
    {E : A ⥤ A'} {H : B ⥤ B'} {Q : A' ⥤ A''} {S : B' ⥤ B''}
    (e : F ⋙ H ≅ E ⋙ F') (f : F' ⋙ S ≅ Q ⋙ F'') :
    F ⋙ (H ⋙ S) ≅ (E ⋙ Q) ⋙ F'' :=
  Functor.isoWhiskerRight e S ≪≫ Functor.isoWhiskerLeft E f

private theorem pasteCoordinate_assoc_id
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category A''] [Category B'']
    {F F' : A ⥤ B} {G : A' ⥤ B'} {K : A'' ⥤ B''}
    {E : A ⥤ A'} {H : B ⥤ B'} {Q : A' ⥤ A''} {S : B' ⥤ B''}
    (e : F ≅ F') (f : F' ⋙ H ≅ E ⋙ G) (g : G ⋙ S ≅ Q ⋙ K) :
    pasteCoordinate
        (pasteCoordinate (E := 𝟭 A) (H := 𝟭 B) (Q := E) (S := H) e f) g =
      Functor.isoWhiskerRight e (H ⋙ S) ≪≫ Functor.isoWhiskerRight f S ≪≫
        Functor.isoWhiskerLeft E g := by
  apply Iso.ext
  ext N
  simp only [pasteCoordinate, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Functor.comp_obj, Functor.id_obj,
    Category.assoc]

private theorem paste_alpha_squares
    {A B C D A' B' C' D' A'' B'' C'' D'' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Category A''] [Category B''] [Category C''] [Category D'']
    {I : A ⥤ B} {P : B ⥤ C} {R : A ⥤ D} {J : D ⥤ C}
    {I' : A' ⥤ B'} {P' : B' ⥤ C'} {R' : A' ⥤ D'} {J' : D' ⥤ C'}
    {I'' : A'' ⥤ B''} {P'' : B'' ⥤ C''} {R'' : A'' ⥤ D''} {J'' : D'' ⥤ C''}
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {QA : A' ⥤ A''} {QB : B' ⥤ B''} {QC : C' ⥤ C''} {QD : D' ⥤ D''}
    (ei : I ⋙ EB ≅ EA ⋙ I') (ep : P ⋙ EC ≅ EB ⋙ P')
    (er : R ⋙ ED ≅ EA ⋙ R') (ej : J ⋙ EC ≅ ED ⋙ J')
    (fi : I' ⋙ QB ≅ QA ⋙ I'') (fp : P' ⋙ QC ≅ QB ⋙ P'')
    (fr : R' ⋙ QD ≅ QA ⋙ R'') (fj : J' ⋙ QC ≅ QD ⋙ J'')
    (a : I ⋙ P ⟶ R ⋙ J) (a' : I' ⋙ P' ⟶ R' ⋙ J')
    (a'' : I'' ⋙ P'' ⟶ R'' ⋙ J'')
    (h : ∀ N, EC.map (a.app N) ≫ ej.hom.app (R.obj N) ≫ J'.map (er.hom.app N) =
      ep.hom.app (I.obj N) ≫ P'.map (ei.hom.app N) ≫ a'.app (EA.obj N))
    (h' : ∀ M, QC.map (a'.app M) ≫ fj.hom.app (R'.obj M) ≫ J''.map (fr.hom.app M) =
      fp.hom.app (I'.obj M) ≫ P''.map (fi.hom.app M) ≫ a''.app (QA.obj M))
    (N : A) :
    (EC ⋙ QC).map (a.app N) ≫
      (pasteCoordinate ej fj).hom.app (R.obj N) ≫
      J''.map ((pasteCoordinate er fr).hom.app N) =
    (pasteCoordinate ep fp).hom.app (I.obj N) ≫
      P''.map ((pasteCoordinate ei fi).hom.app N) ≫ a''.app ((EA ⋙ QA).obj N) := by
  simp only [pasteCoordinate, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  have hj := fj.hom.naturality (er.hom.app N)
  have hp := fp.hom.naturality (ei.hom.app N)
  dsimp only [Functor.comp_map] at hj hp
  rw [← reassoc_of% hj, ← QC.map_comp_assoc, ← QC.map_comp_assoc, Category.assoc, h N]
  simp only [Functor.map_comp, Category.assoc]
  rw [h' (EA.obj N), ← reassoc_of% hp]
  rfl

private theorem transportAlpha_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {L₂ L₂' : C ⥤ D}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (a : G' ⋙ L₂' ⟶ L₁' ⋙ H') (N : A) :
    (AlgebraicGeometry.ProEtale.AmbientClopen.transportAlpha e f g h a).app N ≫
      h.hom.app (L₁.obj N) ≫ H'.map (e.hom.app N) =
    f.hom.app (G.obj N) ≫ L₂'.map (g.hom.app N) ≫ a.app N := by
  simp only [AlgebraicGeometry.ProEtale.AmbientClopen.transportAlpha,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← H'.map_comp, Iso.inv_hom_id_app, H'.map_id]
  rw [← f.hom.naturality_assoc]
  erw [Category.comp_id]

private theorem native_alpha_evaluation
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (n : ℕ) (N : VaryingRing.Derived R φ S) :
    (VaryingRing.ev R φ W n).map ((VaryingRing.alpha R φ k r p i h).app N) ≫
        (VaryingRing.evalJ R φ k n).hom.app ((VaryingRing.G R φ r).obj N) ≫
        (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
          ((VaryingRing.evalG R φ r n).hom.app N) =
      (VaryingRing.evalG R φ p n).hom.app ((VaryingRing.J R φ i).obj N) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((VaryingRing.evalJ R φ i n).hom.app N) ≫
        (singleDerivedAlpha (R n) k r p i h).app ((VaryingRing.ev R φ S n).obj N) := by
  obtain ⟨a, ha, hs⟩ := VaryingRing.clopenArrowEvaluation R φ k r p i h n
  have ht (M : StrictTower.Derived (R n) S) :
      a.app ((StrictTower.ev (R n) S 0).obj M) =
        (singleDerivedAlpha (R n) k r p i h).app
          ((StrictTower.ev (R n) S 0).obj M) := by
    apply (cancel_epi ((StrictTower.evalG (R n) p 0).hom.app
      ((StrictTower.J (R n) i).obj M) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((StrictTower.evalJ (R n) i 0).hom.app M))).1
    simpa only [Category.assoc] using
      (hs M).symm.trans (evaluation_alpha (R n) k r p i h 0 M)
  have he : a = singleDerivedAlpha (R n) k r p i h := by
    ext M
    let e := (VaryingRing.constantEval (R n) S).app M
    have hn := a.naturality e.hom
    have hn' := (singleDerivedAlpha (R n) k r p i h).naturality e.hom
    dsimp only [Functor.comp_map] at hn hn'
    apply (cancel_epi (((StrictTower.moduleJ (R n) i).mapDerivedCategory ⋙
      (StrictTower.modulePullback (R n) p).mapDerivedCategory).map e.hom)).1
    simp only [Functor.comp_map]
    rw [show a.app ((VaryingRing.constantDerived (R n) S ⋙ StrictTower.ev (R n) S 0).obj M) =
      (singleDerivedAlpha (R n) k r p i h).app
        ((VaryingRing.constantDerived (R n) S ⋙ StrictTower.ev (R n) S 0).obj M) from
      ht ((VaryingRing.constantDerived (R n) S).obj M)] at hn
    simpa only [Functor.comp_obj, Functor.id_obj] using hn.trans hn'.symm
  simpa only [he] using ha N

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportSystemLevel compactSupportSystemQuotient

section
attribute [local semireducible] sfIntrinsicDerivedEquivalence

private theorem shriek_coordinates_native (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    shriekCoordinates l E o m j = systemNativeShriekCoordinates l E o m j := by
  apply Iso.ext
  ext M
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let R := sfIntrinsicDerivedEquivalence X A
  let S := sfIntrinsicDerivedEquivalence Y A
  let G := (sfIntrinsicExtensionByZero j A).mapDerivedCategory
  let q := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  have hn := integralNativeOpenComparison l E j (o.extension j) (o.openEvaluation j) M m
  have ht := congrArg (fun f ↦ S.inverse.map f ≫
    S.inverse.map (G.map (R.counitIso.inv.app
      ((coefficientSequenceDerivedEvaluation l E X m).obj M))) ≫
    S.inverse.map (q.hom.app (input l E m X M)) ≫
    S.unitIso.inv.app _) hn
  simp only [shriekCoordinates, fixedShriek, shriek, systemNativeShriekCoordinates,
    finiteNativeShriekCoordinates, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, NatIso.ofComponents_hom_app,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.map_comp, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc,
    fixedEvaluation_map, input, Functor.id_obj,
    A, R, S, G, q] at ht ⊢
  exact ht.symm
end

private theorem pull_coordinates_paste (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pasteCoordinate
        (pasteCoordinate (E := 𝟭 _) (H := 𝟭 _)
          (Q := coefficientSequenceDerivedEvaluation l E Y m)
          (S := coefficientSequenceDerivedEvaluation l E X m)
          (integralNativePullIso l E f)
          (VaryingRing.evalG (scalarRings l E) (scalarTransitions l E) f m))
        (finiteNativePullCoordinates (Padic.coefficientExtensionRing l E (m + 1)) f) =
      systemNativePullCoordinates l E m f := by
  simpa only [systemNativePullCoordinates, fixedEvaluation, pull,
    pullbackTensorSequenceDerived] using
    (pasteCoordinate_assoc_id
      (E := coefficientSequenceDerivedEvaluation l E Y m)
      (H := coefficientSequenceDerivedEvaluation l E X m)
      (integralNativePullIso l E f)
      (VaryingRing.evalG (scalarRings l E) (scalarTransitions l E) f m)
      (finiteNativePullCoordinates (Padic.coefficientExtensionRing l E (m + 1)) f))

private theorem shriek_coordinates_paste (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    pasteCoordinate
        (pasteCoordinate (E := 𝟭 _) (H := 𝟭 _)
          (Q := coefficientSequenceDerivedEvaluation l E X m)
          (S := coefficientSequenceDerivedEvaluation l E Y m)
          (integralNativeOpenIso l E f (o.extension f))
          (VaryingRing.evalJ (scalarRings l E) (scalarTransitions l E) f m))
        (finiteNativeShriekCoordinates (Padic.coefficientExtensionRing l E (m + 1)) f) =
      systemNativeShriekCoordinates l E o m f := by
  simpa only [systemNativeShriekCoordinates, fixedEvaluation, Operations.shriek, Open.derived] using
    (pasteCoordinate_assoc_id
      (E := coefficientSequenceDerivedEvaluation l E X m)
      (H := coefficientSequenceDerivedEvaluation l E Y m)
      (integralNativeOpenIso l E f (o.extension f))
      (VaryingRing.evalJ (scalarRings l E) (scalarTransitions l E) f m)
      (finiteNativeShriekCoordinates (Padic.coefficientExtensionRing l E (m + 1)) f))

private def rawPullCoordinates (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pasteCoordinate (E := 𝟭 _) (H := 𝟭 _)
    (Q := coefficientSequenceDerivedEvaluation l E Y m)
    (S := coefficientSequenceDerivedEvaluation l E X m)
    (integralNativePullIso l E f)
    (VaryingRing.evalG (scalarRings l E) (scalarTransitions l E) f m)

private def rawShriekCoordinates (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  pasteCoordinate (E := 𝟭 _) (H := 𝟭 _)
    (Q := coefficientSequenceDerivedEvaluation l E X m)
    (S := coefficientSequenceDerivedEvaluation l E Y m)
    (integralNativeOpenIso l E j (o.extension j))
    (VaryingRing.evalJ (scalarRings l E) (scalarTransitions l E) j m)

private theorem transportAlpha_evaluation
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {I I₀ : A ⥤ B} {P P₀ : B ⥤ C} {R R₀ : A ⥤ D} {J J₀ : D ⥤ C}
    {I' : A' ⥤ B'} {P' : B' ⥤ C'} {R' : A' ⥤ D'} {J' : D' ⥤ C'}
    {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
    (ei : I ≅ I₀) (ep : P ≅ P₀) (er : R ≅ R₀) (ej : J ≅ J₀)
    (fi : I₀ ⋙ QB ≅ QA ⋙ I') (fp : P₀ ⋙ QC ≅ QB ⋙ P')
    (fr : R₀ ⋙ QD ≅ QA ⋙ R') (fj : J₀ ⋙ QC ≅ QD ⋙ J')
    (a : I₀ ⋙ P₀ ⟶ R₀ ⋙ J₀) (a' : I' ⋙ P' ⟶ R' ⋙ J')
    (hs : ∀ N, QC.map (a.app N) ≫ fj.hom.app (R₀.obj N) ≫ J'.map (fr.hom.app N) =
      fp.hom.app (I₀.obj N) ≫ P'.map (fi.hom.app N) ≫ a'.app (QA.obj N)) (N : A) :
    QC.map ((AmbientClopen.transportAlpha er ep ei ej a).app N) ≫
      (pasteCoordinate (E := 𝟭 D) (H := 𝟭 C) ej fj).hom.app (R.obj N) ≫
      J'.map ((pasteCoordinate (E := 𝟭 A) (H := 𝟭 D) er fr).hom.app N) =
    (pasteCoordinate (E := 𝟭 B) (H := 𝟭 C) ep fp).hom.app (I.obj N) ≫
      P'.map ((pasteCoordinate (E := 𝟭 A) (H := 𝟭 B) ei fi).hom.app N) ≫
      a'.app (QA.obj N) := by
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] using
    (paste_alpha_squares (EA := 𝟭 A) (EB := 𝟭 B) (EC := 𝟭 C) (ED := 𝟭 D)
      ei ep er ej fi fp fr fj (AmbientClopen.transportAlpha er ep ei ej a) a a'
      (fun M ↦ transportAlpha_square er ep ei ej a M) hs N)

set_option maxHeartbeats 1600000 in
-- The native evaluation and system presentations require large coefficient conversions.
attribute [local irreducible] pasteCoordinate integralNativePullIso integralNativeOpenIso in
private theorem raw_alpha_coordinates (o : Operations l E) (m : ℕ)
    {U V Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : U ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] (h : k ≫ p = (𝟙 U) ≫ i) (N : System l E U) :
    let A := scalarRings l E m
    let a := AmbientClopen.transportAlpha (integralNativePullIso l E (𝟙 U))
      (integralNativePullIso l E p) (integralNativeOpenIso l E i (o.extension i))
      (integralNativeOpenIso l E k (o.extension k))
      (VaryingRing.alpha (scalarRings l E) (scalarTransitions l E) k (𝟙 U) p i h)
    (coefficientSequenceDerivedEvaluation l E V m).map (a.app N) ≫
        (rawShriekCoordinates l E o m k).hom.app ((pull l E (𝟙 U)).obj N) ≫
        (StrictTower.moduleJ A k).mapDerivedCategory.map
          ((rawPullCoordinates l E m (𝟙 U)).hom.app N) =
      (rawPullCoordinates l E m p).hom.app ((Operations.shriek l E o i).obj N) ≫
        (StrictTower.modulePullback A p).mapDerivedCategory.map
          ((rawShriekCoordinates l E o m i).hom.app N) ≫
        (singleDerivedAlpha A k (𝟙 U) p i h).app
          ((coefficientSequenceDerivedEvaluation l E U m).obj N) := by
  let C := scalarRings l E
  let τ := scalarTransitions l E
  let r := 𝟙 U
  let si := integralNativeOpenIso l E i (o.extension i)
  let sk := integralNativeOpenIso l E k (o.extension k)
  let pr := integralNativePullIso l E r
  let pp := integralNativePullIso l E p
  let α := VaryingRing.alpha C τ k r p i h
  have h₁ := transportAlpha_evaluation
    (QA := coefficientSequenceDerivedEvaluation l E U m)
    (QB := coefficientSequenceDerivedEvaluation l E Z m)
    (QC := coefficientSequenceDerivedEvaluation l E V m)
    (QD := coefficientSequenceDerivedEvaluation l E U m) si pp pr sk
    (VaryingRing.evalJ C τ i m) (VaryingRing.evalG C τ p m)
    (VaryingRing.evalG C τ r m) (VaryingRing.evalJ C τ k m)
    α (singleDerivedAlpha (C m) k r p i h)
    (native_alpha_evaluation C τ k r p i h m) N
  simpa only [rawShriekCoordinates, rawPullCoordinates, Functor.id_comp, Functor.comp_map,
    Functor.comp_obj, Functor.id_map, Functor.id_obj, C, τ, r, si, sk, pr, pp, α,
    pull, pullbackTensorSequenceDerived, Operations.shriek, Open.derived] using h₁

set_option maxHeartbeats 1600000 in
-- Keep inverse-coefficient conversions separate from the native evaluation calculation.
attribute [local irreducible] integralNativePullIso integralNativeOpenIso
  systemNativePullCoordinates systemNativeShriekCoordinates VaryingRing.evalG VaryingRing.evalJ
  finiteNativePullCoordinates finiteNativeShriekCoordinates in
private theorem native_fixed_alpha_coordinates (o : Operations l E) (m : ℕ)
    {U V Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : U ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] (h : k ≫ p = (𝟙 U) ≫ i) (N : System l E U) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let a := AmbientClopen.transportAlpha (integralNativePullIso l E (𝟙 U))
      (integralNativePullIso l E p) (integralNativeOpenIso l E i (o.extension i))
      (integralNativeOpenIso l E k (o.extension k))
      (VaryingRing.alpha (scalarRings l E) (scalarTransitions l E) k (𝟙 U) p i h)
    (fixedEvaluation l E m V).map (a.app N) ≫
        (systemNativeShriekCoordinates l E o m k).hom.app ((pull l E (𝟙 U)).obj N) ≫
        (ProperOpenShriek A k).map
          ((systemNativePullCoordinates l E m (𝟙 U)).hom.app N) =
      (systemNativePullCoordinates l E m p).hom.app
          ((Operations.shriek l E o i).obj N) ≫
        (ProperOpenPull A p).map
          ((systemNativeShriekCoordinates l E o m i).hom.app N) ≫
        (properOpenAlpha A k (𝟙 U) p i h).app ((fixedEvaluation l E m U).obj N) := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let C := scalarRings l E
  let τ := scalarTransitions l E
  let r := 𝟙 U
  let α := AmbientClopen.transportAlpha (integralNativePullIso l E r)
    (integralNativePullIso l E p) (integralNativeOpenIso l E i (o.extension i))
    (integralNativeOpenIso l E k (o.extension k)) (VaryingRing.alpha C τ k r p i h)
  have h₂ := paste_alpha_squares
    (I := Operations.shriek l E o i) (P := pull l E p)
    (R := pull l E r) (J := Operations.shriek l E o k)
    (I' := (StrictTower.moduleJ (ULift.{u + 1} A) i).mapDerivedCategory)
    (P' := (StrictTower.modulePullback (ULift.{u + 1} A) p).mapDerivedCategory)
    (R' := (StrictTower.modulePullback (ULift.{u + 1} A) r).mapDerivedCategory)
    (J' := (StrictTower.moduleJ (ULift.{u + 1} A) k).mapDerivedCategory)
    (I'' := ProperOpenShriek (ULift.{u + 1} A) i)
    (P'' := ProperOpenPull (ULift.{u + 1} A) p)
    (R'' := ProperOpenPull (ULift.{u + 1} A) r)
    (J'' := ProperOpenShriek (ULift.{u + 1} A) k)
    (EA := coefficientSequenceDerivedEvaluation l E U m)
    (EB := coefficientSequenceDerivedEvaluation l E Z m)
    (EC := coefficientSequenceDerivedEvaluation l E V m)
    (ED := coefficientSequenceDerivedEvaluation l E U m)
    (rawShriekCoordinates l E o m i) (rawPullCoordinates l E m p)
    (rawPullCoordinates l E m r) (rawShriekCoordinates l E o m k)
    (finiteNativeShriekCoordinates A i) (finiteNativePullCoordinates A p)
    (finiteNativePullCoordinates A r) (finiteNativeShriekCoordinates A k)
    α (singleDerivedAlpha (ULift.{u + 1} A) k r p i h)
    (properOpenAlpha (ULift.{u + 1} A) k r p i h)
    (raw_alpha_coordinates l E o m k p i h)
    (finiteNativeAlphaCoordinates A k r p i h) N
  dsimp only [rawShriekCoordinates, rawPullCoordinates, A, C, τ, r, α] at h₂
  simp only [shriek_coordinates_paste l E o m i,
    pull_coordinates_paste l E m p,
    pull_coordinates_paste l E m (𝟙 U),
    shriek_coordinates_paste l E o m k] at h₂
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map, fixedEvaluation,
    fixedEvaluation_obj, input, pull, pullbackTensorSequenceDerived,
    Operations.shriek, Open.derived] using h₂

set_option maxHeartbeats 1600000 in
-- The final rewrite compares the normalized coefficient presentations of all four edges.
attribute [local irreducible] integralNativePullIso integralNativeOpenIso
  systemNativePullCoordinates systemNativeShriekCoordinates in
/-- Exact finite evaluation preserves the identity-left pull/open alpha square.

Source: Stacks 03DI and 0F7B; the finite evaluated proper/open transport in
prop-sf-pf-coherence.proof.md.
Proof: identify the canonical bridge with the section-normalized native bridge,
using its section equation and uniqueness of the two adjoints. Apply native
clopen-arrow evaluation. Its shared single-coefficient arrow is singleDerivedAlpha:
strict-tower evaluation proves equality on constant derived towers, and naturality
along constantEval proves equality on every single-coefficient input. Paste this
native evaluation square with the fixed finite coefficient alpha square, through
the inverse realization equivalences. The pull-coordinate normalization identifies
the pull comparisons. Applying the inverse coefficient functor to the proved native
open evaluation equation identifies the open comparisons directly. A generic
three-level pasting calculation and naturality cancel the bridge inverse pairs.
No faithfulness of derived evaluation is used. Identity maps, empty components and
zero inputs obey the same unit, counit, identity and zero-map equations.
(blueprint: lem-sf-system-finite-alpha-coordinates).
-/
theorem alpha_coordinates (o : Operations l E) (b : CanonicalBridge l E o) (m : ℕ)
    {U V Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : U ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] (h : k ≫ p = (𝟙 U) ≫ i) (N : System l E U) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    (fixedEvaluation l E m V).map ((AmbientClopen.realizationAlpha l E o b k (𝟙 U) p i h).app N) ≫
        (shriekCoordinates l E o m k).hom.app ((pull l E (𝟙 U)).obj N) ≫
        (ProperOpenShriek A k).map ((pullCoordinates l E o m (𝟙 U)).hom.app N) =
      (pullCoordinates l E o m p).hom.app ((Operations.shriek l E o i).obj N) ≫
        (ProperOpenPull A p).map ((shriekCoordinates l E o m i).hom.app N) ≫
        (properOpenAlpha A k (𝟙 U) p i h).app ((fixedEvaluation l E m U).obj N) := by
  simp only [realizationAlpha_native l E o b k (𝟙 U) p i h,
    systemNativeOperationCoordinates l E o m (𝟙 U),
    systemNativeOperationCoordinates l E o m p,
    shriek_coordinates_native l E o m k,
    shriek_coordinates_native l E o m i]
  exact native_fixed_alpha_coordinates l E o m k p i h N

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
