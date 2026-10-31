/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.ClosedScalarDomains
import all WeilConjectures.AlgebraicGeometry.PurityAffineChartBounds
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Adjunction
import all WeilConjectures.AlgebraicGeometry.FiniteClosedRealizationDomain
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

variable {A B : Type u} [CommRing A] [CommRing B]

abbrev splitCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

abbrev splitDerived (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

abbrev splitScalar {A B : Type u} [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B) (T : Scheme.{u}) :
    splitDerived T A ⥤ splitDerived T B :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _ _ _ φ

abbrev splitPush (A : Type u) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    splitDerived Z A ⥤ splitDerived X A :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).rightDerivedFunctor

abbrev splitExceptional (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ProEtale.sfFiniteExceptionalFixed A (Compactification.ofIsProper i)

def splitCounit (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A) :
    (splitPush A i).obj ((splitExceptional A i).obj M) ⟶ M := by
  letI := (Compactification.ofIsProper i).hasCompactification
  exact
    open Classical in
    if hX : CompactSpace X then
      letI := hX
      if hM : DerivedCategory.TStructure.t.plus M then
        (ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).inv.app _ ≫
          ProEtale.rightDerivedUpperShriekCounit i M hM
      else 0
    else 0

def splitDirectInverse {A B : Type u} [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (N : splitDerived Z A) :
    (splitPush B i).obj ((splitScalar φ Z).obj N) ⟶
      (splitScalar φ X).obj ((splitPush A i).obj N) :=
  open Classical in
  if h : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) then
    @inv _ _ _ _ (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) h
  else 0

def splitIsMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A)
    (b : (splitScalar φ Z).obj ((splitExceptional A i).obj M) ⟶
      (splitExceptional B i).obj ((splitScalar φ X).obj M)) : Prop :=
  (splitPush B i).map b ≫
      splitCounit B i ((splitScalar φ X).obj M) =
    splitDirectInverse φ i ((splitExceptional A i).obj M) ≫
      (splitScalar φ X).map (splitCounit A i M)

def splitMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A) :
    (splitScalar φ Z).obj ((splitExceptional A i).obj M) ⟶
      (splitExceptional B i).obj ((splitScalar φ X).obj M) :=
  open Classical in
  if h : ∃! b, splitIsMap φ i M b then h.exists.choose else 0

private theorem splitFixed_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) (K : splitDerived T (splitCoefficient l E n)) :
    finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) T K ↔
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E n))) T K := by
  constructor
  · intro hK
    obtain ⟨a, b, ht⟩ := hK.2
    exact ⟨(finiteClosed_intrinsic_bc_realization_iff l E (n + 1) (Nat.succ_pos n) T K).1 hK.1,
      a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
        (splitCoefficient l E n) T a b ht.1 K).1 ht⟩
  · rintro ⟨hbc, a, b, ht⟩
    have hab : a ≤ b ∨ b < a := le_or_gt a b
    rcases hab with hab | hab
    · exact ⟨(finiteClosed_intrinsic_bc_realization_iff l E (n + 1) (Nat.succ_pos n) T K).2 hbc,
        a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
          (splitCoefficient l E n) T a b hab K).2 ht⟩
    · have ht' : ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E n))) T
          (min a b) (max a b) K :=
        ProEtale.DerivedCategory.torAmplitudeIn.mono
          (min_le_left _ _) (le_max_right _ _) ht
      exact ⟨(finiteClosed_intrinsic_bc_realization_iff l E (n + 1) (Nat.succ_pos n) T K).2 hbc,
        min a b, max a b,
        (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
          (splitCoefficient l E n) T _ _ (min_le_max) K).2 ht'⟩

private theorem splitScalar_preserves
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L] (m n : ℕ)
    (φ : ULift.{u + 1, u} (splitCoefficient l E m) →+*
      ULift.{u + 1, u} (splitCoefficient l L n))
    (T : Over (Spec (.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (K : splitDerived T.left (splitCoefficient l E m))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E m))) T.left K) :
    ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l L n))) T.left
      ((splitScalar φ T.left).obj K) := by
  have hi := (splitFixed_iff l E m T.left K).2 hK
  obtain ⟨a, b, ht⟩ := hi.2
  let ψ : splitCoefficient l E m →+* splitCoefficient l L n :=
    ULift.ringEquiv.toRingHom.comp (φ.comp ULift.ringEquiv.symm.toRingHom)
  have hφ : ψ.ulift.{u + 1, u + 1} = φ := by ext x; rfl
  have hs := (closedScalarDomains_scalar D l hl E L m n ψ T a b ht.1 K hi ht).1.1
  rw [splitFixed_iff] at hs
  simpa only [closedScalarExtension, hφ] using hs

private theorem splitDirect_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m : ℕ) {B : Type u} [CommRing B] [Finite B]
    (φ : ULift.{u + 1, u} (splitCoefficient l E m) →+* ULift.{u + 1, u} B)
    (T X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : splitDerived T.left (splitCoefficient l E m))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E m))) T.left K) :
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ f.left K) := by
  let := φ.toAlgebra
  have : Module.Finite (ULift.{u + 1, u} (splitCoefficient l E m))
      (ULift.{u + 1, u} B) := Module.Finite.of_finite
  obtain ⟨Q, hQ, ⟨e⟩⟩ := hK.1
  obtain ⟨a, b, ht⟩ := hK.2
  have hQt := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory
    (ULift.{u + 1, u} (splitCoefficient l E m))
    ((ProEtale.DerivedCategory.torAmplitudeIn _ T.left a b).prop_of_iso e.symm ht)
  have hqi : finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) T.left Q := by
    refine ⟨(finiteClosed_etale_bc_iff _ T.left Q).2 hQ, ?_⟩
    exact ⟨min a b, max a b, min_le_max,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) (le_max_right _ _) hQt)⟩
  have hc := ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso
    D l hl E (m + 1) (Nat.succ_pos m) (ULift.{u + 1, u} B) T X f Q hqi.1 hqi.2
  have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ f.left
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E m)))
          T.left).mapDerivedCategory.obj Q)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (by infer_instance) hc
  have hn := ProEtale.finiteCoefficientDirectImageMap_naturality φ f.left e.hom
  have hiso : IsIso ((splitScalar φ X.left).map ((splitPush _ f.left).map e.hom) ≫
      ProEtale.finiteCoefficientChangeDirectImageMap φ f.left K) := by
    rw [hn]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (by infer_instance) hiso

private theorem splitCounit_bijective (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    {K : splitDerived Z A} {M : splitDerived X A}
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z K)
    (hM : DerivedCategory.TStructure.t.plus M) :
    Function.Bijective (fun b : K ⟶ (splitExceptional A i).obj M ↦
      (splitPush A i).map b ≫ splitCounit A i M) := by
  let := (Compactification.ofIsProper i).hasCompactification
  let e := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
  have eqn (b : K ⟶ (splitExceptional A i).obj M) :
      (splitPush A i).map b ≫ splitCounit A i M =
        e.inv.app K ≫ (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM).symm b := by
    simp only [splitCounit, dif_pos (inferInstance : CompactSpace X), dif_pos hM]
    erw [← Category.assoc, e.inv.naturality]
    simp only [ProEtale.rightDerivedUpperShriekHomEquiv_symm_apply, Category.assoc]
  simp_rw [eqn]
  exact (e.app K).homFromEquiv.bijective.comp
    (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM).symm.bijective

private theorem splitCounit_triangle (A : Type u) [CommRing A] [Finite A]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [CompactSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0)
    (hA : (N : ULift.{u + 1, u} A) = 0) (s : X ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s]
    (M : splitDerived X A)
    (hM : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X M) :
    ∃ w, Triangle.mk (splitCounit A i M)
      ((ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app M) w ∈
      distTriang _ := by
  let := (Compactification.ofIsProper i).hasCompactification
  let a := ProEtale.derivedLowerStarClosedUpperShriekAdjunction
    (R := ULift.{u + 1, u} A) i j hij
  let K := (ProEtale.closedUpperShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i j).rightDerivedFunctor.obj M
  have hK := (ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj
    i j N hN hA s hij hM).plusEtaleOrigin
  have hM' := hM.plusEtaleOrigin.plus
  have hJ := ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj i hM'
  let e := ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek i j hij hK hM'
  let e' := ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek i j hij hJ hM'
  let b : K ≅ (splitExceptional A i).obj M :=
    { hom := e (𝟙 _)
      inv := e'.symm (𝟙 _)
      hom_inv_id := by
        apply e.injective
        change e (e (𝟙 _) ≫ e'.symm (𝟙 _)) = e (𝟙 _)
        rw [ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek_naturality
          i j hij hK hJ hM', Equiv.apply_symm_apply, Category.comp_id]
      inv_hom_id := by
        change e'.symm (𝟙 _) ≫ e (𝟙 _) = 𝟙 _
        rw [← ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek_naturality
          i j hij hJ hK hM', Category.comp_id]
        exact e'.apply_symm_apply _ }
  have hb : (splitPush A i).map b.hom ≫ splitCounit A i M = a.counit.app M := by
    let t := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
    have he := (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM').symm_apply_apply
      (t.hom.app K ≫ a.counit.app M)
    have hb' : b.hom = (ProEtale.rightDerivedUpperShriekHomEquiv i hK hM')
        (t.hom.app K ≫ a.counit.app M) := by
      dsimp [b, e, ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek]
      simp only [Adjunction.homEquiv_counit, Iso.homFromEquiv_symm_apply]
      congr 1
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    rw [← hb'] at he
    simp only [ProEtale.rightDerivedUpperShriekHomEquiv_symm_apply] at he
    simp only [splitCounit, dif_pos (inferInstance : CompactSpace X), dif_pos hM']
    erw [← Category.assoc, t.inv.naturality, Category.assoc, he]
    simp only [← Category.assoc, t.inv_hom_id_app, Category.id_comp]
  obtain ⟨w, hw⟩ :=
    ProEtale.exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit i j hij M
  let T := ProEtale.closedSupportTriangle i j hij M w
  let T' := Triangle.mk (splitCounit A i M)
    ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app M)
    (w ≫ ((splitPush A i).map b.hom)⟦(1 : ℤ)⟧')
  refine ⟨_, CategoryTheory.Pretriangulated.isomorphic_distinguished
    T hw T' (Triangle.isoMk T T' ((splitPush A i).mapIso b)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_).symm⟩
  · change a.counit.app M ≫ 𝟙 _ = (splitPush A i).map b.hom ≫ splitCounit A i M
    simpa only [Category.comp_id] using hb.symm
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · simp [T', T]

private theorem splitTriangle_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : D ⥤ C) [F.Full] [F.Faithful] {K L : D} (T : Triangle C)
    {N : C} (ε : F.obj L ⟶ T.obj₂) (η : T.obj₂ ⟶ N)
    (δ : N ⟶ (F.obj L)⟦(1 : ℤ)⟧)
    (hT : T ∈ distTriang C) (hB : Triangle.mk ε η δ ∈ distTriang C)
    (d : T.obj₁ ⟶ F.obj K) [IsIso d] (v : T.obj₃ ⟶ N) [IsIso v]
    (hv : T.mor₂ ≫ v = η) (b : K ⟶ L)
    (hb : (d ≫ F.map b) ≫ ε = T.mor₁)
    (hz : Subsingleton ((F.obj K)⟦(1 : ℤ)⟧ ⟶ N)) : IsIso b := by
  have := hz
  let B := Triangle.mk ε η δ
  obtain ⟨a, ha, ha'⟩ := complete_distinguished_triangle_morphism₁ T B hT hB
    (𝟙 _) v (by
      change T.mor₂ ≫ v = 𝟙 _ ≫ η
      simpa only [Category.id_comp] using hv)
  let t : T ⟶ B :=
    { hom₁ := a
      hom₂ := 𝟙 _
      hom₃ := v
      comm₁ := ha
      comm₂ := by
        change T.mor₂ ≫ v = 𝟙 _ ≫ η
        simpa only [Category.id_comp] using hv
      comm₃ := ha' }
  have haIso : IsIso a := isIso₁_of_isIso₂₃ t hT hB (by dsimp [t]; infer_instance)
    (by dsimp [t]; infer_instance)
  have hzT : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ N) :=
    Equiv.subsingleton (((shiftFunctor C (1 : ℤ)).mapIso (asIso d)).homFromEquiv)
  have : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ B.obj₃) := by
    change Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ N)
    exact hzT
  have heq : d ≫ F.map b = a := by
    apply Triangle.cancel_mor₁_of_subsingleton (T := B) hB
    change (d ≫ F.map b) ≫ ε = a ≫ ε
    change T.mor₁ ≫ 𝟙 _ = a ≫ ε at ha
    exact hb.trans (by simpa only [Category.comp_id] using ha)
  have : IsIso (d ≫ F.map b) := heq.symm ▸ haIso
  have : IsIso (F.map b) := IsIso.of_isIso_comp_left d _
  exact isIso_of_reflects_iso b F

attribute [local irreducible] ProEtale.finiteCoefficientChangeDirectImageMap

private theorem splitMap_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (splitCoefficient l E m) →+*
      ULift.{u + 1, u} (splitCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : splitDerived X.left (splitCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M)
    (hc : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((splitExceptional (splitCoefficient l E m) i.left).obj M)))
    (hmap : splitIsMap φ i.left M (splitMap φ i.left M)) :
    IsIso (splitMap φ i.left M) := by
  classical
  let := (Compactification.ofIsProper i.left).hasCompactification
  let := datum_charP D
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hlk : (l : D.k) ≠ 0 := by
    intro h
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).mp
      ((CharP.cast_eq_zero_iff D.k D.p l).mp h)).symm
  have hMf := (splitFixed_iff l E m X.left M).1 _hM
  have hMb := splitScalar_preserves D l _hl E L m n φ X M hMf
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let U : X.left.Opens :=
    ⟨(Set.range i.left.base)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := U.ι
  have hij : IsCompl (Set.range i.left.base) (Set.range j.base) := by
    change IsCompl _ (Set.range U.ι.base)
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have hAc : ((l ^ (m + 1) : ℕ) : ULift.{u + 1, u} (splitCoefficient l E m)) = 0 := by
    apply ULift.down_injective
    exact coefficient_killed l E (m + 1)
  have hBc : ((l ^ (n + 1) : ℕ) : ULift.{u + 1, u} (splitCoefficient l L n)) = 0 := by
    apply ULift.down_injective
    exact coefficient_killed l L (n + 1)
  obtain ⟨wA, hwA⟩ := splitCounit_triangle (splitCoefficient l E m) i.left j hij
    (l ^ (m + 1)) (by simpa only [Nat.cast_pow] using pow_ne_zero (m + 1) hlk)
    hAc X.hom M hMf.1
  obtain ⟨wB, hwB⟩ := splitCounit_triangle (splitCoefficient l L n) i.left j hij
    (l ^ (n + 1)) (by simpa only [Nat.cast_pow] using pow_ne_zero (n + 1) hlk)
    hBc X.hom ((splitScalar φ X.left).obj M) hMb.1
  let adj := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} X.left.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X.left) _ _ _ _ φ)
  let : (@Sheaf.derivedRestrictScalars.{u} X.left.ProEt
      inferInstance (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X.left)
      _ _ _ _ φ).leftAdjoint.CommShift ℤ := adj.leftAdjointCommShift ℤ
  let : (splitScalar φ X.left).CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : (splitScalar φ X.left).IsTriangulated := adj.isTriangulated_leftAdjoint
  let aA := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E m))) j
  let aB := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l L n))) j
  let e := ProEtale.scalarPullbackProEtaleIso φ j
  let J : Over (Spec (.of D.k)) := Over.mk (j ≫ X.hom)
  have : LocallyOfFiniteType J.hom :=
    show LocallyOfFiniteType (j ≫ X.hom) from inferInstance
  have : QuasiCompact J.hom :=
    show QuasiCompact (j ≫ X.hom) from inferInstance
  let f : J ⟶ X := Over.homMk j
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hJ := ProEtale.constructibleFiniteTor_leftDerivedFunctor_upperStar_obj j hMf
  have hco := splitDirect_isIso D l _hl E m φ J X f _ hJ
  have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ j _ ) := hco
  let c := ProEtale.finiteCoefficientChangeDirectImageMap φ j
    ((ProEtale.upperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (splitCoefficient l E m))) j).leftDerivedFunctor.obj M)
  let v := c ≫ (splitPush (splitCoefficient l L n) j).map (e.inv.app M)
  have hv : IsIso v := by dsimp [v, c]; infer_instance
  have hunit : (splitScalar φ X.left).map (aA.unit.app M) ≫ v =
      aB.unit.app ((splitScalar φ X.left).obj M) := by
    have h := unit_mateEquiv aA aB (TwoSquare.mk _ _ _ _ e.hom) M
    change (splitScalar φ X.left).map (aA.unit.app M) ≫
      ((mateEquiv aA aB (TwoSquare.mk _ _ _ _ e.hom)).natTrans.app _) =
      aB.unit.app _ ≫ (splitPush (splitCoefficient l L n) j).map (e.hom.app M) at h
    rw [← ProEtale.finiteCoefficientDirectImageMap_eq_mate φ j] at h
    dsimp only [v, c]
    rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp]
    erw [e.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  let TA := Triangle.mk (splitCounit (splitCoefficient l E m) i.left M) (aA.unit.app M) wA
  let T := (splitScalar φ X.left).mapTriangle.obj TA
  have hT : T ∈ distTriang _ := (splitScalar φ X.left).map_distinguished TA hwA
  have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((splitExceptional (splitCoefficient l E m) i.left).obj M)) := hc
  let d := ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
    ((splitExceptional (splitCoefficient l E m) i.left).obj M)
  have hz := ProEtale.subsingleton_hom_shift_rightDerivedFunctor_lowerStar
    (R := ULift.{u + 1, u} (splitCoefficient l L n)) i.left j hij
    ((splitScalar φ Z.left).obj ((splitExceptional (splitCoefficient l E m) i.left).obj M))
    ((ProEtale.upperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (splitCoefficient l L n))) j).leftDerivedFunctor.obj
        ((splitScalar φ X.left).obj M)) (1 : ℤ)
  refine splitTriangle_isIso (splitPush (splitCoefficient l L n) i.left) T
    (splitCounit (splitCoefficient l L n) i.left ((splitScalar φ X.left).obj M))
    (aB.unit.app ((splitScalar φ X.left).obj M)) wB hT hwB d v ?_
      (splitMap φ i.left M) ?_ ?_
  · exact hunit
  · have hnormal := hmap
    dsimp only [splitIsMap, splitDirectInverse] at hnormal
    rw [dif_pos hc] at hnormal
    change (d ≫ (splitPush (splitCoefficient l L n) i.left).map
      (splitMap φ i.left M)) ≫ splitCounit (splitCoefficient l L n) i.left
        ((splitScalar φ X.left).obj M) =
      (splitScalar φ X.left).map (splitCounit (splitCoefficient l E m) i.left M)
    rw [Category.assoc, hnormal, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫
      (splitScalar φ X.left).map (splitCounit (splitCoefficient l E m) i.left M))
      (IsIso.hom_inv_id d) |>.trans (Category.id_comp _)
  · exact hz

/-- The counit-normalized map and its ordinary direct-image comparison are the
strictly algebraic part of the closed coefficient argument. The geometric finite-
Tor domain assertions are recorded separately in `FiniteClosedShriekDomainPart`.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
proof paragraph 2 (blueprint: lem-coef-finite-closed-shriek). -/
theorem finiteClosedShriek_mapPart
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (splitCoefficient l E m) →+*
      ULift.{u + 1, u} (splitCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : splitDerived X.left (splitCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (∃! b, splitIsMap φ i.left M b) ∧
    splitIsMap φ i.left M (splitMap φ i.left M) ∧
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((splitExceptional (splitCoefficient l E m) i.left).obj M)) ∧
    IsIso (splitMap φ i.left M) := by
  classical
  let := (Compactification.ofIsProper i.left).hasCompactification
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : HasInvertibleExponent (ULift.{u + 1, u} (splitCoefficient l E m)) X.left :=
    coefficient_invertible D l _hl E (m + 1) X.left X.hom
  have : HasInvertibleExponent (ULift.{u + 1, u} (splitCoefficient l L n)) X.left :=
    coefficient_invertible D l _hl L (n + 1) X.left X.hom
  have hMf := (splitFixed_iff l E m X.left M).1 _hM
  have hMb := splitScalar_preserves D l _hl E L m n φ X M hMf
  have hN : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (splitCoefficient l E m))) Z.left
      ((splitExceptional (splitCoefficient l E m) i.left).obj M) :=
    ProEtale.constructibleFiniteTor_rightDerivedUpperShriek
      (ULift.{u + 1, u} (splitCoefficient l E m)) X.hom i.left hMf
  have hNb := splitScalar_preserves D l _hl E L m n φ Z _ hN
  have hc := splitDirect_isIso D l _hl E m φ Z X i _ hN
  have hbij := splitCounit_bijective (splitCoefficient l L n) i.left hNb.1.plusEtaleOrigin
    hMb.1.plusEtaleOrigin.plus
  obtain ⟨b, hb⟩ := hbij.2
    (splitDirectInverse φ i.left ((splitExceptional (splitCoefficient l E m) i.left).obj M) ≫
      (splitScalar φ X.left).map (splitCounit (splitCoefficient l E m) i.left M))
  have hex : ∃! b, splitIsMap φ i.left M b :=
    ⟨b, hb, fun b' hb' ↦ hbij.1 (hb'.trans hb.symm)⟩
  have hmap : splitIsMap φ i.left M (splitMap φ i.left M) := by
    simp only [splitMap, dif_pos hex]
    exact hex.exists.choose_spec
  refine ⟨hex, hmap, hc, ?_⟩
  exact splitMap_isIso D l _hl E L m n φ X Z i M _hM hc hmap

end WeilConjectures
