/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomOrdinaryTranspose
import WeilConjectures.AlgebraicGeometry.Lisse.LisseProjectiveConstantModels
import WeilConjectures.AlgebraicGeometry.LocallyClosedHomGenerator.LocallyClosedHomGenerator
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory

/-! # Invertibility of finite coefficient Hom change on the etale site
Source: blueprint thm-coef-finite-hom, generator and thick-locus argument
(blueprint: lem-coef-finite-hom-etale-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem finiteChange_nativeTranspose
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : Etale.DerivedCategoryModule A X)
    (v : Etale.EtaleHomLeft X φ M ⟶ Etale.EtaleHomRight X φ M)
    (hv : Etale.IsEtaleHomTranspose X φ M v) (K : Etale.DerivedCategoryModule A X) :
    v.app (op K) = Etale.CoefficientPairingChange.evaluationComparison φ X K M := by
  apply ((Etale.derivedTensorHomAdjunction (ModuleCat B)
    ((Etale.scalarExtension φ X).obj K)).homEquiv _ _).symm.injective
  exact (hv K).symm.trans (Equiv.symm_apply_apply _ _).symm

private theorem finiteChangeWord_isIso
    {C D : Type*} [Category C] [Category D] {U V : C}
    (i : U ⟶ V) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) (z : X₀ ⟶ X₆)
    (hz : NormalizedComparisonWord i a b c d e f z) : IsIso z := by
  obtain ⟨_, ha, hb, hc, hd, he, hf, hz⟩ := hz
  let := ha
  let := hb
  let := hc
  let := hd
  let := he
  let := hf
  rw [← hz]
  infer_instance

private theorem finiteChangeMappedWord_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    {U V : C} (i : U ⟶ V) [hi : IsIso i] {P Q R : E}
    (b : F.obj U ⟶ G.obj P) (c : P ⟶ Q) (d : Q ⟶ R)
    {Y Y' : D} (q : Y ⟶ Y') (M : D)
    (e : G.obj R ⟶ (H.obj (op Y')).obj M)
    (z : F.obj V ⟶ (H.obj (op Y)).obj M)
    (hz : MappedComparisonWord F G H i b c d q M e z) : IsIso z :=
  finiteChangeWord_isIso _ _ _ _ _ _ _ _ hz

private theorem finiteChange_thick
    {C : Type a} [Category.{b} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (Q : ObjectProperty C)
    (hz : ∀ K, IsZero K → Q K)
    (hs : ∀ K (n : ℤ), Q K → Q (K⟦n⟧))
    (ht : ∀ T : Triangle C, T ∈ distTriang C → Q T.obj₁ → Q T.obj₂ → Q T.obj₃)
    (hr : ∀ {K L : C} (i : K ⟶ L) (r : L ⟶ K), i ≫ r = 𝟙 K → Q L → Q K) :
    Q.IsTriangulated ∧ Q.IsStableUnderRetracts := by
  let : Q.IsStableUnderRetracts := ⟨fun r h ↦ hr r.i r.r r.retract h⟩
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
  let : Q.ContainsZero := ⟨Z, hZ, hz _ hZ⟩
  let : Q.IsStableUnderShift ℤ := ⟨fun n ↦ .mk (fun K h ↦ hs K n h)⟩
  let : Q.IsTriangulatedClosed₃ := .mk' ht
  let : Q.IsTriangulatedClosed₂ := .of_isTriangulatedClosed₃
  exact ⟨{}, inferInstance⟩

private theorem finiteChange_of_generators
    {C : Type a} [Category.{b} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (Q : ObjectProperty Cᵒᵖ)
    (hz : ∀ K, IsZero K → Q K)
    (hs : ∀ K (n : ℤ), Q K → Q (K⟦n⟧))
    (ht : ∀ T : Triangle Cᵒᵖ, T ∈ distTriang Cᵒᵖ → Q T.obj₁ → Q T.obj₂ → Q T.obj₃)
    (hr : ∀ {K L : Cᵒᵖ} (i : K ⟶ L) (r : L ⟶ K), i ≫ r = 𝟙 K → Q L → Q K)
    (G : ObjectProperty C) (hg : G ≤ Q.unop) {K : C}
    (hK : G.triangEnvelope K) : Q (op K) := by
  have hq := finiteChange_thick Q hz hs ht hr
  let := hq.1
  let := hq.2
  let : Q.unop.IsStableUnderRetracts :=
    ⟨fun r ht ↦ Q.prop_of_retract
      { i := r.r.op, r := r.i.op, retract := by
          simpa only [op_comp, op_id] using congrArg Quiver.Hom.op r.retract } ht⟩
  exact ((ObjectProperty.triangEnvelope_le_iff (Q := Q.unop) G).mpr hg) K hK

/-- The evaluation-defined comparison is invertible on all finite-Tor constructible pairs.
Source: blueprint thm-coef-finite-hom, proof paragraphs 2--4
(blueprint: lem-coef-finite-hom-etale-iso).

Proof: use the evaluation-normalized thick locus for fixed M. Each locally closed
lisse projective generator has the six-factor normalized comparison word, so its
comparison is invertible. Exact open extension and exact closed pushforward identify
the sheaf and derived generator conventions. Thick generation then covers K. The
ordinary-transpose normalization identifies this comparison with the prescribed arrow.
-/
theorem finiteHomEtale_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n) (K M : finiteHomEtale l E X n)
    (hK : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K)
    (hM : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M) :
    IsIso (etaleFiniteHomCanonical l E X h K M) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let B := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))
  let φ := finiteHomQuotient l E h
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  let : IsNoetherian X := by
    have : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (.of D.k))
    exact ⟨⟩
  obtain ⟨v, hv, _⟩ := Etale.etaleHomComparison_thickLocus X φ
  have he (T : finiteHomEtale l E X n) :
      (v M).app (op T) = Etale.CoefficientPairingChange.evaluationComparison φ X T M := by
    exact finiteChange_nativeTranspose X φ M (v M) (hv M).1 T
  let Q : ObjectProperty (finiteHomEtale l E X n)ᵒᵖ := fun T ↦ IsIso ((v M).app T)
  have hg : (fun T : finiteHomEtale l E X n ↦
      ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
        (L : Sheaf S.smallEtaleTopology (ModuleCat A)),
        FlatModelEtaleLisseProjective A L ∧
        Nonempty (T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension A a ha).obj L))) ≤ Q.unop := by
    rintro T ⟨S, a, ha, L, hL, ⟨eT⟩⟩
    let : IsImmersion a := ha
    let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
    have hword := (Etale.LocallyClosedHomGenerator.normalizedComparison D l hl E
      ⟨n + 1, Nat.succ_pos n⟩ ⟨m + 1, Nat.succ_pos m⟩ (Nat.succ_le_succ h)
      a.imageι a.toImage L (lisseProjective_constantModels A L hL) M hM).2.2
    have hi : IsIso (Etale.CoefficientPairingChange.evaluationComparison φ X
        ((Etale.CoefficientPairingChange.shriek A a.imageι a.toImage).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) M) :=
      finiteChangeMappedWord_isIso (hi := hword.1) _ _ _ _ _ _ _ _ _ _ _ hword
    let j := Etale.openImmersionLowerShriek (ModuleCat A) a.toImage
    let g := Etale.lowerStar (ModuleCat A) a.imageι
    let e : (Etale.CoefficientPairingChange.shriek A a.imageι a.toImage).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension A a ha).obj L) :=
      g.rightDerivedFunctor.mapIso ((j.mapDerivedCategorySingleFunctor 0).app L) ≪≫
        (g.singleFunctorCompRightDerivedFunctorIso).app (j.obj L)
    apply (v M).isIso_app_iff_of_iso (eT ≪≫ e.symm).op |>.mp
    rw [he]
    exact hi
  have hgen := congrFun (etale_flatConstructible_thickGeneration X A) K
  have hmem : ObjectProperty.triangEnvelope _ K := Eq.mp hgen ⟨hK.1.1, hK.1.2, hK.2⟩
  have hi : IsIso ((v M).app (op K)) :=
    finiteChange_of_generators Q (hv M).2.2.1 (hv M).2.2.2.2.1
      (hv M).2.2.2.2.2.1 (hv M).2.2.2.2.2.2 _ hg hmem
  rw [he] at hi
  exact Eq.mpr (congrArg
    (fun z : Arrow (finiteHomEtale l E X m) ↦ IsIso z.hom)
    (finiteHom_ordinary_transpose l E X h K M)) hi

end WeilConjectures
