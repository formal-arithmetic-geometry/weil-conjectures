/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.LocallyClosedPairingCancellation
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseProjectiveConstantModels
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedInternalAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyProjectiveCoefficientHom
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorNormalization
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteIsomorphismData

/-! Generator case for the normalized ordinary-etale stage Hom comparison.

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem generator_ordinary_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {S Z X : Scheme.{u}} (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : Etale.DerivedCategoryModule A S)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ (j ≫ g) Q)] :
    IsIso (Etale.CoefficientPairingChange.ordinaryComparison φ g j Q) := by
  let cA := (Etale.rightDerivedLowerStarComp (ModuleCat A) j g).symm.hom.app Q
  let cB := (Etale.rightDerivedLowerStarComp (ModuleCat B) j g).symm.inv.app
    ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (S.smallEtaleTopology) φ).obj Q)
  have : IsIso cA := by dsimp [cA]; infer_instance
  have : IsIso cB := by dsimp [cB]; infer_instance
  let middle := Etale.CoefficientPairingChange.ordinaryComparison φ g j Q
  change IsIso middle
  let dA :=
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).map cA
  have : IsIso dA := by dsimp [dA]; infer_instance
  have hfull : IsIso (dA ≫ (middle ≫ cB)) := by
    have heq : dA ≫ (middle ≫ cB) =
        Etale.finiteCoefficientDirectImageMap φ (j ≫ g) Q := by
      dsimp [dA, middle, Etale.CoefficientPairingChange.ordinaryComparison]
      simpa only [Category.assoc] using
        (Etale.finiteCoefficientDirectImageMap_comp φ j g Q).symm
    rw [heq]
    infer_instance
  have : IsIso (dA ≫ (middle ≫ cB)) := hfull
  have hmiddleRight : IsIso (middle ≫ cB) :=
    IsIso.of_isIso_comp_left dA (middle ≫ cB)
  have : IsIso (middle ≫ cB) := hmiddleRight
  exact IsIso.of_isIso_comp_right middle cB

private theorem generator_transpose_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : Etale.DerivedCategoryModule A X)
    (v : Etale.EtaleHomLeft X φ M ⟶ Etale.EtaleHomRight X φ M)
    (hv : Etale.IsEtaleHomTranspose X φ M v) (K : Etale.DerivedCategoryModule A X) :
    v.app (op K) = Etale.CoefficientPairingChange.evaluationComparison φ X K M := by
  apply ((Etale.derivedTensorHomAdjunction (ModuleCat B)
    ((Etale.scalarExtension φ X).obj K)).homEquiv _ _).symm.injective
  exact (hv K).symm.trans (Equiv.symm_apply_apply _ _).symm

private theorem generator_homMap_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (K M : Sites.D false A X) :
    Sites.homMap false φ X (Etale.ExceptionalCoefficients.tensorIso φ X) K M =
      Etale.CoefficientPairingChange.evaluationComparison φ X K M := by
  apply ((Etale.derivedTensorHomAdjunction (ModuleCat B)
    ((Etale.scalarExtension φ X).obj K)).homEquiv _ _).symm.injective
  dsimp only [Sites.homMap, Sites.scalar, Sites.hom, Sites.adj, Sites.tensor]
  rw [WeilConjectures.finiteHom_scalar_tensor_normalization]
  rfl

/-- The normalized stage Hom comparison is invertible on each flat-model generator.

Proof: identify the normalized tensorator with the canonical etale tensor comparison, transpose
along the etale tensor-Hom adjunction, and use the locally-closed lisse-projective generator
calculation. The generator comparison word has invertible factors: finite projective evaluation,
open and closed exceptional projection, and the ordinary coefficient direct-image comparison.
The transpose uniqueness equation then identifies that word with the displayed `Sites.homMap`.
This statement isolates the generator calculation from the thick-generation argument.
(blueprint: lem-sf-normalized-stage-hom-generator-etale).
-/
theorem normalized_stage_hom_generator_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsNoetherian X]
    {s t : Stage l E} (a : Arrow s t)
    (μ : Sites.TensorComparison false a.ringMap X)
    (hμ : Sites.NormalizedTensor false a.ringMap X μ)
    (M : Sites.D false s.ring X) (hM : Sites.Ctf false s.ring X M)
    (T : Sites.D false s.ring X)
    (hT : ∃ (S : Scheme.{u}) (j : S ⟶ X) (hj : IsImmersion j)
      (L : Sheaf S.smallEtaleTopology (ModuleCat s.ring)),
      FlatModelEtaleLisseProjective s.ring L ∧
        Nonempty (T ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((flatModelEtaleExtension s.ring j hj).obj L))) :
    IsIso (Sites.homMap false a.ringMap X μ T M) := by
  classical
  cases hμ
  obtain ⟨S, b, hb, L, hL, ⟨eT⟩⟩ := hT
  let : IsImmersion b := hb
  let : TopologicalSpace.NoetherianSpace S := b.isEmbedding.isInducing.noetherianSpace
  let g := b.imageι
  let j := b.toImage
  let Z := b.image
  let : Z.Over (Spec (.of D.k)) := ⟨g ≫ X ↘ Spec (.of D.k)⟩
  let : g.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let : S.Over (Spec (.of D.k)) := ⟨j ≫ g ≫ X ↘ Spec (.of D.k)⟩
  let : j.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ X ↘ Spec (.of D.k)))
  have : QuasiCompact (Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ X ↘ Spec (.of D.k)))
  have : LocallyOfFiniteType (S ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ g ≫ X ↘ Spec (.of D.k)))
  have : QuasiCompact (S ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (j ≫ g ≫ X ↘ Spec (.of D.k)))
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : HasInvertibleExponent s.ring X := stageInvertibleExponent D.k D.p l hl s X
  let : HasCompactification g := (Compactification.ofIsProper g).hasCompactification
  let P := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  let N := (Etale.etaleShriekClosedExceptional s.ring g).obj M
  have hNg := Etale.finiteTor_closedExceptional s.ring (X ↘ Spec (.of D.k)) g M hM
  have hN := Etale.finiteTor_restriction s.ring j N hNg
  obtain ⟨hP, hQ, hu⟩ := Etale.locallyProjectiveCoefficientHom a.ringMap S L
    (lisseProjective_constantModels s.ring L hL) _ hN
  have : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap g N) :=
    etale_stage_direct_iso D a.ringMap g N hNg
  have hbg : IsIso (Etale.etaleShriekClosedCoefficientMap a.ringMap g M) := by
    let V : X.Opens := ⟨(Set.range g.base)ᶜ,
      (IsClosedImmersion.isClosedEmbedding g).isClosed_range.isOpen_compl⟩
    have hV : Set.range g.base = (Set.range V.ι.base)ᶜ := by
      rw [Scheme.Opens.range_ι]
      exact (compl_compl _).symm
    let : V.toScheme.Over (Spec (.of D.k)) := ⟨V.ι ≫ X ↘ Spec (.of D.k)⟩
    let : V.ι.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of D.k)))
    have : QuasiCompact (V.toScheme ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact (V.ι ≫ X ↘ Spec (.of D.k)))
    have := etale_stage_direct_iso D a.ringMap V.ι _
      (Etale.finiteTor_restriction s.ring V.ι M hM)
    exact Etale.closedCoefficient_isIso a.ringMap g V.ι hV M
  have : IsIso (Etale.etaleShriekClosedCoefficientMap a.ringMap g M) := hbg
  have hb' : IsIso (Etale.etaleShriekLocallyClosedCoefficientMap a.ringMap g j M) := by
    dsimp only [Etale.etaleShriekLocallyClosedCoefficientMap]
    infer_instance
  have : IsIso (Etale.CoefficientPairingChange.evaluationComparison a.ringMap S P
      ((Etale.CoefficientPairingChange.exceptional s.ring g j).obj M)) := hu
  have hq : IsIso (Etale.CoefficientPairingChange.compactComparison a.ringMap g j P) := by
    have := etale_stage_direct_iso D a.ringMap g _
      (Etale.finiteTor_extension s.ring j P hP)
    dsimp only [Etale.CoefficientPairingChange.compactComparison]
    infer_instance
  have : IsIso (Etale.etaleShriekLocallyClosedCoefficientMap a.ringMap g j M) := hb'
  have : IsIso (Etale.CoefficientPairingChange.compactComparison a.ringMap g j P) := hq
  have hc : IsIso (Etale.CoefficientPairingChange.ordinaryComparison a.ringMap g j
      (((Etale.derivedHom (ModuleCat s.ring) S).obj (op P)).obj
        ((Etale.CoefficientPairingChange.exceptional s.ring g j).obj M))) := by
    have : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap (j ≫ g)
        (((Etale.derivedHom (ModuleCat s.ring) S).obj (op P)).obj
          ((Etale.CoefficientPairingChange.exceptional s.ring g j).obj M))) :=
      etale_stage_direct_iso D a.ringMap (j ≫ g) _ hQ
    exact generator_ordinary_iso a.ringMap g j _
  have hI := Etale.locallyClosedInternalAdjunction_isIso s.ring g j P M
  have : IsIso (Etale.CoefficientPairingChange.ordinaryComparison a.ringMap g j
      (((Etale.derivedHom (ModuleCat s.ring) S).obj (op P)).obj
        ((Etale.CoefficientPairingChange.exceptional s.ring g j).obj M))) := hc
  have hIB := Etale.locallyClosedInternalAdjunction_isIso t.ring g j
    ((Etale.scalarExtension a.ringMap S).obj P) ((Etale.scalarExtension a.ringMap X).obj M)
  have hCounit : Etale.CoefficientPairingChange.CounitCompatible a.ringMap g j M
      (asIso (Etale.etaleShriekLocallyClosedCoefficientMap a.ringMap g j M)) := by
    simpa only [Etale.CoefficientPairingChange.CounitCompatible,
      Etale.CoefficientPairingChange.compactComparison, Etale.etaleShriekLocallyClosedSupportMap,
      asIso_hom, Etale.CoefficientPairingChange.counit,
      Etale.etaleShriekLocallyClosedAdjunction, Etale.etaleShriekClosedAdjunction,
      Etale.CoefficientPairingChange.shriek, Etale.CoefficientPairingChange.exceptional,
      Etale.etaleShriekClosedExceptional, Functor.comp_obj] using
      Etale.locallyClosedCoefficient_counit a.ringMap g j M
  have hp := Etale.CoefficientPairingChange.pairing_change a.ringMap g j P M
    (asIso (Etale.etaleShriekLocallyClosedCoefficientMap a.ringMap g j M)) hCounit
  have : IsIso (Etale.CoefficientPairingChange.internalAdjunction s.ring g j P M) := hI
  have : IsIso (Etale.CoefficientPairingChange.internalAdjunction t.ring g j
      ((Etale.scalarExtension a.ringMap S).obj P)
      ((Etale.scalarExtension a.ringMap X).obj M)) := hIB
  have hEq := Etale.CoefficientPairingChange.pairingCancellation a.ringMap g j P M hp
  have hi : IsIso (Etale.CoefficientPairingChange.evaluationComparison a.ringMap X
      ((Etale.CoefficientPairingChange.shriek s.ring g j).obj P) M) := by
    unfold MappedComparisonEquation at hEq
    rw [← hEq]
    infer_instance
  obtain ⟨v, hv, _⟩ := Etale.etaleHomComparison_thickLocus X a.ringMap
  have he (K : Sites.D false s.ring X) :
      (v M).app (op K) = Etale.CoefficientPairingChange.evaluationComparison
        a.ringMap X K M :=
    generator_transpose_evaluation X a.ringMap M (v M) (hv M).1 K
  let e : (Etale.CoefficientPairingChange.shriek s.ring g j).obj P ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((flatModelEtaleExtension s.ring b hb).obj L) :=
    (Etale.lowerStar (ModuleCat s.ring) g).rightDerivedFunctor.mapIso
      (((Etale.openImmersionLowerShriek (ModuleCat s.ring) j).mapDerivedCategorySingleFunctor
        0).app L) ≪≫
      ((Etale.lowerStar (ModuleCat s.ring) g).singleFunctorCompRightDerivedFunctorIso).app _
  have hiT : IsIso ((v M).app (op T)) := by
    apply (v M).isIso_app_iff_of_iso (eT ≪≫ e.symm).op |>.mp
    rw [he]
    exact hi
  have htrans := generator_homMap_evaluation X a.ringMap T M
  change IsIso (Sites.homMap false a.ringMap X
    (Etale.ExceptionalCoefficients.tensorIso a.ringMap X) T M)
  rw [htrans]
  have hiT' : IsIso (Etale.CoefficientPairingChange.evaluationComparison
      a.ringMap X T M) := by
    rw [← he]
    exact hiT
  exact hiT'

end WeilConjectures.FiniteFreeCoefficients
