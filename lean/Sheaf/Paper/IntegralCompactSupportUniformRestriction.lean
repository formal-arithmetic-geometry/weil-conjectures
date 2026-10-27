/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.UniformCompleteTriangulated
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ProperBaseChangeFourCorners
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Category.Ring.Basic
import all Sheaf.Paper.PbcScalarExtension
import all Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import all Sheaf.Paper.ExtensionZeroStratifiedPerfect
import all Sheaf.Paper.ExtensionZeroPerfectModelTransport
import Sheaf.Paper.IntegralPadicLocalPerfectCriterion
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.CompleteCompactSupportProetale
import Sheaf.Paper.CompletedConstructiblePreservation
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Integral compact support preserves the compatible uniform constructible category

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-extension,
proof, sole paragraph; Stacks Tags 0GL0 and 095U; Bhatt--Scholze, Lemmas 6.7.2 and 6.7.7
(blueprint: lem-cbc-integral-compact-support-uniform-restriction).

The three functor properties below are tested on the full compatible uniform subcategory.
Fullness gives the restricted functor, and its triangles and shifts are inherited.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme

/-- Canonical completed-coefficient inverse image, reusing the published finite-quotient
comparison and the constant-section-normalized presentation of the completed ring.
Source: blueprint finite-extension compact-support base change; Stacks 098T
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
noncomputable def cbcCompletedCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcCompletedComparison Y d).symm ≪≫
    fourCornerCoefficientIso f
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } ≪≫
    pbcCompletedComparison X d

/-- Both completed coefficient comparisons have the same positive-quotient projections. -/
private theorem coefficientIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    cbcCompletedCoefficientIso f d = d.integralRingIso f := by
  apply Iso.ext
  rw [← cbcDatumCoefficient_eq d f]
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  apply limit.hom_ext
  rintro ⟨n⟩
  change (cbcCompletedCoefficientIso f d).hom ≫ pbcAdicProjection X d n = _
  dsimp only [cbcCompletedCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [Category.assoc]
  change L.map (pbcCompletedComparison Y d).inv ≫
    (fourCornerCoefficientIso f dd).hom ≫
      (pbcCompletedComparison X d).hom ≫ limit.π _ (Opposite.op n) = _
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc (fourCornerCoefficientIso f dd).hom]
  have hfc := fourCornerProjectionComm f dd n
  dsimp only [adicDatumProjection] at hfc
  erw [hfc]
  simp only [Category.assoc]
  rw [← Category.assoc, ← L.map_comp]
  change L.map ((pbcCompletedComparison Y d).inv ≫ limit.π _ (Opposite.op n)) ≫ _ = _
  erw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc, completedCoefficientMap, limit.lift_π]
  rfl

private theorem coefficientSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (V : Y.ProEtᵒᵖ) (a : A) :
    (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).hom.app V (pbcCompletedSection Y d V a) =
      pbcCompletedSection X d ((proEtaleBaseChange f).op.obj V) a := by
  have he : proEtaleRingDirectImageMap f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (cbcCompletedCoefficientIso f d) =
        completedCoefficientDirectImageMap f d := by
    rw [coefficientIso_eq]
    unfold proEtaleRingDirectImageMap completedCoefficientDirectImageMap
    rw [cbcDatumCoefficient_eq]
  rw [he]
  exact pbcCompletedSection_directImage f d V a

private theorem completedModulePushLinear {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).Linear A := by
  constructor
  intro M N h a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change pbcCompletedSection X d ((proEtaleBaseChange f).op.obj V) a •
      h.val.app ((proEtaleBaseChange f).op.obj V) x =
    (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).hom.app V (pbcCompletedSection Y d V a) •
        h.val.app ((proEtaleBaseChange f).op.obj V) x
  rw [coefficientSections]

private theorem completedModulePullLinear {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleRingModulePullback f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (cbcCompletedCoefficientIso f d)).Linear A := by
  have := completedModulePushLinear f d
  exact (proEtaleRingModuleAdjunction f _ _ _).left_adjoint_linear

/-- Append the closed complement, retaining the original scheme realizations of the strata. -/
private def extendFiniteStratification {T U Z : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (hcover : Set.range j ∪ Set.range i = Set.univ)
    (hdisjoint : Disjoint (Set.range j) (Set.range i))
    (s : FiniteLocallyClosedStratification U) : FiniteLocallyClosedStratification T where
  n := s.n + 1
  stratum := Fin.cases (Set.range i) (fun k ↦ j '' s.stratum k)
  isLocallyClosed_stratum := Fin.cases i.isLocallyClosed_range
    (fun k ↦ (s.isLocallyClosed_stratum k).image j.isOpenEmbedding.isInducing
      j.isOpenEmbedding.isOpen_range.isLocallyClosed)
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ Set.range j ∪ Set.range i := hcover.symm ▸ Set.mem_univ x
    rcases hx with ⟨y, rfl⟩ | hx
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
      exact Set.mem_iUnion.mpr ⟨k.succ, y, hk, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨0, hx⟩
  pairwise_disjoint_stratum := by
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact (hab rfl).elim
      | succ b =>
        exact hdisjoint.symm.mono (Set.Subset.refl _) (Set.image_subset_range _ _)
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        exact hdisjoint.mono (Set.image_subset_range _ _) (Set.Subset.refl _)
      | succ b =>
        exact (Set.disjoint_image_iff j.isOpenEmbedding.injective).mpr
          (s.pairwise_disjoint_stratum (fun h ↦ hab (congrArg Fin.succ h)))
  domain := Fin.cases Z s.domain
  immersion := Fin.cases i (fun k ↦ s.immersion k ≫ j)
  isImmersion := Fin.cases (inferInstanceAs (IsImmersion i))
    (fun k ↦ by
      change IsImmersion (s.immersion k ≫ j)
      have := s.isImmersion k
      infer_instance)
  range_immersion := Fin.cases rfl (fun k ↦ by
    change Set.range (s.immersion k ≫ j).base = j.base '' s.stratum k
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, s.range_immersion])

/-- The actual-ring local-perfect criterion survives open extension by zero. -/
private theorem openShriek_preserves (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hTdim : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (hXl : IsUnit (l : Γ(X, ⊤))) (hTl : IsUnit (l : Γ(T, ⊤)))
    (j : X ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (K : PbcCompletedDerived X (pbcPadicCoefficientDatum l E))
    (hK : IsPbcBoundedConstructibleComplete X l E K) :
    IsPbcBoundedConstructibleComplete T l E
      ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) j inferInstance).obj K) := by
  classical
  let d := pbcPadicCoefficientDatum l E
  let J := (cbcDerivedOpenShriek d j inferInstance).obj K
  let i := j.closedComplement
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [Scheme.Hom.range_closedComplement, compl_compl]
  have hz := closedDerived_isZero d j i hji K
  let B := (sheafCompose (ProEt.topology (Over.mk i).left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (d.integralRingIso i)
  let G₀ := SheafOfModules.restrictScalars B.hom
  have : G₀.IsEquivalence := by
    exact inferInstanceAs (proEtaleScalarEquivalence (Over.mk i).left B).functor.IsEquivalence
  have : PreservesFiniteLimits G₀ := inferInstance
  have : PreservesFiniteColimits G₀ := inferInstance
  let G := G₀.mapDerivedCategory
  have : G.IsEquivalence := by dsimp [G]; infer_instance
  have hzi : IsZero ((d.pull i).obj J) := by
    apply IsZero.of_full_of_faithful_of_isZero G
    exact hz.of_iso ((derivedPullbackScalarIso i _ _ (d.integralRingIso i)).app J)
  have := cbcOpenUnit_isIso d j
  let ej : K ≅ (d.pull j).obj J := (asIso (cbcDerivedOpenAdjunction d j).unit).app K
  obtain ⟨s, hs⟩ := (integralPadicLocalPerfectCriterion X l E hXdim hXl K).mp hK
  apply (integralPadicLocalPerfectCriterion T l E hTdim hTl J).mpr
  have hcover : Set.range j ∪ Set.range i = Set.univ := by
    rw [Scheme.Hom.range_closedComplement, Set.union_compl_self]
  have hdisjoint : Disjoint (Set.range j) (Set.range i) := by
    rw [Scheme.Hom.range_closedComplement]
    exact disjoint_compl_right
  refine ⟨extendFiniteStratification j i hcover hdisjoint s, ?_⟩
  intro k
  induction k using Fin.cases with
  | zero =>
    change ∃ V : Sieve (⊤_ (Over.mk i).left.ProEt), V ∈ ProEt.topology (Over.mk i).left _ ∧ _
    refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
    intro U q hq
    let := HasDerivedCategory.standard (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E))
    let := HasZeroObject.zero' (C := CochainComplex
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    let P : CochainComplex (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) ℤ := 0
    refine ⟨P, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
    · intro n
      have hzP := (HomologicalComplex.eval _ _ n).map_isZero
        (isZero_zero (CochainComplex
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ))
      have : Subsingleton (P.X n) := ModuleCat.subsingleton_of_isZero hzP
      exact ⟨inferInstance, inferInstance⟩
    · have hleft : IsZero ((pbcActualDerivedPull (U.hom ≫ i) d).obj J) := by
        exact ((d.pull U.hom).map_isZero hzi).of_iso
          ((cbcDatumOrdinaryTransport d (U.hom ≫ i)).app J ≪≫
            (d.pullComp U.hom i).app J)
      have hright : IsZero ((integralConstantDerived U.left d).obj
          ((completedConstantQ _).obj P)) := by
        dsimp [integralConstantDerived]
        apply Functor.map_isZero
        exact Functor.map_isZero _ (isZero_zero _)
      exact ⟨hleft.iso hright⟩
  | succ k =>
    change ∃ V : Sieve (⊤_ (s.domain k).ProEt),
      V ∈ ProEt.topology (s.domain k) _ ∧ _
    obtain ⟨V, hV, hm⟩ := hs k
    refine ⟨V, hV, ?_⟩
    intro U q hq
    obtain ⟨P, a, b, hge, hle, hp, ⟨e⟩⟩ := hm U q hq
    refine ⟨P, a, b, hge, hle, hp, ?_⟩
    change Nonempty ((pbcActualDerivedPull (U.hom ≫ s.immersion k ≫ j) d).obj J ≅ _)
    rw [← Category.assoc]
    exact ⟨(cbcDatumOrdinaryTransport d (U.hom ≫ s.immersion k ≫ j)).app J ≪≫
      (d.pullComp (U.hom ≫ s.immersion k) j).app J ≪≫
      (d.pull (U.hom ≫ s.immersion k)).mapIso ej.symm ≪≫
      (cbcDatumOrdinaryTransport d (U.hom ≫ s.immersion k)).symm.app K ≪≫ e⟩

private def openExtensionIso {X T : Scheme.{u}} (j : X ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingDerivedOpenExtension j (pbcAdicCompletion T d)
        (pbcAdicCompletion X d) (cbcCompletedCoefficientIso j d) ≅
      cbcDerivedOpenShriek d j inferInstance := by
  rw [coefficientIso_eq]
  apply Functor.mapDerivedCategoryNatIso
  exact (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j _ _ _)).leftAdjointUniq
    (Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
      (@asIso _ _ _ _ (cbcPullToRestriction d j)
        (cbcPullToRestriction_isIso d j)).symm)

/-- The chosen-compactification candidate with its actual completed coefficient maps.
Source: blueprint finite-extension compact-support base change, integral functors
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
def cbcIntegralCompactSupport (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (cp : Compactification f) :=
  letI : QuasiCompact cp.i := cp.quasiCompact_openImmersion inferInstance
  proEtaleRingCompactSupportImage cp
    (pbcAdicCompletion Y (pbcPadicCoefficientDatum l E))
    (pbcAdicCompletion cp.Z (pbcPadicCoefficientDatum l E))
    (pbcAdicCompletion X (pbcPadicCoefficientDatum l E))
    (cbcCompletedCoefficientIso cp.g (pbcPadicCoefficientDatum l E))
    (cbcCompletedCoefficientIso cp.i (pbcPadicCoefficientDatum l E))

/-- The shift comparison is the composite of degreewise extension by zero and the
K-injective direct-image shift comparison. It induces the comparison on the restriction.
Source: blueprint finite-extension compact-support base change, integral functors
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
instance cbcIntegralCompactSupport_commShift (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (cp : Compactification f) :
    (cbcIntegralCompactSupport l E cp).CommShift ℤ := by
  unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
  infer_instance

/-- The chosen Rp_* j_! restricts to an exact A-linear functor between the precise
compatible uniform categories. Fullness makes object preservation sufficient to restrict
all maps; addition and scalar multiplication below concern exactly those maps. The last
clause is exactness for the inherited ambient triangles and the specified shift comparison.
Source: blueprint thm-cbc-finite-extension, proof, sole paragraph; Stacks Tags 0GL0 and
095U; Bhatt--Scholze Lemmas 6.7.2 and 6.7.7
(blueprint: lem-cbc-integral-compact-support-uniform-restriction).

Proof:
1. Normalize the chosen completed coefficient isomorphisms by testing their quotient
projections. Transpose the constant-scalar equation to get the sectionwise direct-image
scalar equation, and obtain pullback linearity by adjunction.
2. The proper compactification is Noetherian and finite-dimensional, with a uniform
geometric-fibre dimension bound. Pull back the inverse of l from Y.
3. Use the local-perfect criterion over the actual valuation ring. Extend the input's
finite stratification through the open immersion and append the closed complement with
zero model. Pullback composition and the open unit retain the old models; closed
restriction of extension by zero vanishes. The reverse criterion gives full compatible
uniform membership. Adjoint uniqueness identifies this extension with the chosen one.
4. The DVR maximal ideal contains l. Apply actual-coefficient constructible preservation
to the identity Cartesian square for the proper map, with N=l and the fibre bound from
step 2. Transport its first conclusion through the chosen-functor comparison.
5. Addition, scalar multiplication, and distinguished triangles are preserved by the
composite of exact open extension and derived direct image. The scalar assertions follow
from adjunction linearity and derived linearity; triangulated functoriality uses precisely
the shift comparison already specified above. -/
theorem cbcIntegralCompactSupport_uniformRestriction (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hYl : IsUnit (l : Γ(Y, ⊤)))
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (cp : Compactification f) :
    (∀ K, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete Y l E ((cbcIntegralCompactSupport l E cp).obj K)) ∧
    (∀ K L, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete X l E L → ∀ a b : K ⟶ L,
        (cbcIntegralCompactSupport l E cp).map (a + b) =
          (cbcIntegralCompactSupport l E cp).map a + (cbcIntegralCompactSupport l E cp).map b) ∧
    (∀ K L, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete X l E L →
      ∀ (a : Padic.coefficientExtensionIntegers l E) (b : K ⟶ L),
        (cbcIntegralCompactSupport l E cp).map (a • b) =
          a • (cbcIntegralCompactSupport l E cp).map b) ∧
    (∀ T : Triangle (DerivedCategory (pbcModules X
        (pbcAdicCompletion X (pbcPadicCoefficientDatum l E)))),
      T ∈ distTriang _ → IsPbcBoundedConstructibleComplete X l E T.obj₁ →
      IsPbcBoundedConstructibleComplete X l E T.obj₂ →
      IsPbcBoundedConstructibleComplete X l E T.obj₃ →
      (cbcIntegralCompactSupport l E cp).mapTriangle.obj T ∈ distTriang _) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    classical
    let d := pbcPadicCoefficientDatum l E
    have : QuasiCompact cp.i := cp.quasiCompact_openImmersion inferInstance
    have : IsLocallyNoetherian cp.Z := LocallyOfFiniteType.isLocallyNoetherian cp.g
    have : CompactSpace cp.Z := QuasiCompact.compactSpace_of_compactSpace cp.g
    have : IsNoetherian cp.Z := ⟨⟩
    have hZdim := AlgebraicGeometry.finiteType_source_dimension_bound cp.g _hYdim
    have hZl : IsUnit (l : Γ(cp.Z, ⊤)) := by
      simpa only [map_natCast] using _hYl.map cp.g.appTop.hom
    let J := (cbcDerivedOpenShriek d cp.i inferInstance).obj K
    have hJ : IsPbcBoundedConstructibleComplete cp.Z l E J :=
      openShriek_preserves l E _hXdim hZdim _hXl hZl cp.i K hK
    have hAnn : (l : Padic.coefficientExtensionIntegers l E ⧸ d.ideal) = 0 := by
      have H := (Padic.extension_integers_dvr l E
        (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
      have hgen := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      change (Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (l : Padic.coefficientExtensionIntegers l E) ∈
        Ideal.span {Padic.coefficientExtensionUniformizer l E}
      change Ideal.span {Padic.coefficientExtensionUniformizer l E} =
        Padic.coefficientExtensionMaximalIdeal l E at hgen
      rw [hgen]
      apply (H.2.1 _).2
      have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
      rw [map_natCast] at h
      change spectralNorm ℚ_[l] E (l : E) < 1
      rw [h]
      exact Padic.norm_p_lt_one
    obtain ⟨e, he⟩ := hZdim
    have hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ Y),
        topologicalKrullDim (pullback cp.g y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
      intro Ω _ _ y
      exact (AlgebraicGeometry.topologicalKrullDim_pullback_le cp.g y).trans he
    let s : IsPullback (𝟙 cp.Z) cp.g cp.g (𝟙 Y) := .of_horiz_isIso ⟨by simp⟩
    let sq : ChosenCartesianSquare (𝟙 cp.Z) cp.g cp.g (𝟙 Y) :=
      { w := by simp
        isoPullback := s.isoPullback
        hom_fst := s.isoPullback_hom_fst
        hom_snd := s.isoPullback_hom_snd }
    have hp := (d.constructible_preservation sq ⟨e, he⟩ _hYdim ⟨e, he⟩ _hYdim
      l (Fact.out : l.Prime).pos hAnn hZl _hYl hZl _hYl e hfib J hJ).1
    have := (pbcUniformComplete_isTriangulated Y l E _hYdim _hYl).1
    apply ObjectProperty.prop_of_iso
      (IsPbcBoundedConstructibleComplete Y l E : ObjectProperty _) _ hp
    change (d.push cp.g).obj J ≅ _
    unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
    dsimp only [Functor.comp_obj]
    rw [coefficientIso_eq cp.g d]
    exact (d.push cp.g).mapIso ((openExtensionIso cp.i d).app K).symm
  · intro K L hK hL a b
    unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
    exact Functor.map_add _
  · intro K L hK hL a b
    let d := pbcPadicCoefficientDatum l E
    have := completedModulePullLinear cp.i d
    have := completedModulePullLinear cp.g d
    have hJ : (proEtaleRingOpenExtension cp.i (pbcAdicCompletion cp.Z d)
        (pbcAdicCompletion X d) (cbcCompletedCoefficientIso cp.i d)).Linear
          (Padic.coefficientExtensionIntegers l E) :=
      (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback cp.i _ _ _)).left_adjoint_linear
    have hP : (proEtaleRingDerivedDirectImage cp.g (pbcAdicCompletion Y d)
        (pbcAdicCompletion cp.Z d) (cbcCompletedCoefficientIso cp.g d)).Linear
          (Padic.coefficientExtensionIntegers l E) :=
      (proEtaleRingDerivedAdjunction cp.g _ _ _).right_adjoint_linear
    unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
    exact Functor.map_smul _ a b
  · intro T hT h₁ h₂ h₃
    have : (cbcIntegralCompactSupport l E cp).IsTriangulated := by
      unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
      infer_instance
    exact (cbcIntegralCompactSupport l E cp).map_distinguished T hT

end AlgebraicGeometry.Scheme
