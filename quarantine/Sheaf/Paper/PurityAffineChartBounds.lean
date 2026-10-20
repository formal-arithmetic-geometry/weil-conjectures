/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteTypeExceptionalInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.Paper.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Affine-chart assembly for constructible exceptional inverse image

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
`cor-pur-general-admissibility-datum` (blueprint: cor-pur-general-admissibility-datum).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Specialize the published functor `finiteTypeExceptionalInverseImage` to the actual
positive-level quotient and the supplied compactification. Its defining composite is
`ν_X^* f^× Rν_{Y,*}`; the right adjoint and compactification choices are determined up
to their canonical isomorphisms. The `ULift` changes only the coefficient universe.
Source: blueprint cor-pur-general-admissibility-datum, applying the finite-level
defining formula of def-weil-exceptional-inverse-image (order 1489)
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def sfFiniteExceptionalInverseImage
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (c : Compactification f) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : HasCompactification f := ⟨⟨c⟩⟩
  finiteTypeExceptionalInverseImage
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) k f

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- The chosen finite affine target cover, finite affine source covers over its members,
and closed affine-space presentations. The equations specify that each presentation is
over its target open. Empty opens and empty index sets are permitted.
Source: blueprint, affine charts in cor-pur-general-admissibility-datum
(blueprint: cor-pur-general-admissibility-datum). -/
structure SfAffineChartPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) where
  count : ℕ
  target : Fin count → Y.Opens
  target_affine : ∀ i, IsAffineOpen (target i)
  target_cover : ∀ y : Y, ∃ i, y ∈ target i
  size : Fin count → ℕ
  source : (i : Fin count) → Fin (size i) → X.Opens
  source_affine : ∀ i j, IsAffineOpen (source i j)
  source_le : ∀ i j, source i j ≤ f ⁻¹ᵁ target i
  source_cover : ∀ (i : Fin count) (x : X), x ∈ f ⁻¹ᵁ target i →
    ∃ j : Fin (size i), x ∈ source i j
  dimension : (i : Fin count) → Fin (size i) → ℕ
  presentation : (i : Fin count) → (j : Fin (size i)) →
    (source i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme
  presentation_closed : ∀ i j, IsClosedImmersion (presentation i j)
  presentation_over : ∀ i j,
    presentation i j ≫
        (AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme ↘
          (target i).toScheme) ≫ (target i).ι = (source i j).ι ≫ f

open Classical in
/-- Omit precisely the empty source charts, retaining the target cover and every
surviving chart's affine-space presentation. The subtype of surviving indices is
reindexed by `Fintype.equivFin`. A point in an original chart witnesses its
nonemptiness, so these charts still cover every inverse image of a target open.
Source: blueprint cor-pur-general-admissibility-datum, omission of empty charts
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.nonemptyCharts
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) :
    SfAffineChartPresentation f :=
  let e (i : Fin C.count) :=
    (Fintype.equivFin {j : Fin (C.size i) // Nonempty (C.source i j)}).symm
  { count := C.count
    target := C.target
    target_affine := C.target_affine
    target_cover := C.target_cover
    size := fun i ↦ Fintype.card {j : Fin (C.size i) // Nonempty (C.source i j)}
    source := fun i j ↦ C.source i (e i j).val
    source_affine := fun i j ↦ C.source_affine i (e i j).val
    source_le := fun i j ↦ C.source_le i (e i j).val
    source_cover := by
      intro i x hx
      obtain ⟨j, hj⟩ := C.source_cover i x hx
      refine ⟨(e i).symm ⟨j, ⟨⟨x, hj⟩⟩⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hj
    dimension := fun i j ↦ C.dimension i (e i j).val
    presentation := fun i j ↦ C.presentation i (e i j).val
    presentation_closed := fun i j ↦ C.presentation_closed i (e i j).val
    presentation_over := fun i j ↦ C.presentation_over i (e i j).val }

/-- Maximum chart embedding dimension, with `sup ∅ = 0` in `ℕ`.
Source: blueprint affine-chart maximum
(blueprint: cor-pur-general-admissibility-datum). -/
def SfAffineChartPresentation.maxDimension {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : SfAffineChartPresentation f) : ℕ :=
  Finset.univ.sup (fun ij : (i : Fin C.count) × Fin (C.size i) ↦ C.dimension ij.1 ij.2)

/-- Finite-type schemes over a field have finite Krull dimension. This integer-valued
reading takes the nonnegative dimension for a nonempty such scheme and zero for the
empty scheme, whose topological dimension is bottom.
Source: blueprint dimension convention in the affine-chart assembly
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def sfDimension (Y : Scheme.{u}) : ℕ :=
  ((topologicalKrullDim Y).unbotD 0).toNat

open Classical in
/-- The maximum over the nonempty source charts in affine-chart assembly;
the empty source has shift zero.
Source: blueprint cor-pur-general-admissibility-datum, definition of `D`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyDimension
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℕ :=
  if Nonempty X then C.nonemptyCharts.maxDimension else 0

open Classical in
/-- The corollary's integer `c = max_U (c_U + 1 + 2(D-d_U))`, with
`c_U = 2(d_U + dim Y)`. Every summand equals the displayed expression when `X`
is nonempty, after applying `nonemptyCharts`. For the empty source `c = 0`.
Source: blueprint cor-pur-general-admissibility-datum, formula for `c`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyConstant
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℤ :=
  if Nonempty X then
    2 * (C.nonemptyCharts.maxDimension : ℤ) + 2 * (sfDimension Y : ℤ) + 1 else 0

private theorem coefficient_killed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
  let h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    have he := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change Padic.coefficientExtensionAbsoluteValue l E
      (algebraMap ℚ_[l] E (l : ℚ_[l])) = ‖(l : ℚ_[l])‖ at he
    rw [map_natCast] at he
    rw [he]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rw [← hgen] at hl
  have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl n)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hq

private theorem finite_dimension_bound {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    topologicalKrullDim X ≤
      (((topologicalKrullDim X).unbotD 0).toNat : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  generalize topologicalKrullDim X = t at *
  induction t using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe t =>
    induction t using ENat.recTopCoe with
    | top => exact False.elim ((ENat.natCast_ne_top d)
        (top_le_iff.mp (WithBot.coe_le_coe.mp hd)))
    | coe t => simp

private theorem datum_charP (F : WeilConjectures.FiniteFieldDatum.{u}) : CharP F.k F.p := by
  classical
  let : Fintype F.k₀ := Fintype.ofFinite F.k₀
  let : Fact F.p.Prime := ⟨F.prime⟩
  let : CharP F.k₀ F.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, F.card_base, F.cardinality_eq])
  exact charP_of_injective_algebraMap (algebraMap F.k₀ F.k).injective F.p

private theorem coefficient_invertible
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k)) :
    HasInvertibleExponent
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y := by
  let := datum_charP F
  have hlk : (l : F.k) ≠ 0 := by
    intro h
    exact hl ((Nat.prime_dvd_prime_iff_eq F.prime (Fact.out : l.Prime)).mp
      ((CharP.cast_eq_zero_iff F.k F.p l).mp h)).symm
  have hu : IsUnit ((l ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h := ((Ne.isUnit hlk).pow n).map (Scheme.ΓSpecIso (.of F.k)).inv.hom
    simpa only [← Nat.cast_pow, map_natCast] using h.map aY.appTop.hom
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, ?_, hu⟩
  apply ULift.down_injective
  change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
  exact coefficient_killed l E n

private theorem etale_tor_chart_bounds
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (d : ℕ)
    (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleTorAmplitudeIn
      (ModuleCat.{u + 1} Λ) Y a b K) :
    Etale.DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X
      (a - 2 * (C.maxDimension : ℤ)) (b + 2 * d + 1)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let I := (i : Fin C.count) × Fin (C.size i)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let U : Fin (Fintype.card I) → X.Opens := fun r ↦ C.source (e r).1 (e r).2
  have hU : ∀ x : X, ∃ r, x ∈ U r := by
    intro x
    obtain ⟨i, hi⟩ := C.target_cover (f x)
    obtain ⟨j, hj⟩ := C.source_cover i x hi
    refine ⟨e.symm (⟨i, j⟩ : I), ?_⟩
    change x ∈ C.source (e (e.symm (⟨i, j⟩ : I))).1 _
    rw [e.apply_symm_apply]
    exact hj
  apply Etale.constructibleTorAmplitudeIn_of_openCover Λ U hU
  intro r
  let i := (e r).1
  let j := (e r).2
  have : IsAffine (C.source i j).toScheme := C.source_affine i j
  have : IsAffine (C.target i).toScheme := C.target_affine i
  have : IsClosedImmersion (C.presentation i j) := C.presentation_closed i j
  have : TopologicalSpace.NoetherianSpace (C.source i j) :=
    (C.source i j).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (C.source i j).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (C.source i j).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : TopologicalSpace.NoetherianSpace (C.target i) :=
    (C.target i).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (C.target i).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hK' := Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart Λ aY
    (C.target i).ι (C.presentation i j) d hd a b hK
  obtain ⟨e₁⟩ := Etale.nonempty_iso_rightDerivedUpperShriek_comp Λ (C.source i j).ι f
  have heq : ∀ {g₁ g₂ : (C.source i j).toScheme ⟶ Y}
      [HasCompactification g₁] [HasCompactification g₂], g₁ = g₂ →
      Nonempty (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g₁ ≅
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g₂) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (C.presentation_over i j)
  have hn : C.dimension i j ≤ C.maxDimension :=
    Finset.le_sup (f := fun ij : I ↦ C.dimension ij.1 ij.2)
      (Finset.mem_univ (⟨i, j⟩ : I))
  have hn' : (C.dimension i j : ℤ) ≤ C.maxDimension := by exact_mod_cast hn
  apply Etale.constructibleTorAmplitudeIn_of_iso (ModuleCat.{u + 1} Λ)
    (((Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
      (C.source i j).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm
  obtain ⟨⟨hbc, hc₁, hc₂⟩, hta⟩ := hK'
  exact ⟨⟨hbc, _root_.DerivedCategory.TStructure.t.isGE_of_ge _ _
    (a - 2 * (C.dimension i j : ℤ)) (by omega), hc₂⟩,
    hta.mono (by omega) le_rfl⟩

private theorem closed_homology
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent Λ T] (i : Z ⟶ T) [IsClosedImmersion i]
    [HasCompactification i] (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + 2 * d + 1)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj K) := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := { __ := LocallyOfFiniteType.isLocallyNoetherian aT }
  let V := Scheme.openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    simp [V, Scheme.openComplementOfIsClosedImmersion]
  have hdV : topologicalKrullDim V ≤ (d : WithBot ℕ∞) :=
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
  have hn (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k))
      {P : Scheme.{u}} (p₁ : P ⟶ V.toScheme) (p₂ : P ⟶ Spec (.of L))
      (hP : IsPullback p₁ p₂ (V.ι ≫ aT) s) :
      topologicalKrullDim P ≤ (d : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hP.isoPullback.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_pullback_le (V.ι ≫ aT) s).trans hdV
  have hcd (M : Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (q : ℤ) (hq : (2 * d : ℕ) < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) V.ι).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    have hq0 : 0 ≤ q := by omega
    lift q to ℕ using hq0
    exact (Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le Λ
      isAddTorsion_of_finite (V.ι ≫ aT) aT V.ι rfl d hn M q (by simpa using hq)).of_iso
      (Etale.homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ V.ι M q)
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι
  let G := Etale.lowerStar (ModuleCat.{u + 1} Λ) V.ι
  have hP := P.homologyConcentratedIn_mapDerivedCategory_obj hK
  have hb := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨a, b, hP⟩
  have ha := hP.1
  have hh := hP.2
  have hM : _root_.DerivedCategory.homologyConcentratedIn a (b + 2 * d)
      (G.rightDerivedFunctor.obj (P.mapDerivedCategory.obj K)) := by
    constructor
    · simpa using _root_.DerivedCategory.isGE_obj_of_isGE G.rightDerivedFunctor 0
        (fun M ↦ G.isGE_rightDerivedFunctor_obj_singleFunctor M) _ hb a
    · exact _root_.DerivedCategory.isLE_obj_of_isLE G.rightDerivedFunctor (2 * d)
        (fun M ↦ (_root_.DerivedCategory.isLE_iff _ _).2 (by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcd M)) _ hb b
  have hN := Etale.homologyConcentratedIn_obj₁ (ModuleCat.{u + 1} Λ) _
    (Etale.supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ)
      i V.ι hij K) (by omega : b ≤ b + 2 * d) hK
      (Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
        (G.rightDerivedFunctor.mapIso
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} Λ) V.ι).app K).symm) hM)
  exact Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
    ((Etale.mapDerivedCategoryUpperStarRightDerivedLowerShriekIso
      (ModuleCat.{u + 1} Λ) i).app _)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).homologyConcentratedIn_mapDerivedCategory_obj hN)

private theorem smooth_homology
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn (a - 2 * d) (b - 2 * d)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := Etale.exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨et⟩ := Etale.nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex
    Λ f d K
  obtain ⟨_, hLf⟩ := Etale.isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  have hL₀ := Etale.torAmplitudeIn_singleFunctor_zero_of_flat (ModuleCat.{u + 1} Λ) L hLf
  have hpull := (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    |>.homologyConcentratedIn_mapDerivedCategory_obj hK
  have hpull' := Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} Λ) f).app K).symm hpull
  have hM := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
    hpull' hL₀
  simp only [add_zero] at hM
  let T := (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)
  let e := et.symm ≪≫ T.mapIso eω ≪≫ (T.commShiftIso (2 * d : ℤ)).app _
  have hM' : _root_.DerivedCategory.homologyConcentratedIn a b
      (T.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) := hM
  obtain ⟨hge, hle⟩ := hM'
  have hs : _root_.DerivedCategory.homologyConcentratedIn (a - 2 * d) (b - 2 * d)
      ((T.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦(2 * d : ℤ)⟧) := by
    constructor
    · exact _root_.DerivedCategory.TStructure.t.isGE_shift _ a (2 * d)
        (a - 2 * d) (by omega)
    · exact _root_.DerivedCategory.TStructure.t.isLE_shift _ b (2 * d)
        (b - 2 * d) (by omega)
  exact Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ) e.symm hs

private theorem etale_homology_chart
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {U V Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V]
    {n : ℕ} (c : U ⟶ AffineSpace (ULift.{u} (Fin n)) V)
    [IsClosedImmersion c] [HasCompactification (c ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V) ≫ v)]
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn (a - 2 * n) (b + 2 * d + 1)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ)
        (c ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V) ≫ v)).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := AffineSpace (ULift.{u} (Fin n)) V ↘ V
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasCompactification c := (Compactification.ofIsProper c).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : HasInvertibleExponent Λ (AffineSpace (ULift.{u} (Fin n)) V) :=
    HasInvertibleExponent.of_hom (π ≫ v)
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  have hdP : topologicalKrullDim (AffineSpace (ULift.{u} (Fin n)) V) ≤
      ((d + n : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    have hV := (v.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin, Nat.cast_add]
    exact add_le_add hV le_rfl
  have h₁ := (Etale.upperStar (ModuleCat.{u + 1} Λ) v)
    |>.homologyConcentratedIn_mapDerivedCategory_obj hK
  have h₁' := Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
    ((Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion Λ v).app K).symm h₁
  have h₂ := smooth_homology Λ π n h₁'
  have h₃ := closed_homology Λ (π ≫ v ≫ aY) c (d + n) hdP h₂
  obtain ⟨e₁⟩ := Etale.nonempty_iso_rightDerivedUpperShriek_comp Λ c (π ≫ v)
  obtain ⟨e₂⟩ := Etale.nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  have hb : b - 2 * (n : ℤ) + 2 * ((d + n : ℕ) : ℤ) + 1 = b + 2 * d + 1 := by
    push_cast
    ring
  rw [hb] at h₃
  exact Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
    ((e₁ ≪≫ Functor.isoWhiskerRight e₂ _).app K).symm h₃

private theorem etale_homology_bounds
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (d : ℕ)
    (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn
      (a - 2 * (C.maxDimension : ℤ)) (b + 2 * d + 1)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let I := (i : Fin C.count) × Fin (C.size i)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let U : Fin (Fintype.card I) → X.Opens := fun r ↦ C.source (e r).1 (e r).2
  have hU : ∀ x : X, ∃ r, x ∈ U r := by
    intro x
    obtain ⟨i, hi⟩ := C.target_cover (f x)
    obtain ⟨j, hj⟩ := C.source_cover i x hi
    refine ⟨e.symm (⟨i, j⟩ : I), ?_⟩
    change x ∈ C.source (e (e.symm (⟨i, j⟩ : I))).1 _
    rw [e.apply_symm_apply]
    exact hj
  apply Etale.homologyConcentratedIn_of_openCover (ModuleCat.{u + 1} Λ) U hU
  intro r
  let i := (e r).1
  let j := (e r).2
  have : IsAffine (C.source i j).toScheme := C.source_affine i j
  have : IsAffine (C.target i).toScheme := C.target_affine i
  have : IsClosedImmersion (C.presentation i j) := C.presentation_closed i j
  have : TopologicalSpace.NoetherianSpace (C.source i j) :=
    (C.source i j).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (C.source i j).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (C.source i j).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : TopologicalSpace.NoetherianSpace (C.target i) :=
    (C.target i).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (C.target i).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hK' := etale_homology_chart Λ aY
    (C.target i).ι (C.presentation i j) d hd hK
  obtain ⟨e₁⟩ := Etale.nonempty_iso_rightDerivedUpperShriek_comp Λ (C.source i j).ι f
  have heq : ∀ {g₁ g₂ : (C.source i j).toScheme ⟶ Y}
      [HasCompactification g₁] [HasCompactification g₂], g₁ = g₂ →
      Nonempty (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g₁ ≅
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g₂) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (C.presentation_over i j)
  have hn : C.dimension i j ≤ C.maxDimension :=
    Finset.le_sup (f := fun ij : I ↦ C.dimension ij.1 ij.2)
      (Finset.mem_univ (⟨i, j⟩ : I))
  have hn' : (C.dimension i j : ℤ) ≤ C.maxDimension := by exact_mod_cast hn
  apply Etale.homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ)
    (((Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
      (C.source i j).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm
  obtain ⟨hc₁, hc₂⟩ := hK'
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_ge _ _
    (a - 2 * (C.dimension i j : ℤ)) (by omega), hc₂⟩


private theorem etale_assembly_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b K) :
    Etale.DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X
      (a - 2 * (C.assemblyDimension : ℤ))
      (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  by_cases hx : Nonempty X
  · refine ⟨Etale.boundedConstructible_rightDerivedUpperShriek Λ aY f hK.1, ?_⟩
    have h := etale_homology_bounds Λ aY f C.nonemptyCharts (Scheme.sfDimension Y)
      (finite_dimension_bound aY) a b hK.2
    simpa only [Scheme.SfAffineChartPresentation.assemblyDimension,
      Scheme.SfAffineChartPresentation.assemblyConstant, dif_pos hx, if_pos hx,
      show b - 2 * (C.nonemptyCharts.maxDimension : ℤ) +
        (2 * (C.nonemptyCharts.maxDimension : ℤ) + 2 * (Scheme.sfDimension Y : ℤ) + 1) =
        b + 2 * (Scheme.sfDimension Y : ℤ) + 1 by ring] using h
  · have : IsEmpty X := not_nonempty_iff.mp hx
    let U : Fin 0 → X.Opens := Fin.elim0
    have hU : ∀ x : X, ∃ i, x ∈ U i := fun x ↦ isEmptyElim x
    exact ⟨Etale.boundedConstructible_of_openCover Λ U hU _ (fun i ↦ Fin.elim0 i),
      Etale.homologyConcentratedIn_of_openCover (ModuleCat.{u + 1} Λ) U hU _
        (fun i ↦ Fin.elim0 i)⟩

private theorem etale_assembly_tor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleTorAmplitudeIn
      (ModuleCat.{u + 1} Λ) Y a b K) :
    Etale.DerivedCategory.constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X
      (a - 2 * (C.assemblyDimension : ℤ))
      (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  by_cases hx : Nonempty X
  · have h := etale_tor_chart_bounds Λ aY f C.nonemptyCharts (Scheme.sfDimension Y)
      (finite_dimension_bound aY) a b hK
    simpa only [Scheme.SfAffineChartPresentation.assemblyDimension,
      Scheme.SfAffineChartPresentation.assemblyConstant, dif_pos hx, if_pos hx,
      show b - 2 * (C.nonemptyCharts.maxDimension : ℤ) +
        (2 * (C.nonemptyCharts.maxDimension : ℤ) + 2 * (Scheme.sfDimension Y : ℤ) + 1) =
        b + 2 * (Scheme.sfDimension Y : ℤ) + 1 by ring] using h
  · have : IsEmpty X := not_nonempty_iff.mp hx
    let U : Fin 0 → X.Opens := Fin.elim0
    have hU : ∀ x : X, ∃ i, x ∈ U i := fun x ↦ isEmptyElim x
    exact Etale.constructibleTorAmplitudeIn_of_openCover Λ U hU _ (fun i ↦ Fin.elim0 i)

private theorem pro_assembly_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : ProEtale.DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a b K) :
    ProEtale.DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X
      (a - 2 * (C.assemblyDimension : ℤ))
      (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
      ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hK.1
  let νY := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y
  let νX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  obtain ⟨hKa, hKb⟩ := hK.2
  have he : _root_.DerivedCategory.homologyConcentratedIn a b
      (νY.mapDerivedCategory.obj G) :=
    ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩
  have hG' := νY.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj he
  have h := etale_assembly_constructible Λ aY f C a b ⟨hG, hG'⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} Λ) Y G hG.1.1
  let e' := ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso e).symm ≪≫
    νX.mapDerivedCategory.mapIso
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} Λ) Y).unit.app G)).symm)
  have hh : _root_.DerivedCategory.homologyConcentratedIn
      (a - 2 * (C.assemblyDimension : ℤ))
      (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant) _ :=
    νX.homologyConcentratedIn_mapDerivedCategory_obj h.2
  exact ⟨(ProEtale.DerivedCategory.boundedConstructible _ X).prop_of_iso e'.symm
      (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        h.1),
    (_root_.DerivedCategory.homologyConcentratedIn _ _).prop_of_iso e'.symm hh⟩

private theorem pro_assembly_tor
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (C : Scheme.SfAffineChartPresentation f) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K)
    (ht : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) ∧
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
      (a - 2 * (C.assemblyDimension : ℤ))
      (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
      ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hK.1
  let νX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  have htG : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b G :=
    (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht)
  have h := etale_assembly_tor Λ aY f C a b
    ⟨⟨hG, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htG⟩, htG⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} Λ) Y G hG.1.1
  let e' := ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso e).symm ≪≫
    νX.mapDerivedCategory.mapIso
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} Λ) Y).unit.app G)).symm)
  have hbc := (ProEtale.DerivedCategory.boundedConstructible _ X).prop_of_iso e'.symm
    (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      h.1.1)
  have ht' := (_root_.DerivedCategory.torAmplitudeIn _ _ _).prop_of_iso e'.symm
    (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory Λ h.2)
  exact ⟨⟨hbc, _, _, ht'⟩, ht'⟩


/-- The purity assembly gives constructibility, cohomological bounds, and the same
Tor bounds together with finite-Tor constructible membership. The supplied chart
family is arbitrary: `C.nonemptyCharts` omits empty source charts internally, exactly
as in the corollary. The numerical constants use this restricted family.
Source: blueprint cor-pur-general-admissibility-datum
(blueprint: cor-pur-general-admissibility-datum).

Proof:
1. Use the constructible comparison-transported exceptional functor. Its adjunction
   relative to bounded constructible inputs is cor-sf-ambient-adjoint-discharge;
   no unrestricted ambient pro-etale right adjoint is used.
2. If X is empty, every object of its small pro-etale site is empty and has the empty
   covering family. The sheaf condition forces every module of sections to be zero.
   All output cohomology and every degree-zero module-sheaf tensor test are therefore
   zero, giving both conclusions with D=c=0.
3. For nonempty X, apply `C.nonemptyCharts`: its source indices are exactly the
   subtypes of original indices with nonempty source, reindexed by `Fintype.equivFin`.
   Every original covering chart containing a point survives, so source_cover is
   retained. Every surviving source is nonempty by its subtype property; the target
   cover, embedding dimensions and closed presentations are inherited unchanged.
   The chart clause of
   thm-pur-open-complement-unconditional gives the open-complement condition on
   the complement of U in affine d_U-space over V, with bound 2(d_U+dim V).
   Since dim V is at most dim Y, this bound is at most c_U=2(d_U+dim Y).
4. The condition of def-exc-open-complement-bound is monotone in its bound:
   q>c_U implies q>2(d_U+dim V), so its vanishing clause still holds, while its
   constructibility clause is independent of the bound. Thus each chart satisfies
   the condition with precisely the chosen c_U.
5. Apply thm-pur-general-admissibility to f and `C.nonemptyCharts`, whose
   nonemptiness condition is supplied by the index subtype, without a premise on C.
   Its lower shift is -2D with D=`C.nonemptyCharts.maxDimension`, and its upper
   shift is -2D+c, where
   c=max(c_U+1+2(D-d_U)). Every summand equals 2D+2 dim Y+1, exactly the
   assemblyConstant above. The theorem supplies both the cohomological interval
   and finite-Tor constructible membership with the displayed Tor interval. -/
theorem sf_purity_affine_chart_bounds
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X Y : Scheme.{u})
    [X.Over (Spec (.of F.k))] [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))] [QuasiCompact (Y ↘ Spec (.of F.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of F.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) (C : SfAffineChartPresentation f) :
    ∀ (a b : ℤ) (_hab : a ≤ b),
      (∀ L : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          Y a b L →
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.assemblyDimension : ℤ))
          (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj L)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y a b K →
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K) ∧
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.assemblyDimension : ℤ))
          (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) := by
  classical
  let Λ := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let := Padic.finite_coefficientExtensionRing l E n hn
  let : HasCompactification f := ⟨⟨c⟩⟩
  let : HasInvertibleExponent Λ Y :=
    coefficient_invertible F l _hl E n Y (Y ↘ Spec (.of F.k))
  intro a b _hab
  constructor
  · intro L hL
    exact pro_assembly_constructible Λ (Y ↘ Spec (.of F.k)) f C a b hL
  · intro K hK ht
    exact pro_assembly_tor Λ (Y ↘ Spec (.of F.k)) f C a b hK ht

end AlgebraicGeometry.Scheme
