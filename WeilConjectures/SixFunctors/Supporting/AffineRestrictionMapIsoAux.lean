/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import all WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleLocallyClosedShriek
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMateNormalization
import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart

/-! # Invertibility of the finite dualizing comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private instance finite_coeff (j : ℕ) : Finite (finiteDualizingCoeff l E j) :=
  Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E (j + 1) (Nat.succ_pos j))

open AlgebraicGeometry.Etale in
attribute [local instance 2000] CommRing.toRing in
private theorem regular_unit_ctf
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (𝟙_ _) :=
  ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (Etale.DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

open AlgebraicGeometry.Etale in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [local instance 2000] CommRing.toRing in
private theorem dualizing_finiteTor (hl : l ≠ D.p) (Y : Scheme.{u})
    [Y.Over (Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] (j : ℕ) :
    DerivedCategory.isBoundedConstructible (finiteDualizingCoeff l E j) Y
        (dualizingComplex (finiteDualizingCoeff l E j) (Y ↘ Spec (.of D.k))) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
        (finiteDualizingCoeff l E j) Y a b
        (dualizingComplex (finiteDualizingCoeff l E j) (Y ↘ Spec (.of D.k))) := by
  let A := finiteDualizingCoeff l E j
  let S := Spec (.of D.k)
  let : HasInvertibleExponent A S :=
    Etale.coefficient_hasInvertibleExponent D l hl E (j + 1) (Nat.succ_pos j) S (𝟙 S)
  have hω := Etale.constructibleFiniteTor_dualizingComplex A (𝟙 S)
    (Y ↘ S) (regular_unit_ctf A S)
  exact (Etale.finiteTor_iff A Y _).2 hω

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem counit_mate_changeAdjunction_isIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G H : D ⥤ C} {F' : C' ⥤ D'} {G' H' : D' ⥤ C'}
    (a : F ⊣ G) (a' : F ⊣ H) (b : F' ⊣ G') (b' : F' ⊣ H')
    (Q : C ⥤ C') (T : D ⥤ D') (d : F ⋙ T ≅ Q ⋙ F') (M : D)
    (x : Etale.CoefficientCounitMateData a' b' Q T d M)
    (y : Etale.CoefficientCounitMateData a b Q T d M)
    (hi : IsIso x.hom) : IsIso y.hom := by
  let e := a.rightAdjointUniq a'
  let e' := b.rightAdjointUniq b'
  have he : F.map (e.hom.app M) ≫ a'.counit.app M = a.counit.app M :=
    a.rightAdjointUniq_hom_app_counit a' M
  have he' : F'.map (e'.hom.app (T.obj M)) ≫ b'.counit.app (T.obj M) =
      b.counit.app (T.obj M) := b.rightAdjointUniq_hom_app_counit b' _
  have h : y.hom ≫ e'.hom.app (T.obj M) = Q.map (e.hom.app M) ≫ x.hom := by
    apply (b'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [he', y.counit, x.counit]
    have hn := d.inv.naturality (e.hom.app M)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← T.map_comp, he]
  have : IsIso x.hom := hi
  have : IsIso (Q.map (e.hom.app M) ≫ x.hom) := inferInstance
  have : IsIso (y.hom ≫ e'.hom.app (T.obj M)) := h.symm ▸ this
  exact (isIso_comp_right_iff _ _).1 this

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem closed_mate_isIso_of_etaleComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y P : Scheme.{u}} [IsNoetherian Y] [IsNoetherian P]
    (i : Y ⟶ P) [IsClosedImmersion i] (M : Etale.DerivedCategoryModule A P)
    (hi : IsIso (Etale.etaleShriekClosedCoefficientMap φ i M)) :
    IsIso (Etale.closedDualizingCoefficientMate φ i M) := by
  have hc (N : Etale.DerivedCategoryModule A Y) :
      Etale.finiteCoefficientDirectImageMap φ i N = (Etale.closedScalarIso φ i).hom.app N := by
    rw [Etale.closedScalarIso_hom_app, Etale.finiteCoefficientDirectImageMap_eq_mate]
    rfl
  have hcIso (N : Etale.DerivedCategoryModule A Y) :
      IsIso (Etale.finiteCoefficientDirectImageMap φ i N) := by
    rw [hc]
    infer_instance
  let x : Etale.CoefficientCounitMateData
      (Etale.etaleShriekClosedAdjunction A i) (Etale.etaleShriekClosedAdjunction B i)
      (Etale.scalarExtension φ Y) (Etale.scalarExtension φ P) (Etale.closedScalarIso φ i) M :=
    { hom := Etale.etaleShriekClosedCoefficientMap φ i M
      counit := by
        let := hcIso ((Etale.etaleShriekClosedExceptional A i).obj M)
        apply (cancel_epi ((Etale.closedScalarIso φ i).hom.app _)).1
        simp only [Iso.hom_inv_id_app_assoc]
        rw [← hc]
        exact Etale.closedCoefficient_counit φ i M }
  exact counit_mate_changeAdjunction_isIso _ _ _ _ _ _ _ _ x
    (Etale.closedCoefficientMateData φ i M) hi

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The closed-chart coefficient mate is invertible at the affine-space dualizing complex.

Source: finite dualizing proof, paragraphs 1 and 3 (blueprint: affine-closed-mate-isIso).
The dualizing complex of the affine space at level `m + 1` is bounded constructible of
finite Tor amplitude (`coefDualizingConstruction`). The ordinary etale locally closed
coefficient comparison at levels `m + 1 ≥ n + 1`, with closed immersion `i` and identity
open, makes its closed coefficient map invertible. That map and the specified mate are
counit-defined mates for two right adjoints of the same closed direct image; the canonical
`rightAdjointUniq` isomorphisms intertwine their counits, and the direct-image comparison
is the hom of `closedScalarIso`, so the two mates differ by isomorphisms and the specified
mate is invertible. -/
theorem closed_mate_isIso_aux (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (r : ℕ) (Y : Scheme.{u}) [IsAffine Y]
    (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))
    [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘
      Spec (.of D.k)) = aY)
    [IsNoetherian Y]
    [IsNoetherian (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))] :
    IsIso (Etale.closedDualizingCoefficientMate (finiteDualizingQuotient l E h) i
      (Etale.dualizingComplex (finiteDualizingCoeff l E m)
        (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)))) := by
  have _ := hi
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  have hω := dualizing_finiteTor l E D hl P m
  have hcomp := Etale.etaleLocallyClosedShriekComparisons D l hl E
    (m + 1) (n + 1) (Nat.add_le_add_right h 1) (Nat.succ_le_succ (Nat.zero_le n))
    P i (𝟙 Y)
  have hi := (hcomp.2.1 _ hω).2.2.2.1
  exact closed_mate_isIso_of_etaleComparison (finiteDualizingQuotient l E h) i _ hi

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem closed_mate_isIso (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (r : ℕ) (Y : Scheme.{u}) [IsAffine Y]
    (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))
    [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘
      Spec (.of D.k)) = aY)
    [IsNoetherian Y]
    [IsNoetherian (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))] :
    IsIso (Etale.closedDualizingCoefficientMate (finiteDualizingQuotient l E h) i
      (Etale.dualizingComplex (finiteDualizingCoeff l E m)
        (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)))) := by
  exact closed_mate_isIso_aux l E D hl h r Y aY i hi

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem affine_space_mate_isIso (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m)
    (r : ℕ) :
    IsIso (Etale.ExceptionalCoefficients.dualizingScalarMap (finiteDualizingQuotient l E h)
      (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k))) := by
  let A := finiteDualizingCoeff l E m
  let B := finiteDualizingCoeff l E n
  let φ : A →+* B := finiteDualizingQuotient l E h
  let S := Spec (.of D.k)
  let P : Scheme := AffineSpace (ULift.{u} (Fin r)) S
  let : IsSeparated (P ↘ S) := by infer_instance
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hDVR := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hDVR.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hlmem : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (hDVR.2.1 _).2
    change spectralNorm (Padic l) E (l : E) < 1
    simpa only [map_natCast] using
      (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)).trans_lt
        (Padic.norm_p_lt_one (p := l))
  have hA : ((l ^ (m + 1) : ℕ) : A) = 0 := by
    apply ULift.down_injective
    change ((l ^ (m + 1) : ℕ) : Padic.coefficientExtensionRing l E (m + 1)) = 0
    apply (map_natCast (Ideal.Quotient.mk _) (l ^ (m + 1))).symm.trans
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow (hgen.symm ▸ hlmem) (m + 1)
  have hB : ((l ^ (m + 1) : ℕ) : B) = 0 := by
    exact (map_natCast φ (l ^ (m + 1))).symm.trans
      ((congrArg φ hA).trans (map_zero φ))
  have hS : IsUnit ((l ^ (m + 1) : ℕ) : Γ(S, ⊤)) := by
    have hu : IsUnit ((l ^ (m + 1) : ℕ) : D.k) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : l.Prime) hl.symm)).pow _
    simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (P ↘ S)
  have : IsNoetherian P := ⟨⟩
  let e : P ⟶ affineTraceTower S r := (affineTraceAffineSpaceIso S r).inv
  have he : (𝟙 P) ≫ (P ↘ S) = e ≫ affineTraceProjection S r := by
    rw [Category.id_comp]
    apply (cancel_epi (affineTraceAffineSpaceIso S r).hom).mp
    simp only [e, Iso.hom_inv_id_assoc]
    exact AffineSpace.homOfVector_over _ _
  have hN : 0 < l ^ (m + 1) := pow_pos (Fact.out : l.Prime).pos _
  obtain ⟨MA⟩ := Etale.nonempty_etaleCompactSupportNormalization A
  obtain ⟨MB⟩ := Etale.nonempty_etaleCompactSupportNormalization B
  obtain ⟨tA, PA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (l ^ (m + 1)) hN A hA
  obtain ⟨tB, PB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (l ^ (m + 1)) hN B hB
  let RB := ProEtale.reductionEtaleChartRightIso B MB (P ↘ S) (𝟙 P) r e he
    (HasCompactification.compactification (P ↘ S))
    (Etale.rightDerivedUpperShriek B (P ↘ S))
    (Etale.rightDerivedUpperShriekAdjunction B (P ↘ S))
    (l ^ (m + 1)) hB tB PB hS
  have hc := Etale.ordinary_chart_exceptional_scalar φ (l ^ (m + 1)) hN hA hB hS
    (P ↘ S) (𝟙 P) r e he MA MB tA tB PA PB (𝟙_ _)
  have hi : IsIso ((Etale.scalarPullbackIso φ (𝟙 P)).inv.app
        ((Etale.rightDerivedUpperShriek A (P ↘ S)).obj (𝟙_ _)) ≫
      (Etale.ordinaryFinitePullback B (𝟙 P)).map
        (Etale.ExceptionalCoefficients.mateMap φ (P ↘ S) (𝟙_ _)) ≫
      RB.hom.app ((Etale.scalarExtension φ S).obj (𝟙_ _))) := by
    rw [← hc]
    infer_instance
  have := (isIso_comp_left_iff _ _).1 hi
  have := (isIso_comp_right_iff _ _).1 this
  let : (Etale.ordinaryFinitePullback B (𝟙 P)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} B) P).symm
  have hm : IsIso (Etale.ExceptionalCoefficients.mateMap φ (P ↘ S) (𝟙_ _)) :=
    isIso_of_reflects_iso _ (Etale.ordinaryFinitePullback B (𝟙 P))
  unfold Etale.ExceptionalCoefficients.dualizingScalarMap
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparison_eq_dualizingScalarMap {m n : ℕ} (h : n ≤ m) :
    let := (finiteDualizingCompactification D X).hasCompactification
    finiteDualizingEtaleComparison l E D X h =
      Etale.ExceptionalCoefficients.dualizingScalarMap (finiteDualizingQuotient l E h)
        (X ↘ Spec (.of D.k)) := by
  let := (finiteDualizingCompactification D X).hasCompactification
  dsimp only
  rw [Etale.scalarMap_eq_globalMate]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The global finite dualizing comparison is invertible.

Source: the closed-chart descent and affine-space comparison in
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md`, paragraphs 1--3 (blueprint:
`affine-restriction-map-iso`).  The proof first applies the proper/open
coefficient comparison to the compactification of `X`, then identifies the
resulting mate on each affine chart with the affine-space comparison after a
closed-chart embedding.  Both component comparisons are isomorphisms, and
the jointly-surjective affine cover reflects isomorphisms of derived etale
objects.  Thus the specified counit-defined global mate is an isomorphism;
the argument also covers an empty affine chart because its derived category
is zero. -/
theorem finiteDualizing_etaleComparison_isIso_for_factorization (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    IsIso (finiteDualizingEtaleComparison l E D X h) := by
  let := (finiteDualizingCompactification D X).hasCompactification
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  rw [comparison_eq_dualizingScalarMap]
  have hω := dualizing_finiteTor l E D hl X m
  have hlocal (V : X.affineOpens) :
      IsIso ((Etale.derivedRestriction (A := finiteDualizingCoeff l E n) V.1.ι).map
        (Etale.ExceptionalCoefficients.dualizingScalarMap (finiteDualizingQuotient l E h)
          (X ↘ Spec (.of D.k)))) := by
    have : IsAffine V.1.toScheme := V.2
    let Y := V.1.toScheme
    let aY := V.1.ι ≫ (X ↘ Spec (.of D.k))
    obtain ⟨r, i, he, hi⟩ := exists_isClosedImmersion_affineSpace_of_isAffine aY
    let : IsClosedImmersion i := hi
    let P : Scheme := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
    let : IsSeparated (P ↘ Spec (.of D.k)) := by infer_instance
    have : IsNoetherian Y := ⟨⟩
    have : IsLocallyNoetherian P :=
      LocallyOfFiniteType.isLocallyNoetherian (P ↘ Spec (.of D.k))
    have : CompactSpace P :=
      QuasiCompact.compactSpace_of_compactSpace (P ↘ Spec (.of D.k))
    have : IsNoetherian P := ⟨⟩
    obtain ⟨eA, eB, heq⟩ := Etale.closedOpen_dualizingMate_normalization
      (finiteDualizingQuotient l E h) (X ↘ Spec (.of D.k)) V.1.ι i
      (P ↘ Spec (.of D.k)) he.symm hω
    have := closed_mate_isIso l E D hl h r Y aY i he
    have := affine_space_mate_isIso l E D hl h r
    have hi : IsIso ((Etale.openScalarRestriction (finiteDualizingQuotient l E h)
        V.1.ι).hom.app _ ≫
      (Etale.derivedRestriction (A := finiteDualizingCoeff l E n) V.1.ι).map
        (Etale.ExceptionalCoefficients.dualizingScalarMap (finiteDualizingQuotient l E h)
          (X ↘ Spec (.of D.k))) ≫ eB.hom) := by
      rw [heq]
      infer_instance
    exact (isIso_comp_right_iff _ eB.hom).1 ((isIso_comp_left_iff _ _).1 hi)
  have ha : ∀ x : X, ∃ (i : X.affineOpens) (y : (i : X.Opens)),
      (i : X.Opens).ι.base y = x := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩
  exact Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective
    (finiteDualizingCoeff l E n) (ι := X.affineOpens)
    (fun V ↦ (V : X.Opens).ι) ha _ hlocal

end WeilConjectures
