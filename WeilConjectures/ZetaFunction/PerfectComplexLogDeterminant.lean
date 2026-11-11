/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.CategoricalTrace
public import WeilConjectures.CategoryTheory.DerivedCategory.TraceLaws
public import WeilConjectures.ZetaFunction.CohomologicalFamily

/-!
# The logarithm of the determinant of an endomorphism of a perfect complex

Let `L` be a field of characteristic zero, `P` a perfect complex in `D(L)` and `v` an
endomorphism of `P`. Put `det(1 - T v ∣ P) = ∏ᵢ det(1 - T v ∣ Hⁱ(P))^{(-1)^i}`
(`LinearMap.alternatingCharpolyRevProd`). Then
```
det(1 - T v ∣ P)⁻¹ = exp (∑_{m ≥ 1} tr_L(v^m ∣ P) T^m / m)    in 1 + T L⟦T⟧,
```
where `tr_L(v^m ∣ P)` is the categorical trace of `v^m`, for the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product
(`DerivedCategory.IsPerfect.categoricalTrace`). This is the last clause of blueprint
`lemma-logarithm-determinant`.

## Main results

- `DerivedCategory.IsPerfect.trace_eq_algebraMap_sum_negOnePow_trace_homologyFunctor_map`: over a
  field, the categorical trace of an arbitrary endomorphism `w` of a perfect complex `P` is the
  alternating sum `∑ᵢ (-1)ⁱ Tr(Hⁱ(w) ∣ Hⁱ(P))`.
- `DerivedCategory.IsPerfect.inv_alternatingCharpolyRevProd_eq_exp`: the logarithm of the
  determinant (blueprint `lemma-logarithm-determinant--3`).

## Implementation notes

A perfect complex `P ≅ Q(C)` is represented by a bounded complex `C` of finitely generated
projective modules, which is K-projective; so every endomorphism of `P` comes from a chain
endomorphism of `C`, and the trace is computed by
`DerivedCategory.trace_eq_algebraMap_sum_negOnePow_trace_homologyMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {L : Type u} [Field L]

/-- The trace of the endomorphism of a module induced by `f` through an isomorphism `e` is the
trace of `f`. -/
lemma linearMapTrace_eq_of_iso {M N : ModuleCat.{u} L} (e : M ≅ N) (f : M ⟶ M) (g : N ⟶ N)
    (h : f ≫ e.hom = e.hom ≫ g) :
    LinearMap.trace L M f.hom = LinearMap.trace L N g.hom := by
  have hg : g = e.inv ≫ f ≫ e.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hg, ← LinearMap.trace_conj' f.hom e.toLinearEquiv]
  rfl

/-- The trace of an endomorphism of a zero module is zero. -/
lemma linearMapTrace_eq_zero_of_isZero {M : ModuleCat.{u} L} (hM : IsZero M) (f : M ⟶ M) :
    LinearMap.trace L M f.hom = 0 := by
  rw [hM.eq_of_src f 0, ModuleCat.hom_zero, map_zero]

variable [HasDerivedCategory.{u} (ModuleCat.{u} L)]

/-- **The trace over a field is the supertrace on cohomology**: for a perfect complex `P` of
`D(L)`, `L` a field, an endomorphism `w` of `P` and a finite set `s` of degrees outside of which
the cohomology of `P` vanishes, the categorical trace of `w`, for the Koszul braiding of the
derived tensor product, is `∑_{i ∈ s} (-1)ⁱ Tr(Hⁱ(w) ∣ Hⁱ(P))`. The endomorphism `w` is an
arbitrary morphism of `D(L)`, not necessarily induced by a chain map. -/
theorem IsPerfect.trace_eq_algebraMap_sum_negOnePow_trace_homologyFunctor_map
    {P : DerivedCategory (ModuleCat.{u} L)} (hP : P.IsPerfect) [HasRightDual P] (w : P ⟶ P)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero ((homologyFunctor (ModuleCat.{u} L) i).obj P)) :
    letI := braidedCategory' (ModuleCat.{u} L)
    MonoidalCategory.trace w =
      algebraMap L (End (𝟙_ (DerivedCategory (ModuleCat.{u} L))))
        (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace L
          ((homologyFunctor (ModuleCat.{u} L) i).obj P)
          ((homologyFunctor (ModuleCat.{u} L) i).map w).hom) := by
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hP
  have : C.IsStrictlyLE b := hb
  have : C.IsStrictlyGE a := ha
  have : ∀ n, Projective (C.X n) := fun n ↦
    (IsProjective.iff_projective (R := L) (C.X n)).1 (hC n).1
  have : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
  obtain ⟨v, hv⟩ := exists_Q_map_eq_of_isKProjective C C (e.inv ≫ w ≫ e.hom)
  have hw : w ≫ e.hom = e.hom ≫ Q.map v := by rw [hv, e.hom_inv_id_assoc]
  have hCs : ∀ i ∉ Finset.Icc a b, IsZero (C.X i) := fun i hi ↦ by
    rcases not_and_or.1 (Finset.mem_Icc.not.1 hi) with h | h
    · exact C.isZero_of_isStrictlyGE a i (by lia)
    · exact C.isZero_of_isStrictlyLE b i (by lia)
  rw [trace_eq_algebraMap_sum_negOnePow_trace_homologyMap C v (Finset.Icc a b) hCs
    (fun i ↦ (hC i).2) P w e hw]
  congr 1
  -- the cohomology of `P` is that of `C`, compatibly with `w` and `v`
  let eH (i : ℤ) : (homologyFunctor (ModuleCat.{u} L) i).obj P ≅ C.homology i :=
    (homologyFunctor (ModuleCat.{u} L) i).mapIso e ≪≫ (homologyFunctorFactors _ i).app C
  have htr (i : ℤ) : LinearMap.trace L _ ((homologyFunctor (ModuleCat.{u} L) i).map w).hom =
      LinearMap.trace L _ (HomologicalComplex.homologyMap v i).hom := by
    refine linearMapTrace_eq_of_iso (eH i) _ _ ?_
    have h := (homologyFunctorFactors (ModuleCat.{u} L) i).hom.naturality v
    simp only [Functor.comp_map] at h
    simp only [eH, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp_assoc,
      hw, Functor.map_comp, Category.assoc, h]
    rfl
  have hzero (i : ℤ) (hi : IsZero ((homologyFunctor (ModuleCat.{u} L) i).obj P)) :
      LinearMap.trace L _ (HomologicalComplex.homologyMap v i).hom = 0 :=
    (htr i).symm.trans (linearMapTrace_eq_zero_of_isZero hi _)
  have hzero' (i : ℤ) (hi : i ∉ Finset.Icc a b) :
      LinearMap.trace L _ (HomologicalComplex.homologyMap v i).hom = 0 := by
    refine linearMapTrace_eq_zero_of_isZero ?_ _
    rcases not_and_or.1 (Finset.mem_Icc.not.1 hi) with h | h
    · exact (C.exactAt_of_isGE a i (by lia)).isZero_homology
    · exact (C.exactAt_of_isLE b i (by lia)).isZero_homology
  simp_rw [htr]
  calc _ = ∑ i ∈ Finset.Icc a b ∪ s, (i.negOnePow : ℤ) •
        LinearMap.trace L _ (HomologicalComplex.homologyMap v i).hom :=
        Finset.sum_subset Finset.subset_union_left fun i _ hi ↦ by rw [hzero' i hi, smul_zero]
    _ = _ := (Finset.sum_subset Finset.subset_union_right fun i _ hi ↦ by
        rw [hzero i (hs i hi), smul_zero]).symm

/-- The cohomology of a perfect complex vanishes outside a finite set of degrees. -/
lemma IsPerfect.exists_finset_isZero_homology {P : DerivedCategory (ModuleCat.{u} L)}
    (hP : P.IsPerfect) :
    ∃ s : Finset ℤ, ∀ i ∉ s, IsZero ((homologyFunctor (ModuleCat.{u} L) i).obj P) := by
  obtain ⟨a, b, ha, hb⟩ := hP.exists_homologyConcentratedIn
  refine ⟨Finset.Icc a b, fun i hi ↦ ?_⟩
  rcases not_and_or.1 (Finset.mem_Icc.not.1 hi) with h | h
  · exact P.isZero_of_isGE a i (by lia)
  · exact P.isZero_of_isLE b i (by lia)

/-- The categorical trace on a perfect complex over a field is `L`-linear:
`tr_L(r • w ∣ P) = r • tr_L(w ∣ P)`. -/
theorem IsPerfect.trace_smul {P : DerivedCategory (ModuleCat.{u} L)} (hP : P.IsPerfect)
    [HasRightDual P] (r : L) (w : P ⟶ P) :
    letI := braidedCategory' (ModuleCat.{u} L)
    MonoidalCategory.trace (r • w) = r • MonoidalCategory.trace w := by
  obtain ⟨s, hs⟩ := hP.exists_finset_isZero_homology
  have := fun i ↦ homologyFunctor_linear L i
  rw [hP.trace_eq_algebraMap_sum_negOnePow_trace_homologyFunctor_map _ s hs,
    hP.trace_eq_algebraMap_sum_negOnePow_trace_homologyFunctor_map _ s hs,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Functor.map_smul, ModuleCat.hom_smul, map_smul, smul_eq_mul, mul_smul_comm]

omit [HasDerivedCategory.{u} (ModuleCat.{u} L)] in
/-- A functor to `L`-modules sends powers of an endomorphism to powers of linear maps. -/
lemma hom_map_pow {D : Type*} [Category D] (F : D ⥤ ModuleCat.{u} L) {X : D} (v : End X)
    (m : ℕ) : (F.map (v ^ m)).hom = (F.map v).hom ^ m := by
  induction m with
  | zero => simp [End.one_def]; rfl
  | succ m ih => rw [pow_succ, End.mul_def, F.map_comp, ModuleCat.hom_comp, ih, pow_succ,
      Module.End.mul_eq_comp]

/-- Blueprint `lemma-logarithm-determinant--3`: for a field `L` of characteristic zero, a perfect
complex `P` of `D(L)` and an endomorphism `v` of `P`, with
`det(1 - T v ∣ P) = ∏ᵢ det(1 - T v ∣ Hⁱ(P))^{(-1)^i}` (`LinearMap.alternatingCharpolyRevProd`,
the product over a finite set `s` of degrees outside of which the cohomology of `P` vanishes),
```
det(1 - T v ∣ P)⁻¹ = exp (∑_{m ≥ 1} tr_L(v^m ∣ P) T^m / m),
```
`tr_L(v^m ∣ P)` being the categorical trace (`DerivedCategory.IsPerfect.categoricalTrace`) for
the Koszul braiding of the derived tensor product. The coefficient of `T^0` of the series in the
exponential is `tr_L(1 ∣ P) / 0 = 0`. -/
theorem IsPerfect.inv_alternatingCharpolyRevProd_eq_exp [CharZero L]
    {P : DerivedCategory (ModuleCat.{u} L)} (hP : P.IsPerfect) (v : End P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero ((homologyFunctor (ModuleCat.{u} L) i).obj P)) :
    letI := braidedCategory' (ModuleCat.{u} L)
    letI (i : ℤ) : FiniteDimensional L ((homologyFunctor (ModuleCat.{u} L) i).obj P) :=
      hP.finite_homology i
    (LinearMap.alternatingCharpolyRevProd s
        (fun i ↦ ((homologyFunctor (ModuleCat.{u} L) i).map v).hom) 1)⁻¹ =
      (PowerSeries.exp L).subst (PowerSeries.mk fun m ↦ hP.categoricalTrace (v ^ m) / m) := by
  let := braidedCategory' (ModuleCat.{u} L)
  let (i : ℤ) : FiniteDimensional L ((homologyFunctor (ModuleCat.{u} L) i).obj P) :=
    hP.finite_homology i
  rw [LinearMap.inv_alternatingCharpolyRevProd_eq_exp]
  congr 1
  ext m
  rw [LinearMap.coeff_alternatingTraceSeries, PowerSeries.coeff_mk]
  split_ifs with hm
  · simp [hm]
  · congr 1
    let : HasRightDual P := hP.isDualizable.some
    rw [IsPerfect.categoricalTrace,
      hP.trace_eq_algebraMap_sum_negOnePow_trace_homologyFunctor_map (v ^ m) s hs,
      unitEndScalar_algebraMap]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hom_map_pow]

end DerivedCategory
