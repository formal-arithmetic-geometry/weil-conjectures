/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosedHenselian
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified

/-!

# The fraction field of a generic slice trait is separably closed in `K((t))`

Let `S' = Spec R` be a generic slice trait (`AlgebraicGeometry.GenericSliceTrait`) with
`ι : R ⟶ K⟦t⟧`, `K = k'(x)^alg`, and suppose that the residues `ι(r)(0) ∈ K` are separable
over `k'(x)` (true for the strict localization of `𝔸¹_S`). Then, with `κ = k'(x)^sep ⊆ K`:

* the constants `κ` lie in `ι(R)`
  (`AlgebraicGeometry.GenericSliceTrait.C_mem_range_ι`): an element of `κ` is a simple root of a
  polynomial over `k'[x] ⊆ R`, it is the residue of an element of `R` as the residue field of
  `R` is separably closed, and Hensel's lemma lifts it to a root in `R`, whose image is the
  constant root by uniqueness of simple roots in `K⟦t⟧`;
* `ι(R) ⊆ κ⟦t⟧` (`AlgebraicGeometry.GenericSliceTrait.coeff_ι_mem`), by induction on the
  coefficients;
* hence `Frac R` is separably closed in `K((t))`
  (`AlgebraicGeometry.GenericSliceTrait.mem_range_of_isSeparable`,
  from `IsDiscreteValuationRing.mem_range_fractionRingLift_of_isSeparable`).

This is the field-theoretic input of SGA 4½, [Th. finitude], 3.3–3.4 for the generic slice.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing Polynomial

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The chart `k'⟦t⟧[x] ⟶ R` of `S' ⟶ 𝔸¹_S`. -/
noncomputable def chart : MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k') →+* D.R :=
  (Spec.preimage (D.toAffineLine ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).hom)).hom

lemma ι_comp_chart : D.ι.comp D.chart = traitSliceRingHom (traitSliceCoord k') := by
  have h := D.spec_ι_comp
  have h' : Spec.map (CommRingCat.ofHom (D.ι.comp D.chart)) =
      Spec.map (CommRingCat.ofHom (traitSliceRingHom (traitSliceCoord k'))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, chart, CommRingCat.ofHom_hom, Spec.map_preimage,
      ← Category.assoc, h, traitSlice, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

/-- The coordinate `x̃ ∈ R`, with `ι x̃ = x`. -/
noncomputable def coord : D.R := D.chart (MvPolynomial.X ⟨0⟩)

lemma ι_coord : D.ι D.coord = PowerSeries.C (traitSliceCoord k') := by
  rw [coord, ← RingHom.comp_apply, ι_comp_chart, traitSliceRingHom, MvPolynomial.eval₂Hom_X']

/-- The map `k'[x] ⟶ R`, `x ↦ x̃`. -/
noncomputable def polyMap : k'[X] →+* D.R :=
  Polynomial.eval₂RingHom (D.φ.comp (PowerSeries.C (R := k'))) D.coord

lemma ι_comp_polyMap : D.ι.comp D.polyMap =
    (PowerSeries.C (R := traitSliceField k')).comp
      (Polynomial.aeval (traitSliceCoord k')).toRingHom := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · have h := congrArg (fun f ↦ f (PowerSeries.C a)) D.ι_comp_φ
    simp only [RingHom.coe_comp, Function.comp_apply, PowerSeries.map_C] at h
    simp [polyMap, h]
  · simp [polyMap, ι_coord]

/-- The residue `r ↦ ι(r)(0)`, with values in `K`. -/
noncomputable abbrev residueMap : D.R →+* traitSliceField k' :=
  (PowerSeries.constantCoeff (R := traitSliceField k')).comp D.ι

lemma residueMap_eq_zero_iff (r : D.R) : D.residueMap r = 0 ↔ r ∈ maximalIdeal D.R := by
  rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff D.ι,
    PowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]
  rfl

instance : IsLocalHom D.residueMap :=
  ⟨fun r hr ↦ by
    by_contra h
    exact hr.ne_zero ((D.residueMap_eq_zero_iff r).2 h)⟩

/-- **Hensel lifting of constant simple roots**: let `G` be a polynomial over `R` whose image in
`K⟦t⟧` has constant coefficients and whose residue polynomial is separable. Every root `α ∈ K` of
the residue polynomial is the image of a root of `G` in `R`: `ι r = α`. -/
theorem exists_isRoot_ι_eq_C (G : D.R[X])
    (hG : G.map D.ι = (G.map D.residueMap).map (PowerSeries.C (R := traitSliceField k')))
    (hsep : (G.map D.residueMap).Separable) {α : traitSliceField k'}
    (hα : (G.map D.residueMap).eval α = 0) :
    ∃ r, G.IsRoot r ∧ D.ι r = PowerSeries.C α := by
  -- `α` is a residue
  let ρ := ResidueField.lift D.residueMap
  have hρ : ρ.comp (residue D.R) = D.residueMap := ResidueField.lift_comp_residue _
  let Gb := G.map (residue D.R)
  have hGb : Gb.map ρ = G.map D.residueMap := by rw [Polynomial.map_map, hρ]
  have hGbsep : Gb.Separable := (Polynomial.separable_map ρ).1 (hGb ▸ hsep)
  let _ := ρ.toAlgebra
  have hGb0 : Gb ≠ 0 := hGbsep.ne_zero
  have hroot : aeval α Gb = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact (congrArg (eval α) hGb).trans hα
  have hint := (show IsAlgebraic (ResidueField D.R) α from ⟨Gb, hGb0, hroot⟩).isIntegral
  have hdeg : (minpoly (ResidueField D.R) α).natDegree = 1 := by
    have := IsSepClosed.degree_eq_one_of_irreducible (ResidueField D.R) (minpoly.irreducible hint)
      (hGbsep.of_dvd (minpoly.dvd _ _ hroot))
    exact natDegree_eq_of_degree_eq_some this
  obtain ⟨β, hβ⟩ := minpoly.natDegree_eq_one_iff.1 hdeg
  obtain ⟨r₀, rfl⟩ := residue_surjective β
  have hr₀ : D.residueMap r₀ = α := by rw [← hβ, ← hρ]; rfl
  -- Hensel
  have hmap : ∀ (H : D.R[X]) (r : D.R), D.residueMap (H.eval r) =
      (H.map D.residueMap).eval (D.residueMap r) := fun H r ↦ by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hder : (G.map D.residueMap).derivative.eval α ≠ 0 := by
    exact hsep.eval₂_derivative_ne_zero (RingHom.id _) hα
  obtain ⟨r, hr, hrr₀⟩ := HenselianLocalRing.exists_isRoot_sub_mem G r₀
    ((D.residueMap_eq_zero_iff _).1 (by rw [hmap, hr₀, hα]))
    (by
      by_contra h
      apply hder
      rw [← hr₀, Polynomial.derivative_map, ← hmap]
      exact (D.residueMap_eq_zero_iff _).2 h)
  have hrα : D.residueMap r = α := by
    rw [← hr₀, ← sub_eq_zero, ← map_sub]
    exact (D.residueMap_eq_zero_iff _).2 hrr₀
  refine ⟨r, hr, ?_⟩
  -- uniqueness of simple roots in `K⟦t⟧`
  have hy : (G.map D.ι).IsRoot (D.ι r) := by
    rw [IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hr.eq_zero, map_zero]
  have hC : (G.map D.ι).IsRoot (PowerSeries.C α) := by
    rw [hG, IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hα, map_zero]
  rcases Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot hy hC with h | h
  · exact h
  · exfalso
    have hd : PowerSeries.constantCoeff ((G.map D.ι).derivative.eval (D.ι r)) ≠ 0 := by
      rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_hom]
      change D.residueMap _ ≠ 0
      rw [hmap, ← Polynomial.derivative_map, hrα]
      exact hder
    have hu := isUnit_of_dvd_unit h
      (PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hd))
    rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C] at hu
    change IsUnit (D.residueMap r - α) at hu
    rw [hrα, sub_self] at hu
    exact not_isUnit_zero hu

lemma isUnit_polyMap (y : nonZeroDivisors k'[X]) : IsUnit (D.polyMap y) := by
  refine isUnit_of_map_unit D.ι _ ?_
  rw [← RingHom.comp_apply, ι_comp_polyMap, RingHom.comp_apply,
    PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C, isUnit_iff_ne_zero]
  exact fun h ↦ transcendental_traitSliceCoord k' ⟨y, nonZeroDivisors.ne_zero y.2, h⟩

/-- The map `k'(x) ⟶ R`, `x ↦ x̃`. -/
noncomputable def ratFuncMap : RatFunc k' →+* D.R :=
  IsLocalization.lift (M := nonZeroDivisors k'[X]) D.isUnit_polyMap

lemma algebraMap_ratFunc_comp :
    (algebraMap (RatFunc k') (traitSliceField k')).comp (algebraMap k'[X] (RatFunc k')) =
      (Polynomial.aeval (traitSliceCoord k')).toRingHom := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RatFunc.algebraMap_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Polynomial.aeval_C, ← RatFunc.algebraMap_eq_C]
    exact (IsScalarTower.algebraMap_apply k' (RatFunc k') _ a).symm
  · simp [traitSliceCoord, RatFunc.algebraMap_X]

lemma ι_comp_ratFuncMap : D.ι.comp D.ratFuncMap =
    (PowerSeries.C (R := traitSliceField k')).comp
      (algebraMap (RatFunc k') (traitSliceField k')) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors k'[X]) ?_
  rw [RingHom.comp_assoc, ratFuncMap, IsLocalization.lift_comp, ι_comp_polyMap, RingHom.comp_assoc,
    algebraMap_ratFunc_comp]

/-- **The constants `k'(x)^sep` lie in `ι(R)`.** -/
theorem C_mem_range_ι {α : traitSliceField k'}
    (hα : α ∈ separableClosure (RatFunc k') (traitSliceField k')) :
    PowerSeries.C α ∈ D.ι.range := by
  rw [mem_separableClosure_iff] at hα
  set p := minpoly (RatFunc k') α
  have hcomp : D.residueMap.comp D.ratFuncMap = algebraMap (RatFunc k') (traitSliceField k') := by
    rw [residueMap, RingHom.comp_assoc, ι_comp_ratFuncMap, ← RingHom.comp_assoc]
    ext a
    simp
  have hρ : (p.map D.ratFuncMap).map D.residueMap = p.map (algebraMap _ _) := by
    rw [Polynomial.map_map, hcomp]
  obtain ⟨r, -, hr⟩ := D.exists_isRoot_ι_eq_C (p.map D.ratFuncMap)
    (by rw [hρ, Polynomial.map_map, Polynomial.map_map, ι_comp_ratFuncMap])
    (by rw [hρ]; exact (Polynomial.separable_map _).2 hα)
    (by rw [hρ, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, minpoly.aeval])
  exact ⟨r, hr⟩

/-- The uniformizer `t ∈ R`. -/
noncomputable def uniformizer : D.R := D.φ PowerSeries.X

lemma maximalIdeal_eq_span_uniformizer :
    maximalIdeal D.R = Ideal.span {D.uniformizer} := by
  rw [D.maximalIdeal_eq, PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
    uniformizer]

lemma irreducible_uniformizer : Irreducible D.uniformizer :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 D.maximalIdeal_eq_span_uniformizer

lemma ι_uniformizer : D.ι D.uniformizer = PowerSeries.X := by
  rw [uniformizer, ← RingHom.comp_apply, ι_comp_φ, PowerSeries.map_X]

/-- **`ι(R) ⊆ k'(x)^sep⟦t⟧`** when the residues are separable over `k'(x)`. -/
theorem coeff_ι_mem
    (hres : ∀ r, D.residueMap r ∈ separableClosure (RatFunc k') (traitSliceField k'))
    (n : ℕ) (r : D.R) :
    PowerSeries.coeff n (D.ι r) ∈ separableClosure (RatFunc k') (traitSliceField k') := by
  induction n generalizing r with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hres r
  | succ n ih =>
    obtain ⟨r₀, hr₀⟩ := D.C_mem_range_ι (hres r)
    have hm : r - r₀ ∈ maximalIdeal D.R := by
      rw [← D.residueMap_eq_zero_iff, map_sub, sub_eq_zero]
      change _ = PowerSeries.constantCoeff (D.ι r₀)
      rw [hr₀, PowerSeries.constantCoeff_C]
    rw [D.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton'] at hm
    obtain ⟨r₁, hr₁⟩ := hm
    have : D.ι r = PowerSeries.C (D.residueMap r) + PowerSeries.X * D.ι r₁ := by
      rw [← hr₀, ← D.ι_uniformizer, ← map_mul, ← map_add, mul_comm, hr₁, add_sub_cancel]
    rw [this, map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), zero_add,
      PowerSeries.coeff_succ_X_mul]
    exact ih r₁

/-- **`Frac R` is separably closed in `K((t))`** for a generic slice trait whose residues are
separable over `k'(x)`. -/
theorem mem_range_of_isSeparable
    (hres : ∀ r, D.residueMap r ∈ separableClosure (RatFunc k') (traitSliceField k'))
    (y : FractionRing (PowerSeries (traitSliceField k')))
    (hy : letI := (IsDiscreteValuationRing.fractionRingLift D.ι D.injective_ι).toAlgebra
      IsSeparable (FractionRing D.R) y) :
    y ∈ (IsDiscreteValuationRing.fractionRingLift D.ι D.injective_ι).range := by
  have : Algebra.IsAlgebraic (separableClosure (RatFunc k') (traitSliceField k'))
      (traitSliceField k') := Algebra.IsAlgebraic.tower_top (K := RatFunc k') _
  exact IsDiscreteValuationRing.mem_range_fractionRingLift_of_isSeparable D.ι
    D.irreducible_uniformizer D.ι_uniformizer D.injective_ι
    (κ := separableClosure (RatFunc k') (traitSliceField k'))
    (by rw [trdeg_eq_zero]; exact zero_le_one)
    (fun a ↦ D.C_mem_range_ι a.2) (fun r n ↦ ⟨⟨_, D.coeff_ι_mem hres n r⟩, rfl⟩) y hy

end AlgebraicGeometry.GenericSliceTrait
