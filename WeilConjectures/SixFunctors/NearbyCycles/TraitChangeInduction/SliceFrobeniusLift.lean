/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceUnramifiedRoots
public import WeilConjectures.TraceFormula.Specialization.SliceTraitAlgebraic
public import WeilConjectures.RingTheory.Valuation.FrobeniusLiftApprox
public import WeilConjectures.RingTheory.Valuation.GaussResidue
public import WeilConjectures.FieldTheory.FrobeniusClosedBasisSubfield

/-!

# Lifts of Frobenius-closed bases in the slice compositum

Let `D` be the strict-localization slice trait over a strictly henselian trait `R` with residue
characteristic `p`, and `L = Ω(R') ⊆ Ω'` its compositum. Every element `α ∈ L` lies, together with
the coordinate `x`, in a discretely valued subfield `D₀ ⊆ L` whose residue field `E` is a finite
separable extension of `k(x̄)`, `k` the (algebraically closed) residue field of `Ω`. The abstract
package `ValuationSubring.exists_frobeniusLift_package` applied to lifts of a Frobenius-closed
`k`-basis of `E` (`FrobeniusClosedBasis.exists_of_subfield`) then gives the approximation package
used in the proof of the relative separable closedness of the slice composita
(`AlgebraicGeometry.SliceTrait.exists_frobeniusLift_package`).

The field `D₀ = K₀(x, a₁, …, aₙ)` is generated over the discrete subfield `K₀ ⊆ Ω` with full
residue field by the coordinate and finitely many elements of `R'`. It is discretely valued
since it lies in the unramified radical extension `B` of `Frac R'`
(`AlgebraicGeometry.SliceTrait.exists_unramified_subfields`), its residue field is separable over
`k(x̄)` for the same reason, and finite over `k(x̄)` by the Gauss valuation on `K₀(x)`
(`ValuationSubring.residue_mem_adjoin_of_mem_adjoin`), since `R'` is algebraic over `R[x]`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

section General

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)

attribute [local instance] algebraFracΩ algebraFrac algebraValuationSubring
  algebraBaseValuationSubring

/-- **The residue of the coordinate is transcendental over the residue field of `Ω`.** The
residues of the integral elements of `Ω` are purely inseparable over the residue field `κ` of
`R`, over which the residue `x̄` is transcendental. -/
lemma transcendental_residue_a [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] {x : D.R}
    (htr : Transcendental (ResidueField R) (residue D.R x)) :
    Transcendental (D.valuationSubring.residueSubfield D.ωS.fieldRange)
      (residue D.valuationSubring (algebraMap D.R D.valuationSubring x)) := by
  set ℓ := ResidueField D.valuationSubring
  set k := D.valuationSubring.residueSubfield D.ωS.fieldRange
  set P := perfectClosure (ResidueField R) ℓ
  have h1 : Transcendental (ResidueField R) (residue D.valuationSubring
      (algebraMap D.R D.valuationSubring x)) := by
    rw [← ResidueField.algebraMap_residue, transcendental_algebraMap_iff
      (algebraMap (ResidueField D.R) ℓ).injective]
    exact htr
  have hkP : k ≤ P.toSubfield := by
    rintro _ ⟨y, ⟨ω, hω⟩, rfl⟩
    obtain ⟨y, hy⟩ := y
    dsimp only at hω
    subst hω
    exact D.residue_mem_perfectClosure hy
  intro halg
  letI : Algebra k P := (Subfield.inclusion hkP).toAlgebra
  haveI : IsScalarTower k P ℓ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact h1 ((halg.tower_top P).restrictScalars (ResidueField R))

/-- **`R'` is algebraic over `K₀(x)`.** If `R'` is algebraic over `R[x]` (via `g`, with `x̄`
transcendental over `κ`) and `K₀ ⊆ Ω` contains `R`, then every element of `R'` is algebraic
over `K₀(x)`: the polynomials in `x` over `R` do not vanish in `Ω'`, by the Gauss valuation. -/
lemma isAlgebraic_a_adjoin_coord [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]
    (g : MvPolynomial (ULift.{u} (Fin 1)) R →+* D.R) (hgC : g.comp MvPolynomial.C = D.φ)
    (htr : Transcendental (ResidueField R) (residue D.R (g (MvPolynomial.X ⟨0⟩))))
    {K₀ : Subfield D.Ω} (hK₀K : K₀ ≤ D.ωS.fieldRange) (hφK₀ : ∀ r : R, D.a (D.φ r) ∈ K₀)
    {r : D.R} (hr : ∃ f : Polynomial (MvPolynomial (ULift.{u} (Fin 1)) R),
      f ≠ 0 ∧ (f.map g).eval r = 0) :
    IsAlgebraic (adjoin K₀ {D.a (g (MvPolynomial.X ⟨0⟩))}) (D.a r) := by
  set x₀ := g (MvPolynomial.X ⟨0⟩) with hx₀
  set F₁ := adjoin K₀ {D.a x₀} with hF₁
  let φ'' : R →+* K₀ := (D.a.comp D.φ).codRestrict K₀ hφK₀
  have heval (c : MvPolynomial (ULift.{u} (Fin 1)) R) : D.a (g c) =
      Polynomial.aeval (D.a x₀) ((MvPolynomial.uniqueAlgEquiv R _ c).map φ'') := by
    conv_lhs => rw [← (MvPolynomial.uniqueAlgEquiv R _).symm_apply_apply c]
    generalize MvPolynomial.uniqueAlgEquiv R _ c = P
    rw [MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.hom_eval₂, hgC,
      Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hmem (c : MvPolynomial (ULift.{u} (Fin 1)) R) : D.a (g c) ∈ F₁ := by
    rw [heval]
    exact algebra_adjoin_le_adjoin K₀ _ (Polynomial.aeval_mem_adjoin_singleton K₀ _)
  have hinj (c : MvPolynomial (ULift.{u} (Fin 1)) R) (hc : D.a (g c) = 0) : c = 0 := by
    by_contra hc0
    set P := (MvPolynomial.uniqueAlgEquiv R _ c).map φ'' with hP
    have hP0 : P ≠ 0 := by
      rw [hP, Polynomial.map_ne_zero_iff ((D.injective_a.comp D.injective_φ).codRestrict _)]
      exact (map_ne_zero_iff _ (MvPolynomial.uniqueAlgEquiv R _).injective).2 hc0
    have hv := ValuationSubring.valuation_aeval_eq_sup
      (D.valuationSubring.residueSubfield_mono hK₀K) (D.transcendental_residue_a htr) P
    obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hP0 (Polynomial.ext h)
    have hle := Finset.le_sup (f := fun i ↦ D.valuationSubring.valuation (P.coeff i : D.Ω))
      (Polynomial.mem_support_iff.2 hi)
    have hpos : 0 < D.valuationSubring.valuation (P.coeff i : D.Ω) :=
      (Valuation.pos_iff _).2 (by exact_mod_cast hi)
    have h0 : Polynomial.aeval (D.a x₀) P = 0 := by rw [← heval, hc]
    have : (Polynomial.aeval ((algebraMap D.R D.valuationSubring x₀ : D.valuationSubring) :
        D.Ω) P) = 0 := h0
    rw [this, map_zero] at hv
    exact (hpos.trans_le (hle.trans hv.symm.le)).ne rfl
  let ψ : MvPolynomial (ULift.{u} (Fin 1)) R →+* F₁ := (D.a.comp g).codRestrict F₁ hmem
  have hψ : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun c hc ↦
    hinj c (congrArg Subtype.val hc)
  obtain ⟨f, hf0, hfr⟩ := hr
  refine ⟨f.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hf0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval_map] at *
  have : (algebraMap F₁ D.Ω).comp ψ = D.a.comp g := rfl
  rw [this, ← Polynomial.hom_eval₂, hfr, map_zero]

/-- **Separability of residues.** If the residue field of `R'` is separable over `κ(x̄)`, then a
sum of products of residues of elements of `R'` and of integral elements of `Ω` is separable over
`k(x̄)`, `k` the residue field of `Ω`. -/
lemma isSeparable_residue_of_eq_sum [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] {x : D.R}
    (hsep : ∀ y : ResidueField D.R, IsSeparable (ResidueField R)⟮residue D.R x⟯ y)
    {z : D.valuationSubring} {n : ℕ} (c : Fin n → D.R) (e : Fin n → D.valuationSubring)
    (he : ∀ j, (e j : D.Ω) ∈ D.ωS.fieldRange)
    (hz : residue _ z = ∑ j, residue _ (algebraMap D.R _ (c j)) * residue _ (e j)) :
    IsSeparable (adjoin (D.valuationSubring.residueSubfield D.ωS.fieldRange)
      {residue D.valuationSubring (algebraMap D.R D.valuationSubring x)}) (residue _ z) := by
  set ℓ := ResidueField D.valuationSubring
  set k := D.valuationSubring.residueSubfield D.ωS.fieldRange
  set M := adjoin k {residue D.valuationSubring (algebraMap D.R D.valuationSubring x)}
  set f := algebraMap (ResidueField D.R) ℓ
  have hkM {y : ℓ} (hy : y ∈ k) : y ∈ M := IntermediateField.algebraMap_mem M (⟨y, hy⟩ : k)
  -- the residues of `R` lie in `k`
  have hRk (r : ResidueField R) : algebraMap (ResidueField R) ℓ r ∈ k := by
    obtain ⟨r, rfl⟩ := residue_surjective r
    refine ⟨algebraMap R D.valuationSubring r, ⟨algebraMap R Ω r, ?_⟩, rfl⟩
    exact (RingHom.congr_fun D.ωS_comp r)
  let C' : IntermediateField (ResidueField R) (ResidueField D.R) :=
    (M.toSubfield.comap f).toIntermediateField fun r ↦ by
      change f (algebraMap (ResidueField R) (ResidueField D.R) r) ∈ M
      rw [← IsScalarTower.algebraMap_apply]
      exact hkM (hRk r)
  have hC : (ResidueField R)⟮residue D.R x⟯ ≤ C' := by
    rw [adjoin_simple_le_iff]
    exact mem_adjoin_simple_self k _
  let h : (ResidueField R)⟮residue D.R x⟯ →+* M :=
    (f.comp (IntermediateField.val _).toRingHom).codRestrict M fun y ↦ hC y.2
  rw [← mem_separableClosure_iff, hz]
  refine sum_mem fun j _ ↦ mul_mem ?_ ?_
  · rw [mem_separableClosure_iff, ← ResidueField.algebraMap_residue]
    exact IsSeparable.of_ringHom_comp f h rfl (hsep _)
  · rw [mem_separableClosure_iff]
    obtain ⟨ω, hω⟩ := he j
    have hk : residue D.valuationSubring (e j) ∈ k := ⟨e j, ⟨ω, hω⟩, rfl⟩
    exact isSeparable_algebraMap (F := M) (K := ℓ) ⟨_, hkM hk⟩

end General

end AlgebraicGeometry.SliceTrait
