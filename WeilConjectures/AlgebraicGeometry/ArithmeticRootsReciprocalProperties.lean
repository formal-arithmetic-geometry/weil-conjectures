/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicNumberRealization
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.AlgebraicGeometry.WeilNumbers
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactWeilCohomology
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.Eval.Coeff
import WeilConjectures.ZetaWeil.WeightPurityRoots
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Algebra.Hom.Rat
import WeilConjectures.ZetaLinearAlgebra.WeilNumbers

/-! Reciprocal-root part of the arithmetic-roots proposition.

Source: Weil conjectures blueprint, `prop-arithmetic-roots`.
The proof combines reversal, transport through every algebraic-number realization, root
purity, and the characteristic polynomial of a scalar-extended Frobenius operator.
(blueprint: prop-arithmetic-roots-reciprocal-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The finite-field cardinality supplies the characteristic used in the root transport.
Source: the finite-field setting of `prop-arithmetic-roots`.
(blueprint: prop-arithmetic-roots-reciprocal-properties). -/
local instance arithmeticRootsReciprocalBaseCharP (D : FiniteFieldDatum.{u}) : CharP D.k₀ D.p :=
  letI := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))

/-- Coefficient primes distinct from `p` differ from the characteristic of the base.
Source: the coefficient-prime setting of `prop-arithmetic-roots`.
(blueprint: prop-arithmetic-roots-reciprocal-properties). -/
local instance arithmeticRootsReciprocalCoefficientChar (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) : Fact (ringChar D.k₀ ≠ C.l) :=
  ⟨fun h ↦ C.different (h.symm.trans (ringChar.eq D.k₀ D.p))⟩

private theorem integerRoot_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : Polynomial ℤ) {α : K}
    (hα : (P.map (Int.castRingHom K)).IsRoot α) :
    (P.map (Int.castRingHom L)).IsRoot (f α) := by
  have h := hα.map (f := f)
  simpa only [Polynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom K))
    (Int.castRingHom L)] using h

private theorem connectedSmooth_dimension {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] [ConnectedSpace Y] :
    ∃ n : ℕ, SmoothOfRelativeDimension n g := by
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsRegular.of_smooth g
  have := IsRegular.isIntegral Y
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, V, -, -, hy, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g y
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  have : SmoothOfRelativeDimension n (V.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    have : SmoothOfRelativeDimension (n + 0) (g.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  refine ⟨n, (smoothOfRelativeDimension_iff_topologicalKrullDim_eq g n).mpr ?_⟩
  exact (topologicalKrullDim_opens_eq g V).symm.trans
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ g) n)

private theorem arithmeticRoots_relativeDimension (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u}) [X₀.Over (Spec (.of D.k₀))]
    [IsProper (X₀ ↘ Spec (.of D.k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (.of D.k₀))]
    (d : ℕ) (hsmooth : D.IsSmoothOfPureDimension
      (Over.mk (X₀ ↘ Spec (.of D.k₀))) d) :
    SmoothOfRelativeDimension d (X₀ ↘ Spec (.of D.k₀)) := by
  let f := X₀ ↘ Spec (.of D.k₀)
  have : Smooth f := hsmooth.1
  have : ConnectedSpace X₀ := GeometricallyConnected.connectedSpace_of_subsingleton (f := f)
  obtain ⟨n, hn⟩ := connectedSmooth_dimension f
  have := hn
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let Y := CategoryTheory.Limits.pullback f g
  have : ConnectedSpace Y := inferInstance
  have : Smooth (CategoryTheory.Limits.pullback.snd f g) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (CategoryTheory.Limits.pullback.snd f g)
  have := IsRegular.of_smooth (CategoryTheory.Limits.pullback.snd f g)
  have := IsRegular.irreducibleSpace Y
  have hpure : Y.IsPureDimension d := hsmooth.2
  have hdim : topologicalKrullDim Y = (d : WithBot ℕ∞) := by
    have h := hpure Set.univ (by simp [irreducibleComponents_eq_singleton])
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ Y).isHomeomorph).symm.trans h
  have hnDim := topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (CategoryTheory.Limits.pullback.snd f g) n
  have hnd : n = d := by exact_mod_cast hnDim.symm.trans hdim
  exact hnd ▸ hn

/-- Reciprocal roots are integral Weil numbers and give the transported eigenvalues.
Source: blueprint `prop-arithmetic-roots`, reciprocal-root clauses.
Proof:
1. A connected smooth scheme over a field is regular and integral. A nonempty smooth chart
   fixes its relative dimension. Base change preserves that dimension; the connected smooth
   geometric fibre is irreducible, so its pure dimension identifies this dimension with `d`.
2. The normalized reverse polynomial is monic. Its roots are therefore integral, and the
   reverse-root identity makes them nonzero.
3. Choose a prime larger than `p` and an abstract complex isomorphism of its adic closure.
   Transport every complex root back to that closure and apply `reciprocalRoot_weight`.
   Every conjugate of a root is again a root of the same integer polynomial, so the proved
   source-library conjugate criterion gives the intrinsic Weil norm for every embedding.
4. Transport the reverse equation through `j` and then `e` inverse. The integral-factor
   identity gives the recorded reciprocal root. Map its inverse root equation through `e`.
5. The reciprocal-root identity gives a characteristic-polynomial root. Characteristic
   polynomials commute with base change, giving an eigenvalue of the displayed tensor-extended
   endomorphism. Ordinary cohomology is its specified Frobenius module by definition.
(blueprint: prop-arithmetic-roots-reciprocal-properties). -/
theorem arithmetic_roots_reciprocal_properties (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u}) [X₀.Over (Spec (.of D.k₀))]
    [IsProper (X₀ ↘ Spec (.of D.k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (.of D.k₀))]
    (d : ℕ) (hsmooth : @FiniteFieldDatum.IsSmoothOfPureDimension D
      (Over.mk (X₀ ↘ Spec (.of D.k₀)))
      (inferInstanceAs (LocallyOfFiniteType (X₀ ↘ Spec (.of D.k₀))))
      (inferInstanceAs (QuasiCompact (X₀ ↘ Spec (.of D.k₀)))) d)
    (i : ℤ) (hi₀ : 0 ≤ i) (hi : i ≤ 2 * (d : ℤ))
    (P : Polynomial ℤ) (hP₀ : P.coeff 0 = 1)
    (hP : Scheme.IsIntegralFrobeniusFactor D.k₀ X₀ i P)
    (Qbar : Type v) [Field Qbar] [Algebra ℚ Qbar] [IsAlgClosure ℚ Qbar] :
    ∀ α : Qbar, (P.reverse.map (Int.castRingHom Qbar)).IsRoot α →
      IsIntegral ℤ α ∧ IsWeilNumber D α (i : ℝ) ∧
        ∀ (C : D.CoefficientDatum)
          (e : PadicAlgCl C.l ≃ₐ[Padic C.l] C.Qbar)
          (j : C.AlgebraicNumberRealization D Qbar),
          ((AlgEquiv.toEquiv j) α : C.Qbar) ≠ 0 ∧
            ((Scheme.frobeniusCharpolyRev D.k₀ C.l X₀ i).map e.toRingHom).IsRoot
              ((AlgEquiv.toEquiv j) α : C.Qbar)⁻¹ ∧
            Module.End.HasEigenvalue
              (((ModuleCat.extendScalars e.toRingHom).map
                (ModuleCat.ofHom
                  (WeilSheaf.ordinaryCompactWeilSheafCohomology
                    (WeilSheaf.adicConstant D.k₀ C.l X₀) i).1.frobeniusEnd)).hom)
              ((AlgEquiv.toEquiv j) α : C.Qbar) := by
  classical
  have : CharZero Qbar := algebraRat.charZero Qbar
  have := arithmeticRoots_relativeDimension D X₀ d hsmooth
  have hPne : P ≠ 0 := by intro h; simp [h] at hP₀
  have hrevne : P.reverse ≠ 0 := Polynomial.reverse_eq_zero.not.2 hPne
  have hnorm : ∀ y ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      ‖y‖ = (D.q : ℝ) ^ ((i : ℝ) / 2) := by
    obtain ⟨l, hl, hlprime⟩ := Nat.exists_infinite_primes (D.p + 1)
    have : Fact l.Prime := ⟨hlprime⟩
    have hlp : l ≠ D.p := by omega
    have : Fact (ringChar D.k₀ ≠ l) := ⟨by
      rw [ringChar.eq D.k₀ D.p]
      exact Ne.symm hlp⟩
    obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringEquiv_complex l
    intro y hy
    have hroot := integerRoot_map ι.symm.toRingHom P.reverse
      (Polynomial.isRoot_of_mem_roots hy)
    have hEq := hP l
    have hmem : ι.symm y ∈ (Scheme.frobeniusCharpolyRev D.k₀ l X₀ i).reverse.roots := by
      rw [← hEq, Polynomial.reverse_map (RingHom.injective_int _)]
      exact (Polynomial.mem_roots
        ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hrevne)).2 hroot
    simpa using reciprocalRoot_weight D l hlp X₀ d ι i hi₀ hi (ι.symm y) hmem
  intro α hα
  have hαmem : α ∈ (P.reverse.map (Int.castRingHom Qbar)).roots :=
    (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hrevne)).2 hα
  have hαne : α ≠ 0 := by
    apply Polynomial.ne_zero_of_mem_roots_reverse
    rwa [Polynomial.reverse_map (RingHom.injective_int _)]
  have hint : IsIntegral ℤ α := by
    refine ⟨P.reverse, Polynomial.monic_reverse_of_coeff_zero_eq_one hP₀, ?_⟩
    rw [show algebraMap ℤ Qbar = Int.castRingHom Qbar from RingHom.ext_int _ _,
      ← Polynomial.eval_map]
    exact hα
  have hw := _root_.isWeilNumber_of_mem_roots hrevne hnorm hαmem
  refine ⟨hint, ⟨hαne, ?_⟩, ?_⟩
  · intro τ
    let : Algebra ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) :=
      IntermediateField.algebra' _
    exact hw.2 τ.toRatAlgHom
  intro C e j
  let jring : Qbar ≃+* algebraicClosure ℚ C.Qbar :=
    @AlgEquiv.toRingEquiv ℚ Qbar (algebraicClosure ℚ C.Qbar) _ _ _ _ _ j
  let jhom : Qbar →+* C.Qbar :=
    (algebraicClosure ℚ C.Qbar).toSubfield.subtype.comp jring.toRingHom
  have hjhom : jhom α = ((AlgEquiv.toEquiv j) α : C.Qbar) := rfl
  let x : PadicAlgCl C.l := e.symm (jhom α)
  have hxroot : (P.reverse.map (Int.castRingHom (PadicAlgCl C.l))).IsRoot x :=
    integerRoot_map (e.symm.toRingHom.comp jhom) P.reverse hα
  have hEq := hP C.l
  have hxmem : x ∈ (Scheme.frobeniusCharpolyRev D.k₀ C.l X₀ i).reverse.roots := by
    rw [← hEq, Polynomial.reverse_map (RingHom.injective_int _)]
    exact (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hrevne)).2 hxroot
  have hdetne : Scheme.frobeniusCharpolyRev D.k₀ C.l X₀ i ≠ 0 := by
    rw [← hEq]
    exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hPne
  have hxinv := ((Polynomial.mem_roots_reverse_iff hdetne).1 hxmem).2
  have hrealne : jhom α ≠ 0 := (map_ne_zero jhom).2 hαne
  refine ⟨hrealne, ?_, ?_⟩
  · have h := hxinv.map (f := e.toRingHom)
    have he : e.toRingHom (x⁻¹) = ((AlgEquiv.toEquiv j) α : C.Qbar)⁻¹ := by
      rw [map_inv₀]
      change (e (e.symm (jhom α)))⁻¹ = _
      rw [e.apply_symm_apply, hjhom]
    rw [he] at h
    exact h
  · let M := (WeilSheaf.adicConstant D.k₀ C.l X₀).cohomology i
    have hchar : M.frobeniusEnd.charpoly.IsRoot x := by
      apply Polynomial.isRoot_of_mem_roots
      rw [← (LinearMap.reciprocal_roots_eigenvalues M.frobeniusEnd
        (LinearEquiv.isUnit_det' M.frobenius)).1]
      exact hxmem
    let : Algebra (PadicAlgCl C.l) C.Qbar := e.toRingHom.toAlgebra
    change Module.End.HasEigenvalue (M.frobeniusEnd.baseChange C.Qbar) (jhom α)
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2
    rw [LinearMap.charpoly_baseChange]
    change (M.frobeniusEnd.charpoly.map e.toRingHom).IsRoot (jhom α)
    have h := hchar.map (f := e.toRingHom)
    have he : e.toRingHom x = jhom α := e.apply_symm_apply _
    rw [he] at h
    exact h

end WeilConjectures
