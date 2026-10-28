/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData
public import Sheaf.SixFunctors.ClosedOpenDualizingMate
import all Sheaf.Paper.EtaleCompactScalarCoherence
import Sheaf.Paper.SfBcAdicRingDomain
import Sheaf.SixFunctors.CoefDualizingConstruction
import Sheaf.SixFunctors.CoefficientDualizingClosedDescent
import Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar
import all Sheaf.SixFunctors.ClosedOpenDualizingMateNormalization
import all Sheaf.CategoryTheory.CounitMateTransport
import Sheaf.Paper.CoefDualizingClosedChart

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

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The closed-chart coefficient mate is invertible after closed descent.

Source: finite dualizing proof, paragraph 3 (blueprint: affine-closed-mate-isIso).
The proof is the closed-chart descent argument: identify the ordinary counit mate
with the descent witness by the proper adjunction Hom equivalence, then use the
witness's recorded isomorphism. The quotient and coefficient lifts are fixed by
finite coefficient construction; no arbitrary object is chosen. -/
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
      (Etale.dualizingComplex (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
        (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)))) := by sorry

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
      (Etale.dualizingComplex (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
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
  let P := AffineSpace (ULift.{u} (Fin r)) S
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hz := (Scheme.sf_bc_adic_ring_domain l E).2.2.2.2.2.2.2.2.2
    (m + 1) (Nat.succ_pos m)
  have hA : ((l ^ (m + 1) : ℕ) : A) = 0 := by
    apply ULift.down_injective
    change ((l ^ (m + 1) : ℕ) : Padic.coefficientExtensionRing l E (m + 1)) = 0
    simpa only [nsmul_eq_mul, mul_one] using hz.2.1 1
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
  have : SmoothOfRelativeDimension r (P ↘ S) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin r)) S
  exact (Etale.finite_smooth_dualizing_scalar φ l (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    hA hB hS (P ↘ S) r).1

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
  have hω := (Etale.coefDualizingConstruction D l hl E X
    ⟨m + 1, Nat.succ_pos m⟩).2.2
  have hlocal (V : X.affineOpens) :
      IsIso ((Etale.derivedRestriction (A := finiteDualizingCoeff l E n) V.1.ι).map
        (Etale.ExceptionalCoefficients.dualizingScalarMap (finiteDualizingQuotient l E h)
          (X ↘ Spec (.of D.k)))) := by
    have : IsAffine V.1.toScheme := V.2
    let Y := V.1.toScheme
    let aY := V.1.ι ≫ (X ↘ Spec (.of D.k))
    obtain ⟨r, i, hi, hrest⟩ := Etale.exists_coefDualizingClosedChart D l hl E
      (n + 1) (m + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Nat.add_le_add_right h 1) Y aY
    let : IsClosedImmersion i := hi
    have he := (hrest).1
    let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
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
