/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Punctured local coefficient-field cohomological dimension

Source: blueprint thm-sc-affine-torsion-cd, rational-function-field local calculation.
(blueprint: lem-sc-punctured-coefficient-field-cohomological-dimension)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
open CommRingCat

private theorem old_to_new {X : Scheme.{u}} {c : ℕ}
    (h : X.HasTorsionCohomologicalDimensionLE c) :
    X.HasTorsionEtaleCohomologicalDimensionLE c := by
  intro F hF q hq
  have : Subsingleton ((Sheaf.functorH X.smallEtaleTopology q).obj F) := h F hF q hq
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton
private theorem new_to_old {X : Scheme.{u}} {c : ℕ}
    (h : X.HasTorsionEtaleCohomologicalDimensionLE c) :
    X.HasTorsionCohomologicalDimensionLE c := by
  intro F hF q hq
  have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} X q).obj F) := h F hF q hq
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  exact (e.app F).addCommGroupIsoToAddEquiv.injective.subsingleton

private theorem domain_cd (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (L A : Type u) [Field L] [CommRing A] [IsDomain A] [Algebra L A]
    (m c : ℕ) (hm : m < n + 2)
    (hL : (Spec (.of L)).HasTorsionCohomologicalDimensionLE c)
    (htr : Algebra.trdeg L A ≤ (m : Cardinal.{u})) :
    (Spec (.of A)).HasTorsionCohomologicalDimensionLE (m + c) := by
  classical
  let I := {B : Subalgebra L A // B.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder I := ⟨fun B C ↦ ⟨⟨B.1 ⊔ C.1, B.2.sup C.2⟩,
    show B.1 ≤ B.1 ⊔ C.1 from le_sup_left,
    show C.1 ≤ B.1 ⊔ C.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (fgSubalgebraDiagramOf L A).op ⋙ Scheme.Spec
  let s : Cone D := Scheme.Spec.mapCone (fgSubalgebraCoconeOf L A).op
  have hs : IsLimit s := isLimitOfPreserves Scheme.Spec (isColimitFGSubalgebraCocone L A).op
  have (i : Iᵒᵖ) : IsAffine (D.obj i) := inferInstanceAs (IsAffine (Spec _))
  have (i : Iᵒᵖ) : CompactSpace (D.obj i) := inferInstance
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := inferInstance
  have {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  apply new_to_old
  apply hasTorsionEtaleCohomologicalDimensionLE_of_isLimit D s hs (m + c)
  intro i
  let B := i.unop.1
  have : Algebra.FiniteType L B := (Subalgebra.fg_iff_finiteType B).mp i.unop.2
  let b : Spec (.of B) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L B))
  have : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  obtain ⟨k, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg L B
  have hd : ringKrullDim B = (k : WithBot ℕ∞) :=
    ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin
  have ht : Algebra.trdeg L B = (k : Cardinal.{u}) :=
    Algebra.trdeg_eq_of_ringKrullDim_eq L B hd
  have hk : k ≤ m := by
    have hle := (trdeg_le_of_injective B.val Subtype.val_injective).trans htr
    rw [ht] at hle
    exact_mod_cast hle
  apply old_to_new
  apply hIH L m c hm hL (Spec (.of B)) b
  change topologicalKrullDim (PrimeSpectrum B) ≤ (m : WithBot ℕ∞)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hd]
  exact_mod_cast hk


private theorem polynomial_eval_unit_localization
    (F R : Type u) [Field F] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra F R]
    (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R)
    (P : Polynomial F) (hP : P ≠ 0) :
    IsUnit (algebraMap R (Localization.Away h) (Polynomial.aeval h P)) := by
  classical
  induction hdP : P.natDegree using Nat.strong_induction_on generalizing P with
  | h deg ih =>
    by_cases hc : P.coeff 0 = 0
    · obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.mpr hc
      have hQ0 : Q ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hQ
        exact hP hQ
      have hdeg : Q.natDegree < deg := by
        rw [hQ, Polynomial.natDegree_X_mul hQ0] at hdP
        omega
      have hu := ih Q.natDegree hdeg Q hQ0 rfl
      rw [hQ, map_mul, Polynomial.aeval_X, map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit h).mul hu
    · have hr : IsLocalRing.residue R (Polynomial.aeval h P) ≠ 0 := by
        have heval : IsLocalRing.residue R (Polynomial.aeval h P) =
            ((IsLocalRing.residue R).comp (algebraMap F R)) (P.coeff 0) := by
          rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
            (IsLocalRing.residue_eq_zero_iff h).mpr hh, Polynomial.eval₂_at_zero]
        rw [heval]
        exact (map_ne_zero _).mpr hc
      exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hr).map _

/-- The induction bound for a principal puncture of a local domain with a coefficient field.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, "Local calculation in dimension d".
(blueprint: lem-sc-punctured-coefficient-field-cohomological-dimension)

Proof: The residue-bijective coefficient field identifies the residue of R with F. For a
nonzero P in F[T], factor out its lowest power T^r; the remaining Q has nonzero constant
term. Reducing Q(h) modulo the maximal ideal, using h in that ideal, gives this nonzero
constant; Q(h) is therefore a unit. Thus P(h) is a unit after h is inverted. Evaluation
constructs an embedding F(T) into R[1/h]. Both R[1/h] and F(T) embed compatibly in Frac R.
The transcendence-degree tower formula gives trdeg over F(T) at most e-1. Express R[1/h]
as the filtered union of its finitely generated F(T)-subalgebras. Each is a domain, and its
Krull dimension equals its finite transcendence degree by Noether normalization, hence is
at most e-1<n+2. The rational-function field over separably closed F has torsion
cohomological dimension at most one. Apply hIH with m=e-1 and c=1 to each finite-type
spectrum; the affine-limit cohomology theorem transfers the uniform bound e to the inverse
limit Spec R[1/h]. The use of finite subalgebras, not all subrings, keeps the scalar maps
compatible. The case e=1 uses m=0; h not zero ensures that the localized ring is nonzero. -/
theorem hasTorsionCohomologicalDimensionLE_punctured_of_coefficientField
    (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (F R : Type u) [Field F] [IsSepClosed F] [CommRing R] [IsDomain R]
    [IsLocalRing R] [Algebra F R]
    (_hres : Function.Bijective
      ((IsLocalRing.residue R).comp (algebraMap F R)))
    (e : ℕ) (he : 0 < e) (hed : e ≤ n + 2)
    (htr : letI : Algebra F (FractionRing R) :=
      ((algebraMap R (FractionRing R)).comp (algebraMap F R)).toAlgebra
      Algebra.trdeg F (FractionRing R) = (e : Cardinal.{u}))
    (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R) (hh0 : h ≠ 0) :
    (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE e := by
  classical
  let A := Localization.Away h
  let : IsDomain A := Localization.Away.isDomain hh0
  let Q := FractionRing R
  have : Algebra.trdeg F Q = (e : Cardinal.{u}) := htr
  let E : Polynomial F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F R A).comp (Polynomial.aeval h)
  have hE : ∀ p : nonZeroDivisors (Polynomial F), IsUnit (E p) := by
    intro p
    exact polynomial_eval_unit_localization F R h hh p
      (nonZeroDivisors.ne_zero p.property)
  let φ : RatFunc F →ₐ[F] A := IsLocalization.liftAlgHom hE
  let L := RatFunc F
  let : Algebra L A := φ.toRingHom.toAlgebra
  have : IsScalarTower F L A :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (φ.commutes x).symm)
  have hQunit (p : Submonoid.powers h) : IsUnit (algebraMap R Q p) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply nonZeroDivisors.ne_zero
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh0 p.property)
    exact IsFractionRing.injective R Q (by simpa only [map_zero] using hz)
  let α : A →ₐ[F] Q := IsLocalization.liftAlgHom
    (M := Submonoid.powers h) (S := A)
    (f := IsScalarTower.toAlgHom F R Q) hQunit
  have hα : Function.Injective α := by
    apply (IsLocalization.lift_injective_iff _).mpr
    intro x y
    change algebraMap R A x = algebraMap R A y ↔ algebraMap R Q x = algebraMap R Q y
    rw [(IsLocalization.injective A
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh0)).eq_iff,
      (IsFractionRing.injective R Q).eq_iff]
  have htrA : Algebra.trdeg F A ≤ (e : Cardinal.{u}) :=
    (trdeg_le_of_injective α hα).trans (le_of_eq htr)
  have hFL : (1 : Cardinal.{u}) ≤ Algebra.trdeg F L := by
    have ht := trdeg_le_of_injective
      (IsScalarTower.toAlgHom F (Polynomial F) L) (IsFractionRing.injective (Polynomial F) L)
    simpa only [Polynomial.trdeg_of_isDomain] using ht
  have htower : (1 : Cardinal.{u}) + Algebra.trdeg L A ≤ (e : Cardinal.{u}) :=
    (add_le_add hFL (le_refl (Algebra.trdeg L A))).trans
      ((trdeg_add_le (R := F) (S := L) (A := A)).trans htrA)
  have hfinite : Algebra.trdeg L A < Cardinal.aleph0 :=
    (le_add_self.trans htower).trans_lt (Cardinal.natCast_lt_aleph0 (n := e))
  have hcast := Cardinal.cast_toNat_of_lt_aleph0 hfinite
  have hm : Algebra.trdeg L A ≤ ((e - 1 : ℕ) : Cardinal.{u}) := by
    rw [← hcast] at htower ⊢
    have hnat : 1 + (Algebra.trdeg L A).toNat ≤ e := by
      exact_mod_cast htower
    exact_mod_cast (show (Algebra.trdeg L A).toNat ≤ e - 1 by omega)
  have hL := hasTorsionCohomologicalDimensionLE_one_ratFunc F
  have hcd := domain_cd n hIH L A (e - 1) 1 (by omega) hL hm
  simpa only [Nat.sub_add_cancel he] using hcd

end AlgebraicGeometry.Scheme
