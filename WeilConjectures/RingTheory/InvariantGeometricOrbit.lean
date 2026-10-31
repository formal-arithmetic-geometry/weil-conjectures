/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Geometric-point orbits of a finite-group invariant ring
Source: Stacks Project, More on Algebra, Tag 0BRJ.
(blueprint: lem-dl-a1-invariant-geometric-orbit). -/

@[expose] public section
set_option autoImplicit false
universe u v

/-- The geometric points of a finite-group invariant ring over one base point form one G-orbit.
Source: Stacks Project, More on Algebra, Tag 0BRJ.
(blueprint: lem-dl-a1-invariant-geometric-orbit).

Proof: pass to the polynomial rings C[variables indexed by Ω] and R[variables indexed
by Ω], letting G act on coefficients. The invariant property holds coefficient by
coefficient. Extend the two points by evaluating each variable at its index in Ω. Their
prime kernels contract to the same ideal in the polynomial base ring. The prime-orbit
theorem gives g carrying the first kernel to the second. For each x in R the polynomial
C(x) - X(s(x)) lies in the first kernel. Its g-translate lies in the second kernel, so
 t(g(x)) - s(x) = 0. This proves equality of the points after translation. The argument
needs neither finiteness of R over C nor algebraic closedness of Ω. -/
theorem RingHom.PointsOver.exists_smul_of_isInvariant
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    (G : Type v) [Group G] [_root_.Finite G] [MulSemiringAction G R]
    [SMulCommClass G C R] [Algebra.IsInvariant C R G]
    (Ω : Type u) [Field Ω] (φ : C →+* Ω)
    (s t : RingHom.PointsOver φ R) :
    ∃ g : G, ∀ x : R, s x = t (g • x) := by
  classical
  let CP := MvPolynomial Ω C
  let RP := MvPolynomial Ω R
  let : Algebra CP RP := MvPolynomial.algebraMvPolynomial
  let : MulSemiringAction G RP :=
    { smul g p := MvPolynomial.map (MulSemiringAction.toRingHom G R g) p
      one_smul p := by
        apply MvPolynomial.ext
        intro d
        change (1 : G) • MvPolynomial.coeff d p = MvPolynomial.coeff d p
        exact one_smul G _
      mul_smul g h p := by
        apply MvPolynomial.ext
        intro d
        change (g * h) • MvPolynomial.coeff d p = g • h • MvPolynomial.coeff d p
        exact mul_smul g h _
      smul_zero g := map_zero _
      smul_add g := map_add _
      smul_one g := map_one _
      smul_mul g := map_mul _ }
  have hfix (g : G) (p : CP) :
      g • (algebraMap CP RP p) = algebraMap CP RP p := by
    apply MvPolynomial.ext
    intro d
    change g • (MvPolynomial.coeff d (MvPolynomial.map (algebraMap C R) p)) =
      MvPolynomial.coeff d (MvPolynomial.map (algebraMap C R) p)
    simp only [MvPolynomial.coeff_map, smul_algebraMap]
  have : SMulCommClass G CP RP := ⟨by
    intro g c p
    change g • (algebraMap CP RP c * p) = algebraMap CP RP c * (g • p)
    rw [smul_mul', hfix]⟩
  have : Algebra.IsInvariant CP RP G := ⟨by
    intro p hp
    change p ∈ Set.range (MvPolynomial.map (algebraMap C R))
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    obtain ⟨d, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hx
    apply Algebra.IsInvariant.isInvariant (A := C) (G := G)
    intro g
    have hh := congrArg (MvPolynomial.coeff d) (hp g)
    change g • MvPolynomial.coeff d p = MvPolynomial.coeff d p at hh
    exact hh⟩
  let S : RP →+* Ω := MvPolynomial.eval₂Hom s.1 (fun z : Ω ↦ z)
  let T : RP →+* Ω := MvPolynomial.eval₂Hom t.1 (fun z : Ω ↦ z)
  have hcomp : S.comp (algebraMap CP RP) = T.comp (algebraMap CP RP) := by
    change S.comp (MvPolynomial.map (algebraMap C R)) =
      T.comp (MvPolynomial.map (algebraMap C R))
    ext c
    · change MvPolynomial.eval₂Hom s.1 (fun z : Ω ↦ z)
          (MvPolynomial.map (algebraMap C R) (MvPolynomial.C c)) =
        MvPolynomial.eval₂Hom t.1 (fun z : Ω ↦ z)
          (MvPolynomial.map (algebraMap C R) (MvPolynomial.C c))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact (s.apply_algebraMap c).trans (t.apply_algebraMap c).symm
    · change MvPolynomial.eval₂Hom s.1 (fun z : Ω ↦ z)
          (MvPolynomial.map (algebraMap C R) (MvPolynomial.X c)) =
        MvPolynomial.eval₂Hom t.1 (fun z : Ω ↦ z)
          (MvPolynomial.map (algebraMap C R) (MvPolynomial.X c))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have hker : (RingHom.ker S).under CP = (RingHom.ker T).under CP := by
    ext p
    change S (algebraMap CP RP p) = 0 ↔ T (algebraMap CP RP p) = 0
    rw [show S (algebraMap CP RP p) = T (algebraMap CP RP p) from
      RingHom.congr_fun hcomp p]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq CP RP G
    (RingHom.ker S) (RingHom.ker T) hker
  refine ⟨g, fun x ↦ ?_⟩
  let p : RP := MvPolynomial.C x - MvPolynomial.X (s x)
  have hp : p ∈ RingHom.ker S := by
    change MvPolynomial.eval₂Hom s.1 (fun z : Ω ↦ z)
      (MvPolynomial.C x - MvPolynomial.X (s x)) = 0
    rw [map_sub, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', sub_self]
  have hgp : g • p ∈ RingHom.ker T := hg ▸ Ideal.smul_mem_pointwise_smul g _ _ hp
  change T (MvPolynomial.map (MulSemiringAction.toRingHom G R g) p) = 0 at hgp
  have : t (g • x) - s x = 0 := by
    change MvPolynomial.eval₂Hom t.1 (fun z : Ω ↦ z)
      (MvPolynomial.map (MulSemiringAction.toRingHom G R g)
        (MvPolynomial.C x - MvPolynomial.X (s x))) = 0 at hgp
    rw [map_sub, MvPolynomial.map_C, MvPolynomial.map_X, map_sub,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at hgp
    exact hgp
  exact (sub_eq_zero.mp this).symm
