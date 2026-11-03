/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Polynomial.Lifts
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! # Real Weil sheaves and their local spectra

Source: latest blueprint, part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-top-cohomology-and-positive-euler-products/sk-def-wrp-real-definition/_section.md,
complete Real sheaves statement (blueprint: sk-def-wrp-real-definition).

The reality predicate and local factors are the existing ones on actual modules over
pulled-back condensed coefficients. Eigenvalues below are characteristic-polynomial roots,
with algebraic multiplicities. The scalar universe lift is removed before applying iota.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeCondensedWeil

open NativeCondensedModule

private theorem algClosed_of_equiv
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine ⟨fun p ↦ ?_⟩
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    ext j
    simp
  rwa [he] at h

private theorem lift_embedding_apply {K : Type*} [Field K] (φ : K →+* ℂ)
    (a : ULift.{u} K) : (φ.comp ULift.ringEquiv.toRingHom) a = φ a.down := rfl

private theorem reverse_real_coeff {K : Type*} [Field K]
    (p : Polynomial K) (φ : K →+* ℂ) :
    (∀ j, (φ (p.reverse.coeff j)).im = 0) ↔
      ∀ j, (φ (p.coeff j)).im = 0 := by
  simp only [Polynomial.coeff_reverse]
  constructor
  · intro h j
    simpa only [Polynomial.revAt_invol] using h (Polynomial.revAt p.natDegree j)
  · intro h j
    exact h _

private theorem monic_real_iff_roots {K : Type*} [Field K] [IsAlgClosed K]
    (p : Polynomial K) (hp : p.Monic) (φ : K →+* ℂ) :
    (∀ j, (φ (p.coeff j)).im = 0) ↔
      (p.roots.map φ).map (starRingEnd ℂ) = p.roots.map φ := by
  let q := p.map φ
  have hq : q.Monic := hp.map φ
  have hsplit : q.Splits := (IsAlgClosed.splits p).map φ
  have hr : q.roots = p.roots.map φ := (IsAlgClosed.splits p).roots_map φ
  have hc : (q.map (starRingEnd ℂ)).roots = q.roots.map (starRingEnd ℂ) :=
    hsplit.roots_map (starRingEnd ℂ)
  have he : (∀ j, (φ (p.coeff j)).im = 0) ↔ q.map (starRingEnd ℂ) = q := by
    constructor
    · intro h
      ext j
      simpa only [q, Polynomial.coeff_map] using Complex.conj_eq_iff_im.mpr (h j)
    · intro h j
      apply Complex.conj_eq_iff_im.mp
      simpa only [q, Polynomial.coeff_map] using
        congrArg (fun r : Polynomial ℂ ↦ r.coeff j) h
  rw [he, ← hr, ← hc]
  constructor
  · exact congrArg Polynomial.roots
  · intro h
    rw [(hsplit.map (starRingEnd ℂ)).eq_prod_roots_of_monic
      (hq.map (starRingEnd ℂ)), h,
      ← hsplit.eq_prod_roots_of_monic hq]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [hsep : IsSeparated X₀.hom]
  (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom)
  (iota : PadicAlgCl l →+* ℂ)

include hsep

-- The published signature retains the geometric hypotheses; this step is pure algebra.
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- Reality is equivalent to conjugation stability of every complex local eigenvalue
multiset, retaining algebraic multiplicity. No purity, lissity or semisimplicity is assumed.
Source: latest blueprint, Real sheaves, equivalently clause
(blueprint: sk-def-wrp-real-definition).
Proof: fix a closed point and a finite basis of its constructible scalar stalk. The
canonical local return is invertible. Over Qbar_l its characteristic polynomial splits
with nonzero roots, counted with root multiplicity. Reverse its factorization to get
P_x = product (1-alpha*T). Embedding the coefficients and conjugating replaces alpha by
conjugate(iota(alpha)). Real coefficients are exactly coefficients fixed by conjugation.
Uniqueness of the multiset of nonzero reciprocal roots gives conjugation stability in
one direction; multiplying the conjugate-stable factors gives the other direction.
This includes the zero-dimensional stalk, whose root multiset is empty. -/
theorem real_iff_conjugate_local_spectra (hl : l ≠ D.p)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier) :
    Real D l X₀ M iota ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (n : ℕ)
        (b : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl l))
          (fibre l D M.carrier (localClosedPoint D X₀ x i hi))),
        let A := LinearMap.toMatrix b b
          (operator l D (D.geometricFrobenius X₀).hom M.carrier M.str
            (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
            (localClosedPoint_return D X₀ x i hi)).hom
        let S := A.charpoly.roots.map (iota.comp ULift.ringEquiv.toRingHom)
        S.map (starRingEnd ℂ) = S := by
  have : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    algClosed_of_equiv ULift.ringEquiv.symm
  constructor
  · intro h x i hi n b
    apply (monic_real_iff_roots _ (Matrix.charpoly_monic _) _).mp
    apply (reverse_real_coeff _ _).mp
    simpa only [localFactorInBasis, lift_embedding_apply] using h x i hi n b
  · intro h x i hi n b
    have hr := (monic_real_iff_roots _ (Matrix.charpoly_monic _)
      (iota.comp ULift.ringEquiv.toRingHom)).mpr (h x i hi n b)
    have hr' := (reverse_real_coeff _ _).mpr hr
    simpa only [localFactorInBasis, lift_embedding_apply] using hr'

end WeilConjectures.NativeCondensedWeil
