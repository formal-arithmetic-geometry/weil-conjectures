/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Determinant

/-!
# Prescribed étale coordinates after principal localization

Source: Stacks Project, algebra.tex, Tag 00T7(2), and morphisms.tex, Tag 02GU(8).
The determinant of the coordinate differentials in a global differential basis is
nonzero in the specified field fibre. Inverting it makes the prescribed map étale.
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace MvPolynomial

private theorem baseChange_toMatrix
    {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (b : Module.Basis ι A M) (v : ι → M)
    (S : Type*) [CommRing S] [Algebra A S] :
    (b.baseChange S).toMatrix (fun i => 1 ⊗ₜ[A] v i) =
      (b.toMatrix v).map (algebraMap A S) := by
  classical
  ext i j
  simp [Module.Basis.toMatrix_apply, Algebra.smul_def]

/-- A fibre basis of prescribed differentials becomes an étale coordinate map on a
principal localization of a smooth algebra with free differentials.
Source: Stacks Project, algebra.tex, Tag 00T7(2), and morphisms.tex, Tag 02GU(8).
(blueprint: lem-pur-etale-coordinates-of-fibre-basis).

Proof: express the prescribed differentials in the given global basis and let `f`
be the determinant of that coefficient matrix. After base change to `K`, this is
the change-of-basis matrix between two bases, so its determinant is nonzero.
In `A[1/f]`, its determinant is a unit, so the prescribed vectors form a basis.
The canonical localization equivalence for Kähler differentials sends these
vectors to the differentials of the localized functions. Smoothness persists under
localization. Apply the proved polynomial-evaluation criterion for a basis of
Kähler differentials. Empty matrices have determinant one, so the same proof
covers an empty coordinate family. -/
theorem exists_etale_aeval_localization_of_fibre_basis
    {R A K ι : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] [Algebra.Smooth R A] [Finite ι]
    (h : ι → A) (b : Module.Basis ι A (KaehlerDifferential R A))
    (c : Module.Basis ι K (K ⊗[A] KaehlerDifferential R A))
    (hc : ∀ i, c i = 1 ⊗ₜ[A] KaehlerDifferential.D R A (h i)) :
    ∃ f : A, algebraMap A K f ≠ 0 ∧
      (aeval (fun i => algebraMap A (Localization.Away f) (h i)) :
        MvPolynomial ι R →ₐ[R] Localization.Away f).toRingHom.Etale := by
  classical
  let := Fintype.ofFinite ι
  let v : ι → KaehlerDifferential R A := fun i => KaehlerDifferential.D R A (h i)
  let f : A := (b.toMatrix v).det
  have hf : algebraMap A K f ≠ 0 := by
    have heq : (fun i => 1 ⊗ₜ[A] v i) = c := funext fun i => (hc i).symm
    have hu := (b.baseChange K).isUnit_det c
    rw [Module.Basis.det_apply, ← heq, baseChange_toMatrix b v K,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hu
    exact hu.ne_zero
  let S := Localization.Away f
  have hu : IsUnit ((b.baseChange S).det (fun i => 1 ⊗ₜ[A] v i)) := by
    rw [Module.Basis.det_apply, baseChange_toMatrix b v S,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact IsLocalization.Away.algebraMap_isUnit f
  obtain ⟨hind, hspan⟩ := (b.baseChange S).is_basis_iff_det.mpr hu
  let bs : Module.Basis ι S (S ⊗[A] KaehlerDifferential R A) :=
    Module.Basis.mk hind hspan.ge
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S
  let bs' := bs.map e
  have hb : ∀ i, bs' i = KaehlerDifferential.D R S (algebraMap A S (h i)) := by
    intro i
    simp [bs', bs, e, v, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D]
  exact ⟨f, hf, etale_aeval_of_basis_kaehlerDifferential _ bs' hb⟩

end MvPolynomial
