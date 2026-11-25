/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import WeilConjectures.FieldTheory.BrauerScalarDefect
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
import WeilConjectures.Algebra.Central.ReducedNorm
import WeilConjectures.FieldTheory.BrauerScalarDefectExists
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithful
import WeilConjectures.FieldTheory.BrauerScalarDefectSurjective

/-!
# Algebraic Brauer classes and continuous Galois cohomology

Central simple algebras over a field `K` up to Brauer equivalence are classified by the second
continuous Galois cohomology of `K` with coefficients in the units of the separable closure,
via the scalar-defect class of matrix lifts of a Galois descent datum.

## Implementation details

A central simple algebra splits over a finite Galois extension. Its descent datum is a
projective-linear cocycle; lifts to general linear matrices have scalar defects, giving a
continuous two-cocycle in the units of the separable closure. Changing the lifts changes this by
a continuous coboundary; tensor products multiply the cocycles and matrix amplification preserves
their class, so the construction descends to Brauer equivalence. Injectivity uses matrix
Hilbert 90 on the tensor product with an opposite algebra; surjectivity uses a crossed-product
algebra over a finite Galois extension through which a given continuous cocycle factors.
All fields, including imperfect fields, use separable-closure units, not algebraic-closure units.

## References

* Stacks Project, Theorem 03R7 (Brauer groups) and Section 0DVG (continuous homogeneous and
  inhomogeneous cochains).
-/

@[expose] public section

universe u

namespace Field

variable (K : Type u) [Field K]

theorem existsUnique_hasBrauerScalarDefect (A : CSA.{u, u} K) :
    ∃! x : GaloisUnitsH2 K, HasBrauerScalarDefect K A x := by
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    Algebra.IsCentral.exists_algEquiv_matrix_of_isSepClosed K A (SeparableClosure K)
  obtain ⟨b, hb, z, hdesc, hdefect⟩ :=
    exists_brauerScalarDefect_lifts K A n hn.ne e
  have hx : HasBrauerScalarDefect K A ((ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z) :=
    ⟨n, hn.ne, e, b, hb, z, rfl, hdesc, hdefect⟩
  exact ⟨_, hx, fun y hy ↦
    (brauerScalarDefect_eq_iff K A A _ _ hy hx).mpr (IsBrauerEquivalent.refl A)⟩

/-- The scalar-defect class of a central simple algebra `A`: the unique class in
`GaloisUnitsH2 K` realized by matrix lifts of a Galois descent datum of `A`. -/
noncomputable def brauerScalarDefectClass (A : CSA.{u, u} K) : GaloisUnitsH2 K :=
  (existsUnique_hasBrauerScalarDefect K A).choose

theorem hasBrauerScalarDefect_brauerScalarDefectClass (A : CSA.{u, u} K) :
    HasBrauerScalarDefect K A (brauerScalarDefectClass K A) :=
  (existsUnique_hasBrauerScalarDefect K A).choose_spec.1

theorem eq_brauerScalarDefectClass_iff (A : CSA.{u, u} K) (x : GaloisUnitsH2 K) :
    x = brauerScalarDefectClass K A ↔ HasBrauerScalarDefect K A x :=
  ⟨fun h ↦ h ▸ hasBrauerScalarDefect_brauerScalarDefectClass K A,
    fun h ↦ (existsUnique_hasBrauerScalarDefect K A).unique h
      (hasBrauerScalarDefect_brauerScalarDefectClass K A)⟩

theorem brauerScalarDefectClass_eq_iff (A B : CSA.{u, u} K) :
    brauerScalarDefectClass K A = brauerScalarDefectClass K B ↔ IsBrauerEquivalent A B :=
  brauerScalarDefect_eq_iff K A B _ _ (hasBrauerScalarDefect_brauerScalarDefectClass K A)
    (hasBrauerScalarDefect_brauerScalarDefectClass K B)

/-- Central simple algebras up to Brauer equivalence are classified by second continuous
Galois cohomology with coefficients in separable-closure units: the Brauer group of `K` is in
bijection with `GaloisUnitsH2 K`, sending a class to its scalar-defect class. -/
noncomputable def brauerGroupEquivGaloisUnitsH2 : BrauerGroup.{u, u} K ≃ GaloisUnitsH2 K :=
  Equiv.ofBijective
    (Quotient.lift (brauerScalarDefectClass K) fun A B h ↦
      (brauerScalarDefectClass_eq_iff K A B).mpr h)
    ⟨fun a b ↦ Quotient.inductionOn₂ a b fun A B h ↦
      Quotient.sound ((brauerScalarDefectClass_eq_iff K A B).mp h),
    fun x ↦ by
      obtain ⟨A, hx⟩ := exists_csa_brauerScalarDefect K x
      exact ⟨Quotient.mk _ A, ((eq_brauerScalarDefectClass_iff K A x).mpr hx).symm⟩⟩

@[simp]
theorem brauerGroupEquivGaloisUnitsH2_mk (A : CSA.{u, u} K) :
    brauerGroupEquivGaloisUnitsH2 K (Quotient.mk _ A) = brauerScalarDefectClass K A :=
  rfl

theorem hasBrauerScalarDefect_brauerGroupEquivGaloisUnitsH2 (A : CSA.{u, u} K) :
    HasBrauerScalarDefect K A (brauerGroupEquivGaloisUnitsH2 K (Quotient.mk _ A)) :=
  hasBrauerScalarDefect_brauerScalarDefectClass K A

end Field
