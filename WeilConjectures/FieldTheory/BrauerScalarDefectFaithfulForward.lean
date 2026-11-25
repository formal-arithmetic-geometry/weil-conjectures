/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import WeilConjectures.FieldTheory.BrauerScalarDefectAmplification
import WeilConjectures.FieldTheory.BrauerScalarDefectUnique

/-!
# Brauer-equivalent algebras have the same scalar-defect class

## Main results

- `Field.brauerScalarDefect_eq_of_brauerEquivalent`: Brauer-equivalent central simple algebras
  realize the same scalar-defect class.

## Implementation details

Both algebras are replaced by isomorphic matrix amplifications, which realize the same classes
(`Field.hasBrauerScalarDefect_of_matrix_algEquiv`); the realization is transported along the
isomorphism and uniqueness of the realized class concludes.

## References

* Stacks Project, Theorem 03R7 and Section 0DVG.
-/

@[expose] public section
universe u
namespace Field

private theorem scalarDefect_transport (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (f : A ≃ₐ[K] B) (x : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) : HasBrauerScalarDefect K B x := by
  obtain ⟨n, hn, e, b, hb, z, hz, hdesc, hdefect⟩ := hx
  let t := Algebra.TensorProduct.congr
    (AlgEquiv.refl : SeparableClosure K ≃ₐ[SeparableClosure K] SeparableClosure K) f.symm
  refine ⟨n, hn, t.trans e, b, hb, z, hz, ?_, hdefect⟩
  intro g a
  simpa [t] using hdesc g (f.symm a)

/-- If Brauer-equivalent central simple algebras `A` and `B` realize the classes `x` and `y` by
matrix scalar defects, then `x = y`. -/
theorem brauerScalarDefect_eq_of_brauerEquivalent (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : IsBrauerEquivalent A B) : x = y := by
  obtain ⟨n, m, hn, hm, ⟨f⟩⟩ := h
  let : NeZero n := ⟨hn⟩
  let : NeZero m := ⟨hm⟩
  let C : CSA.{u, u} K := { toAlgCat := .of K (Matrix (Fin n) (Fin n) A) }
  let D : CSA.{u, u} K := { toAlgCat := .of K (Matrix (Fin m) (Fin m) B) }
  have hxC : HasBrauerScalarDefect K C x :=
    hasBrauerScalarDefect_of_matrix_algEquiv K A C x n hn AlgEquiv.refl hx
  have hyD : HasBrauerScalarDefect K D y :=
    hasBrauerScalarDefect_of_matrix_algEquiv K B D y m hm AlgEquiv.refl hy
  have hxD : HasBrauerScalarDefect K D x := scalarDefect_transport K C D f x hxC
  exact brauerScalarDefect_unique K D x y hxD hyD
end Field
