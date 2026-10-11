/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Improving a presentation by a symmetric algebra

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CE and its proof, restricted to
smooth localizations (blueprint: lem-weil-pbc-improve-presentation).

## Main statements

* `Algebra.exists_finiteType_retract_smooth_free_differentials`: the finite type retract.
* `Algebra.Presentation.symmetricAlgebra_improves`: the specified conormal construction.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Stacks Project, Lemma 07CE, smooth case
(blueprint: lem-weil-pbc-improve-presentation).

Proof: choose a finite polynomial presentation with kernel `I`. The conormal module
`I/I²` is finitely generated, so its symmetric algebra `C` is of finite type over `A`
(lem-weil-pbc-symmetric-algebra-finite-presentation). Its degree-zero projection is an
`A`-algebra retraction (lem-weil-pbc-symmetric-algebra-universal-property).
Localization commutes with symmetric algebras (lem-weil-pbc-localization-tensor,
lem-weil-pbc-symmetric-algebra-base-change). If `A_a` is smooth over `R`, the localized
conormal module `M_a` is finite projective and `M_a ⊕ Ω[A_a/R]` is finite free: use the
localized presentation with relation `hx₀ - 1`, the Jacobi--Zariski sequence and the
polynomial differential basis (lem-weil-pbc-principal-localization-naive-cotangent,
lem-weil-pbc-jacobi-zariski-quotient-smooth, lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-polynomial-ring-kahler-basis). Thus `C_a = Sym_{A_a}(M_a)` is smooth over
`A_a` and over `R` (lem-weil-pbc-symmetric-algebra-finite-projective-smooth,
lem-weil-pbc-smooth-ring-map-base-change-composition). The differential sequence for
`R → A_a → C_a` is short exact and splits, since `Ω[C_a/A_a] = C_a ⊗ M_a` is projective
(lem-weil-pbc-jacobi-zariski-homology-sequence,
lem-weil-pbc-cotangent-complex-symmetric-algebra). Its middle module is therefore
`C_a ⊗ (Ω[A_a/R] ⊕ M_a)`, which is free. -/
theorem exists_finiteType_retract_smooth_free_differentials
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      letI : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
      FiniteType A C ∧ ∃ ρ : C →ₐ[A] A,
        (∀ x : A, ρ (algebraMap A C x) = x) ∧
        ∀ a : A, Smooth R (Localization.Away a) →
          Smooth R (Localization.Away (algebraMap A C a)) ∧
          Module.Free (Localization.Away (algebraMap A C a))
            (KaehlerDifferential R (Localization.Away (algebraMap A C a))) := by
  sorry

/-- Stacks Project, proof of Lemma 07CE: for any finite presentation one may take
`Sym_A(I/I²)` and its degree-zero projection
(blueprint: lem-weil-pbc-improve-presentation).

Proof: the relations of `P` generate its conormal module, so the symmetric algebra is
finite type (lem-weil-pbc-symmetric-algebra-finite-presentation). The map
`SymmetricAlgebra.lift 0` kills the degree-one generators and is the identity on `A`
(lem-weil-pbc-symmetric-algebra-universal-property). After localization, the conormal
module is finite projective and its direct sum with `Ω[A_a/R]` is finite free, by the
localized polynomial presentation and the Jacobi--Zariski sequence
(lem-weil-pbc-principal-localization-naive-cotangent,
lem-weil-pbc-jacobi-zariski-quotient-smooth, lem-weil-pbc-polynomial-ring-smooth,
lem-weil-pbc-polynomial-ring-kahler-basis). Symmetric algebra commutes with localization
(lem-weil-pbc-localization-tensor, lem-weil-pbc-symmetric-algebra-base-change), and the
symmetric algebra of this finite projective module is smooth over `A_a`, hence over `R`
(lem-weil-pbc-symmetric-algebra-finite-projective-smooth,
lem-weil-pbc-smooth-ring-map-base-change-composition). Finally the differential sequence
splits with outer terms `C_a ⊗ Ω[A_a/R]` and `C_a ⊗ (I/I²)_a`, giving a free middle term
(lem-weil-pbc-jacobi-zariski-homology-sequence,
lem-weil-pbc-cotangent-complex-symmetric-algebra). -/
theorem Presentation.symmetricAlgebra_improves
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Presentation R A (Fin n) (Fin m)) :
    let C := SymmetricAlgebra A P.toExtension.Cotangent
    letI : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
    FiniteType A C ∧
      (∀ x : A, (SymmetricAlgebra.lift (0 : P.toExtension.Cotangent →ₗ[A] A))
        (algebraMap A C x) = x) ∧
      ∀ a : A, Smooth R (Localization.Away a) →
        Smooth R (Localization.Away (algebraMap A C a)) ∧
        Module.Free (Localization.Away (algebraMap A C a))
          (KaehlerDifferential R (Localization.Away (algebraMap A C a))) := by
  sorry

end Algebra
