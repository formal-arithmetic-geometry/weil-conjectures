module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.RingTheory.SmoothLocalizationConormalSplit
import Sheaf.RingTheory.SymmetricAlgebraFinitePresentation
import Sheaf.RingTheory.SymmetricAlgebraSmooth
import Sheaf.RingTheory.SymmetricProjectivePresentationConormal

/-!
# Smooth presentation with free conormal module

Source: Stacks Project, Smoothing Ring Maps, Lemma 07CE, clause (1) for `a = 1`, smooth case
(blueprint: lem-weil-pbc-improve-presentation-smooth-conormal-free).
-/

@[expose] public section

universe u v

namespace Algebra

/--
Source: Stacks Project, Smoothing Ring Maps, Lemma 07CE, clause (1) for `a = 1`, with
`R → A` smooth (blueprint: lem-weil-pbc-improve-presentation-smooth-conormal-free).

Proof. Step 1: choose a finite presentation `A = P/I`, `P = R[x_1, …, x_n]`,
`I = (f_1, …, f_m)` (a smooth map is finitely presented), put `M = I/I²` and let
`q : A^m → M` send `e_j` to `f_j mod I²`. By
lem-weil-pbc-smooth-localization-conormal-split with `a = 1`, `M ⊕ Ω[A/R] ≅ A^n`, so `M` is
finite projective; a section `s` of `q` gives `K ⊕ M ≅ A^m` with `K = ker q`.
Step 2: let `C = Sym_A(M)` (lem-weil-pbc-symmetric-algebra-universal-property); the zero map
`M → A` induces the `A`-algebra retraction `ρ : C → A`. Since `M` is finite projective,
`A → C` is smooth (lem-weil-pbc-symmetric-algebra-finite-projective-smooth). The images of
`f_j mod I²` generate `C` over `A` (lem-weil-pbc-symmetric-algebra-finite-presentation), giving
a surjection `Q = R[x_1, …, x_n, y_1, …, y_m] → C` with `y_j ↦ f_j mod I²`; let `J` be its
kernel.
Step 3: lem-weil-pbc-symmetric-projective-presentation-conormal (with `M` projective) gives a
split exact sequence `0 → M ⊗_A C → J/J² → K ⊗_A C → 0`, so
`J/J² ≅ (M ⊕ K) ⊗_A C ≅ C^m` is free. Reindexing the `n + m` variables of `Q` gives the
required presentation.
-/
theorem improve_presentation_smooth_conormal_free
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Smooth R A] :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Smooth A C),
      ∃ (ρ : C →ₐ[A] A),
        ρ.comp (Algebra.ofId A C) = AlgHom.id A A ∧
      ∃ (m : ℕ) (f : MvPolynomial (Fin m) R →ₐ[R] C),
        Function.Surjective f ∧
        ∃ (J : Ideal (MvPolynomial (Fin m) R)),
          J = RingHom.ker f.toRingHom ∧
          Module.Free (MvPolynomial (Fin m) R ⧸ J) J.Cotangent := by
  sorry

end Algebra
