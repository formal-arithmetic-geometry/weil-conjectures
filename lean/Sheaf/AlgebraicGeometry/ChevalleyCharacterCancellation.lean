module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Chevalley line stabilizers with trivial stabilizer character

Source: Milne, Algebraic Groups (2017), Theorem 4.27 and Corollary 4.29,
printed pp.94--95, and Remark 4.30, p.96.
(blueprint: lem-sfb-chevalley-character-cancellation)

Finite-dimensional spaces are written in a basis as k^(ULift (Fin n)), including n = 0.
The scalar extension of a subspace is its A-span in A^(ULift (Fin n)). A character
is evaluated on the Laurent coordinate t; evaluation on t^(-m) gives its negative power.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Chevalley's stabilizer line can be chosen pointwise fixed under character cancellation.
Source: Milne, Theorem 4.27, Corollary 4.29 and Remark 4.30, pp.94--96
(blueprint: lem-sfb-chevalley-character-cancellation).

Proof: (1) Apply lem-sfb-chevalley-scheme-line-stabilizer to obtain E and a line D
with stabilizer H on every algebra. Choose a nonzero e in D. The action on Ae is
a character chi: its coefficient in a basis beginning with e is regular on H,
its inverse is the coefficient at h inverse, and multiplication gives multiplicativity.
Thus chi occurs. The hypothesis gives m > 0, a representation F and a nonzero
scalar-action subspace U of character chi^(-m). Choose a nonzero f in U.
(2) Give E tensor-power m tensor F the diagonal rational action, whose matrix
coefficients are products of the original matrix coefficients. The line generated
by e tensor-power m tensor f is one-dimensional, and H acts on it by
chi^m chi^(-m) = 1, so H is contained in its stabilizer and fixes it pointwise.
(3) Conversely, over a nonzero algebra, a point stabilizing that line satisfies
x tensor-power m tensor y = c (e tensor-power m tensor f), where c is a unit,
x = g e and y = g f. Coordinate functionals composed with the inverse matrices
give lambda(x) = mu(y) = 1. Contract all but the first x factor using lambda and mu.
This yields x = a e with a = c lambda(e)^(m-1) mu(f). Applying lambda gives
1 = a lambda(e), so a is a unit. Hence g stabilizes D and belongs to H by the
Chevalley line-stabilizer equality. Over the zero algebra all point groups are
singletons and the same equality holds. These are the three proof steps of the node. -/
theorem chevalley_character_cancellation
    {k : Type u} [Field k] (G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : H ⟶ G) [IsClosedSubgroupScheme i]
    (hc : ∀ (χ : H ⟶ StandardGroupSchemes.multiplicative k) [IsMonHom χ],
      (∃ (n : ℕ) (ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n)))
        (_ : IsMonHom ρ) (U : Submodule k (ULift.{u} (Fin n) → k)),
        U ≠ ⊥ ∧ ∀ (A : Type u) [CommRing A] [Algebra k A]
          (h : points H A) (v : ULift.{u} (Fin n) → A),
          v ∈ Submodule.span A
            ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
              (U : Set (ULift.{u} (Fin n) → k))) →
          Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
            (h ≫ i ≫ ρ)) v =
            ((Spec.preimage (h ≫ χ).left).hom (LaurentPolynomial.T 1)) • v) →
      ∃ (m : ℕ), 0 < m ∧
        ∃ (n : ℕ) (ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n)))
          (_ : IsMonHom ρ) (U : Submodule k (ULift.{u} (Fin n) → k)),
          U ≠ ⊥ ∧ ∀ (A : Type u) [CommRing A] [Algebra k A]
            (h : points H A) (v : ULift.{u} (Fin n) → A),
            v ∈ Submodule.span A
              ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
                (U : Set (ULift.{u} (Fin n) → k))) →
            Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
              (h ≫ i ≫ ρ)) v =
              ((Spec.preimage (h ≫ χ).left).hom (LaurentPolynomial.T (-(m : ℤ)))) • v) :
    ∃ (n : ℕ) (ρ : GeneralLinearGroup.RationalHom G (ULift.{u} (Fin n)))
      (_ : IsMonHom ρ) (L : Submodule k (ULift.{u} (Fin n) → k)),
      Module.finrank k L = 1 ∧ ∀ (A : Type u) [CommRing A] [Algebra k A],
        (∀ g : points G A,
          (∃ h : points H A, h ≫ i = g) ↔
            Submodule.map
              (Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (g ≫ ρ)))
              (Submodule.span A
                ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
                  (L : Set (ULift.{u} (Fin n) → k)))) =
              Submodule.span A
                ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
                  (L : Set (ULift.{u} (Fin n) → k)))) ∧
        (∀ (h : points H A) (v : ULift.{u} (Fin n) → A),
          v ∈ Submodule.span A
            ((fun w : ULift.{u} (Fin n) → k ↦ fun j ↦ algebraMap k A (w j)) ''
              (L : Set (ULift.{u} (Fin n) → k))) →
          Matrix.toLin' (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A
            (h ≫ i ≫ ρ)) v = v) := by
  sorry

end AlgebraicGeometry
