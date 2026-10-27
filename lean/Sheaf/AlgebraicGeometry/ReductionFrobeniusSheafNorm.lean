module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-! # A uniform Frobenius power gives a sheaf norm for the reduction immersion

Source: Stacks Project, Divisors, Tag 0BDZ (divisors-lemma-Frobenius-gives-norm-for-reduction);
norm conditions in Tag 0BCX (divisors-section-norms).
(blueprint: lem-sfb-reduction-frobenius-sheaf-norm)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A uniform Frobenius power gives a compatible sheaf norm for the reduction immersion.

Source: Stacks Project, Divisors, Tag 0BDZ (divisors-lemma-Frobenius-gives-norm-for-reduction);
norm conditions in Tag 0BCX (divisors-section-norms).
(blueprint: lem-sfb-reduction-frobenius-sheaf-norm)

Proof:
1. Apply `lem-sc-reduction-nilradical-nilpotent` to choose one positive exponent `n`
   killing the nilradical on all of `X`. Choose `e ≥ 1` with `p ^ e ≥ n`; then the
   `p ^ e`-th power of every local nilradical section vanishes.
2. The prime vanishes in every section ring since its germs vanish. By
   `def-weil-ring-frobenius`, the power map is a unital ring endomorphism on each
   open, including the empty open, and commutes with restriction.
3. The quotient-sheaf description of `def-weil-pbc-scheme-reduction` supplies local
   lifts of any section on the reduction. Two lifts differ by a nilradical section,
   so their `p ^ e`-th powers agree by steps 1 and 2. This works on intersections
   without assuming that they are affine.
4. Glue these powers using the structure sheaf axiom of `def-pc-scheme`. Independence
   of lifts and covers, additivity, multiplicativity, preservation of one and
   compatibility with restriction all follow by checking on the lifting cover.
5. A section of `X` itself lifts its pullback, giving the scalar-power identity.
   On every affine open, `def-weil-closed-immersion` and the reduction description
   identify the pullback ring with the quotient by the nilradical, so the formula
   is precisely the `p ^ e`-th power of a representative.
6. For a local lift at `i(y)`, `def-weil-residue-field` identifies its residue at `y`
   with the image of its residue at `i(y)`. A field homomorphism is injective, so
   vanishing upstairs implies vanishing downstairs, and its power also vanishes.
   For the empty open the section homomorphism is unique and this clause is vacuous.
-/
theorem reduction_frobenius_sheaf_norm (p : ℕ) (hp : p.Prime) (X : Scheme.{u})
    [IsNoetherian X] (hchar : ∀ x : X, (p : X.presheaf.stalk x) = 0) :
    ∃ e : ℕ, 1 ≤ e ∧
      ∃ ν : ∀ V : X.Opens,
        Γ(X.nilradical.subscheme, X.nilradical.subschemeι ⁻¹ᵁ V) →+* Γ(X, V),
        (∀ (V W : X.Opens) (hVW : V ≤ W)
          (b : Γ(X.nilradical.subscheme, X.nilradical.subschemeι ⁻¹ᵁ W)),
          X.presheaf.map (homOfLE hVW).op (ν W b) =
            ν V (X.nilradical.subscheme.presheaf.map
              (homOfLE (X.nilradical.subschemeι.preimage_mono hVW)).op b)) ∧
        (∀ (V : X.Opens) (a : Γ(X, V)),
          ν V (X.nilradical.subschemeι.app V a) = a ^ (p ^ e)) ∧
        (∀ (U : X.affineOpens) (a : Γ(X, U.1)),
          ν U.1 ((X.nilradical.subschemeObjIso U).inv
            (Ideal.Quotient.mk (X.nilradical.ideal U) a)) = a ^ (p ^ e)) ∧
        (∀ (V : X.Opens)
          (b : Γ(X.nilradical.subscheme, X.nilradical.subschemeι ⁻¹ᵁ V))
          (y : X.nilradical.subscheme) (hy : y ∈ X.nilradical.subschemeι ⁻¹ᵁ V),
          X.nilradical.subscheme.evaluation (X.nilradical.subschemeι ⁻¹ᵁ V) y hy b = 0 →
            X.evaluation V (X.nilradical.subschemeι y) hy (ν V b) = 0) := by
  sorry

end AlgebraicGeometry.Scheme
