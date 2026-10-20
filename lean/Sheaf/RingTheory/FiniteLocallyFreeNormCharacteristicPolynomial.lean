/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Sheaf.AlgebraicGeometry.PushforwardRankOnOpen
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Algebra.CharpolyLocallyFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.RingTheory.CoverModuleExact

/-!
# The norm characteristic polynomial of a finite locally free algebra

Source: Stacks Project, Tags 02DU(1), 02DV(1),(3), and 00DX; the polynomial in
`groupoids-lemma-integral-over-invariants`
(blueprint: lem-a1-finite-locally-free-norm-characteristic-polynomial).

The local determinant predicate uses every principal free chart and every finite basis.
Unique existence specifies canonical norms without assuming a global basis.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Local determinant characterization of a norm along a ring homomorphism. On each
principal open where the scalar extension is free, every finite basis gives the same
specified value. The multiplication endomorphism is scalar extended before taking its
matrix. Source: Stacks Project, Tags 02DU(1) and 02DV(1)
(blueprint: lem-a1-finite-locally-free-norm-characteristic-polynomial). -/
def IsLocallyFreeDeterminantNorm {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (N : B → A) : Prop :=
  letI : Algebra A B := φ.toAlgebra
  ∀ (a : A) (n : ℕ)
    (e : Module.Basis (Fin n) (Localization.Away a) (Localization.Away a ⊗[A] B))
    (b : B),
    algebraMap A (Localization.Away a) (N b) =
      (LinearMap.toMatrix e e ((Algebra.lmul A B b).baseChange (Localization.Away a))).det

/-- A finite locally free affine algebra has canonical determinant norms, and the norm of
`X - C b` is a degree-`r` characteristic polynomial annihilating `b`. Unique existence is
spelled out separately for each norm using only its local determinant characterization.
Thus the functions are determined independently of the asserted polynomial properties.
Source: Stacks Project, Tags 02DU(1), 02DV(1),(3), 00DX, and the second paragraph of
`groupoids-lemma-integral-over-invariants`
(blueprint: lem-a1-finite-locally-free-norm-characteristic-polynomial).

Proof:
1. If A is the zero ring, unitality forces B to be zero. Both norms are the unique
   functions, all polynomial identities hold, and all fibre conditions are vacuous.
2. Otherwise the finite locally free degree hypothesis identifies the finite flat rank
   with r (`lem-weil-pbc-finite-flat-rank-iso`). Apply
   `lem-sc-finite-pushforward-rank-on-open` to the whole target to obtain a locally free
   structure-sheaf pushforward of rank r (`def-amb-finite-locally-free-module`).
3. Refine trivializations to principal opens and choose a finite subcover using
   `lem-weil-pbc-spec-localization-away-basic-open` and
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`. Identify sections with
   localizations using `lem-weil-pbc-affine-module-basic-open-localization` and the
   invertibility in `lem-weil-pbc-basic-open-function`. This gives rank-r free charts.
4. The explicit coefficientwise isomorphism B tensor_A A[X] = B[X] identifies the
   polynomial extension with a base change (`lem-weil-pbc-fibre-product-affine-spectra`).
   Finite, flat, finite-presentation and degree-r properties persist by
   `lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-flat-morphism-base-change`,
   `lem-weil-pbc-qcqs-morphism-permanence`, and `lem-weil-pbc-finite-flat-rank-iso`.
   The same pushforward-rank lemma makes its pushforward quasi-coherent.
5. Localizing polynomial rings at C(f) gives A_f[X] and B_f[X]: use common denominators
   for finitely many coefficients. Constant polynomials of a local basis form a basis.
6. Apply `lem-weil-pbc-charpoly-locally-free-existence` to multiplication by each element
   of B and B[X]. `lem-weil-pbc-localization-module-tensor` identifies its scalar
   extension with local multiplication, giving local characteristic polynomials.
7. Set N(u) = (-1)^r times the constant coefficient of that characteristic polynomial.
   Locally this equals det(multiplication by u), as in `def-weil-endomorphism-determinant`.
   `lem-weil-pbc-charpoly-free-module-properties` gives basis independence;
   `lem-weil-pbc-quasi-coherent-affine-section-base-change` identifies all affine charts.
   `lem-weil-pbc-standard-covering-glue` gives uniqueness, for both rings.
8. In a constant polynomial basis multiplication by X-b has matrix XI-M(b). Hence its
   determinant is the local characteristic polynomial of multiplication by b.
   Coefficientwise injectivity from `lem-weil-pbc-standard-covering-glue` identifies
   P_b with the glued characteristic polynomial. Its expansion gives monicity and
   degree r when A is nonzero.
9. On every nonempty free chart, `lem-weil-cayley-hamilton-free-module` annihilates the
   multiplication endomorphism. Evaluation at 1 gives the required scalar polynomial
   identity in B_f.
10. Injectivity in `lem-weil-pbc-cover-module-exact` gives that identity in B. Rank zero
    has empty determinant 1 and forces B=0, so its annihilation assertion also holds. -/
theorem finiteLocallyFree_norm_characteristicPolynomial
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (h : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) :
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Polynomial.mapRingHom φ))).IsFiniteLocallyFreeOfDegree r ∧
    ∃ N : B → A,
      (IsLocallyFreeDeterminantNorm φ N ∧
        ∀ N' : B → A, IsLocallyFreeDeterminantNorm φ N' → N' = N) ∧
      ∃ Npoly : Polynomial B → Polynomial A,
        (IsLocallyFreeDeterminantNorm (Polynomial.mapRingHom φ) Npoly ∧
          ∀ Npoly' : Polynomial B → Polynomial A,
            IsLocallyFreeDeterminantNorm (Polynomial.mapRingHom φ) Npoly' →
              Npoly' = Npoly) ∧
        ∀ b : B,
          (∃ a : Fin r → A,
            Npoly (Polynomial.X - Polynomial.C b) =
              Polynomial.X ^ r +
                ∑ j : Fin r, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) ∧
          (Polynomial.map φ (Npoly (Polynomial.X - Polynomial.C b))).eval b = 0 ∧
          (Nontrivial A →
            (Npoly (Polynomial.X - Polynomial.C b)).Monic ∧
            (Npoly (Polynomial.X - Polynomial.C b)).natDegree = r) := by
  sorry

/-- The canonical determinant norm of a finite locally free affine algebra. This chooses
from the uniquely characterized norm in `finiteLocallyFree_norm_characteristicPolynomial`;
only its existence proof is postponed, and the local determinant values determine all
its data uniquely. Source: Stacks Project, Tags 02DU(1) and 02DV(1)
(blueprint: lem-a1-finite-locally-free-norm-characteristic-polynomial). -/
noncomputable def finiteLocallyFreeDeterminantNorm
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (h : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) :
    B → A :=
  Classical.choose (finiteLocallyFree_norm_characteristicPolynomial φ r h).2

/-- The canonical polynomial `N_{φ[X]}(X - C b)`. Its norm uses the degree-r polynomial
extension supplied by `finiteLocallyFree_norm_characteristicPolynomial`.
Source: Stacks Project, Tags 02DV(3), 00DX, and `groupoids-lemma-integral-over-invariants`
(blueprint: lem-a1-finite-locally-free-norm-characteristic-polynomial). -/
noncomputable def finiteLocallyFreeNormPolynomial
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (h : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r)
    (b : B) : Polynomial A :=
  finiteLocallyFreeDeterminantNorm (Polynomial.mapRingHom φ) r
    (finiteLocallyFree_norm_characteristicPolynomial φ r h).1 (Polynomial.X - Polynomial.C b)

end Algebra
