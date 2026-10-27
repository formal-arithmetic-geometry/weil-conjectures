module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.GroupTheory.Finiteness

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Noetherian.Basic

/-! # Effectivity of formal homomorphisms from diagonalizable groups

Source: Conrad, Reductive group schemes (2014), Theorem B.3.2(1), formula (B.3.1),
printed p.288, restricted to a split source.
(blueprint: lem-sfb-adic-diagonalizable-hom-effectivity).

The quotient with index n is A/m^(n+1). Compatibility is expressed by a commuting
square between the actual pullbacks over adjacent quotient spectra. Unique lifting
is the bijectivity assertion for the canonical reduction map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace AdicGroupHom

/-- The quotient spectrum Spec(A/m^(n+1)), as an object over Spec A.
Source: Conrad, Theorem B.3.2(1), printed p.288, the bases S_n.
(blueprint: lem-sfb-adic-diagonalizable-hom-effectivity). -/
noncomputable def quotientBase (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Over (Spec (.of A)) :=
  (algSpec (.of A)).obj
    (op (CommAlgCat.of A (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))))

/-- The closed immersion Spec(A/m^(n+1)) → Spec(A/m^(n+2)) over Spec A.
It is Spec of the canonical quotient factor map, not an arbitrary transition.
Source: Conrad, Theorem B.3.2(1), printed p.288, the transition of the bases S_n.
(blueprint: lem-sfb-adic-diagonalizable-hom-effectivity). -/
noncomputable def successorBase (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    quotientBase A n ⟶ quotientBase A (n + 1) :=
  (algSpec (.of A)).map (CommAlgCat.ofHom
    (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        IsLocalRing.maximalIdeal A ^ ((n + 1) + 1) ≤
          IsLocalRing.maximalIdeal A ^ (n + 1)))).op

end AdicGroupHom

/-- Every compatible family of homomorphisms D_(A/m^n)(M) → G_(A/m^n), n ≥ 1,
is the reduction of a unique A-group homomorphism. No smoothness of G is assumed.
Source: Conrad, Reductive group schemes (2014), Theorem B.3.2(1), formula (B.3.1),
printed p.288, split-source case.
(blueprint: lem-sfb-adic-diagonalizable-hom-effectivity).

Proof, following the accepted seven-step DAG split:
1. Put C = A[M]. Affine duality (def-weil-affine-spectrum), the affine
   fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra), and the
   algebra tensor universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) identify the family
   with compatible Hopf maps f_n : B → (A/m^n)[M]. The identification sends
   e_m tensor a to a e_m and respects multiplication, counit and antipode.
2. By completeness (def-weil-pbc-adic-completion), every coefficient of f_n(b)
   lifts uniquely to a_m(b) in A. Separatedness detects equality of finite sums
   coefficient by coefficient. Finite support is not yet asserted.
3. Write Delta_B(b) = sum_i x_i tensor y_i. Put alpha_m = (a_m(x_i))_i in A^r
   and lambda_t(z) = sum_i z_i a_t(y_i). Comparing the (m,t) coefficient in the
   levelwise coalgebra identity gives lambda_t(alpha_m) = delta_(m,t) a_m(b).
   The tensor basis identification uses def-weil-pbc-module-tensor-product;
   separatedness lifts the identity from every quotient to A.
4. Apply lem-weil-pbc-noetherian-finite-module-acc to the submodules of A^r
   spanned by finite subsets of the alpha_m. A maximal one is spanned by some
   finite F and contains every alpha_m. For t outside F, lambda_t vanishes
   on its generators, so a_t(b) = lambda_t(alpha_t) = 0. This proves finite
   support without any flatness hypothesis on B and also when r = 0.
5. Define f(b) = sum_m a_m(b)e_m. Its reductions are f_n. The differences
   measuring additivity, multiplicativity, scalar compatibility and the unit
   reduce to zero at every level; coefficientwise separatedness kills them.
6. The same argument in the free module on M squared proves the coalgebra
   identity; the counit and antipode identities follow in A and C. Affine
   duality gives an actual group homomorphism with the prescribed reductions.
7. Equal reductions imply equality of all coefficients of the coordinate maps,
   hence equality of homomorphisms. Reductions of a homomorphism are compatible
   by functoriality of base change. This establishes the stated bijection,
   including M = 0 and character torsion in the residue characteristic. -/
theorem adic_diagonalizable_hom_effectivity
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (G : Grp (Over (Spec (.of A))))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (f : ∀ n : ℕ,
      (Over.pullback (AdicGroupHom.quotientBase A n).hom).mapGrp.obj
          (ringDiagonalizableGroup A M) ⟶
        (Over.pullback (AdicGroupHom.quotientBase A n).hom).mapGrp.obj G)
    (hf : ∀ n : ℕ,
      baseChangeMap (ringDiagonalizableGroup A M).X.hom
          (AdicGroupHom.successorBase A n) ≫ (f (n + 1)).hom.hom.left =
        (f n).hom.hom.left ≫ baseChangeMap G.X.hom (AdicGroupHom.successorBase A n)) :
    ∃! g : ringDiagonalizableGroup A M ⟶ G, ∀ n : ℕ,
      (Over.pullback (AdicGroupHom.quotientBase A n).hom).mapGrp.map g = f n := by
  sorry

end AlgebraicGeometry
