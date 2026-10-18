/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.LinearAlgebra.Dimension.Free
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.DeltaFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Finite free change of Kummer coefficients

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-kummer-coefficient-base-change.md, order 1925
(blueprint: lem-pur-kummer-coefficient-base-change).

The comparison is specified on pure tensors. Integral lifts are represented in a finite
basis: tensoring the Kummer sequence with L is its finite biproduct in this basis. Both
comparison isomorphisms are normalized on the basis, so no arbitrary comparison or
boundary is substituted for the actual connecting homomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Finite sums of abelian sheaves, using the standard products-to-biproducts construction.
Source: blueprint integral-lift finite direct sum, Stacks Tag 015B
(blueprint: lem-pur-kummer-coefficient-base-change). -/
instance kummerIntegralLift_hasFiniteBiproducts (C : Scheme.{u}) :
    HasFiniteBiproducts (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The integral-lift clause for the coefficient boundary, in any finite integral basis.
Here `e` is the specified identification L/mL = A. The two biproduct maps are exactly
inclusion of roots and multiplication by m on each summand. The isomorphism `alpha`
sends u tensor l to the cohomology of g maps to g tensor l; `theta` sends the j-th root
summand to z maps to z tensor e([b_j]). The last equality says that the actual connecting
map of this short exact sequence descends to the specified coefficient boundary.

Source: blueprint sk-prop-a1-kummer, lem-pur-kummer-coefficient-base-change, integral-lift
paragraph; Stacks Tags 03PL, 03EK and 015B
(blueprint: lem-pur-kummer-coefficient-base-change). -/
def KummerIntegralLiftBoundary (C : Scheme.{u}) (m q : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (delta : (Sheaf.H C.gmSheaf q ⊗[ℤ] A) →+
      Sheaf.H ((kummerAbelianTwist C m).obj A) (q + 1)) : Prop :=
  ∀ (L : ModuleCat.{u + 1} ℤ) (r : ℕ) (b : Module.Basis (Fin r) ℤ L)
    (e : (L ⧸ LinearMap.range ((m : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))) ≃ₗ[ℤ] A),
    ∃ (w : biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).f) ≫
        biproduct.map (fun _ : Fin r ↦ (C.kummerSequence m).g) = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact)
      (alpha : (Sheaf.H C.gmSheaf q ⊗[ℤ] L) ≃+
        Sheaf.H (⨁ fun _ : Fin r ↦ C.gmSheaf) q)
      (theta : (⨁ fun _ : Fin r ↦ C.rootsOfUnitySheaf m) ≅
        (kummerAbelianTwist C m).obj A),
      (∀ (x : Sheaf.H C.gmSheaf q) (l : L),
        alpha (x ⊗ₜ[ℤ] l) = Sheaf.H.map
          (∑ j : Fin r, (b.repr l j) • biproduct.ι (fun _ : Fin r ↦ C.gmSheaf) j) q x) ∧
      (∀ j : Fin r,
        biproduct.ι (fun _ : Fin r ↦ C.rootsOfUnitySheaf m) j ≫ theta.hom =
          kummerCoefficientInsertion C m A (e (Submodule.Quotient.mk (b j)))) ∧
      ∀ (x : Sheaf.H C.gmSheaf q) (l : L),
        delta (x ⊗ₜ[ℤ] e (Submodule.Quotient.mk l)) =
          Sheaf.H.map theta.hom (q + 1)
            (Sheaf.H.δSucc hS q (alpha (x ⊗ₜ[ℤ] l)))

/-- Finite free constant coefficients commute with Kummer cohomology in every degree,
and the coefficient boundary is the descent of the boundary for every integral lift.
The pure-tensor equations uniquely specify both the comparison and the descended map;
in particular the latter is independent of the integral lift and includes the units
Kummer class when q = 0.

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-kummer-coefficient-base-change.md, order 1925
(blueprint: lem-pur-kummer-coefficient-base-change).

Proof:
1. Use enough injectives and additive left exact sections from
   def-weil-pbc-sites-and-cohomology. Bounded below injective resolutions are K-injective
   (lem-weil-pbc-bounded-below-injectives-kinjective). The universal right-derived
   delta-functor (lem-weil-pbc-right-derived-universal-delta-functor, Stacks 015B/05TE)
   makes cohomology additive and its boundaries natural. Scalar endomorphisms give the
   residue-ring actions already recorded in def-pur-kummer-module-coefficients.
2. Choose a finite R-basis e_j of A with coordinate maps lambda_j. Insertion i_j and
   projection p_j on the sheafified tensor (def-pur-sheaf-tensor-product and
   def-kun-constant-sheaf) satisfy p_j i_h = delta_jh and sum i_j p_j = id, including
   the empty basis. Locally constant sections have the same coordinate expansions.
3. Additivity and i_(ta) = i_a composed with t make H(i_a)(x) R-bilinear. The induced
   tensor map has inverse y maps to sum H(p_j)(y) tensor e_j. The two basis identities
   prove that these are inverses. The defining formula does not depend on the basis.
4. The exponent m is invertible by the finite-field datum. The ordinary Kummer sequence
   is short exact (lem-sc-kummer-exact, Stacks 03PL). A finite free integral lift exists
   by lifting a basis. For any lift L, use a finite integral basis b_j. Tensoring gives
   the finite biproduct of the ordinary sequence, hence is short exact. Additivity gives
   alpha with inverse sum H(P_j)(y) tensor b_j. The left-term comparison sends z tensor l
   to z tensor e([l]); it is an isomorphism because m kills z. Naturality of connecting
   maps for g maps to g tensor l gives the displayed integral-lift boundary equality.
5. This equality kills x tensor ml. The tensor universal property identifies its quotient
   with H(G_m) tensor (L/mL), so the boundary descends to A. Its pure-tensor formula is
   beta(partial(x) tensor a), independent of L, its basis, and lifts of a. Pure tensors
   generate, giving independence. At q=0 this is the ordinary units Kummer class.
-/
theorem kummer_coefficient_base_change (P : WeilConjectures.PurityFiniteSetting.{u})
    (N : ℕ) (hN : 1 ≤ N) (C : Scheme.{u})
    (f : C ⟶ Spec (CommRingCat.of P.field.k)) [IsCurve f] [Smooth f]
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (P.coefficients.l ^ N))))
    [Module.Free (ULift.{u + 1} (ZMod (P.coefficients.l ^ N))) A]
    [Module.Finite (ULift.{u + 1} (ZMod (P.coefficients.l ^ N))) A] :
    ∃ (hm : IsUnit ((P.coefficients.l ^ N : ℕ) : Γ(C, ⊤)))
      (beta : ∀ q : ℕ,
        (Sheaf.H (C.rootsOfUnitySheaf (P.coefficients.l ^ N)) q ⊗[
          ULift.{u + 1} (ZMod (P.coefficients.l ^ N))] A) ≃ₗ[
            ULift.{u + 1} (ZMod (P.coefficients.l ^ N))]
          Sheaf.H ((kummerAbelianTwist C (P.coefficients.l ^ N)).obj A) q),
      (∀ (q : ℕ) (x : Sheaf.H (C.rootsOfUnitySheaf (P.coefficients.l ^ N)) q) (a : A),
        beta q (x ⊗ₜ a) =
          Sheaf.H.map (kummerCoefficientInsertion C (P.coefficients.l ^ N) A a) q x) ∧
      ∃ delta : ∀ q : ℕ, (Sheaf.H C.gmSheaf q ⊗[ℤ] A) →+
          Sheaf.H ((kummerAbelianTwist C (P.coefficients.l ^ N)).obj A) (q + 1),
        (∀ (q : ℕ) (x : Sheaf.H C.gmSheaf q) (a : A),
          delta q (x ⊗ₜ[ℤ] a) = beta (q + 1)
            (Sheaf.H.δSucc (C.kummerSequence_shortExact (P.coefficients.l ^ N) hm) q x ⊗ₜ a)) ∧
        ∀ q : ℕ, KummerIntegralLiftBoundary C (P.coefficients.l ^ N) q A (delta q) := by
  sorry

end AlgebraicGeometry.Scheme
