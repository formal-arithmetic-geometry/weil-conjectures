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
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.AlgebraicGeometry.KummerFiniteBiproducts
import Sheaf.AlgebraicGeometry.KummerFiniteFreeComparison
import Sheaf.AlgebraicGeometry.KummerIntegralRootComparison
import WeilConjectures.AlgebraicGeometry.Sites.Kummer

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Finite sums of abelian sheaves, using the standard products-to-biproducts construction.
Source: blueprint integral-lift finite direct sum, Stacks Tag 015B
(blueprint: lem-pur-kummer-coefficient-base-change). -/
instance kummerIntegralLift_hasFiniteBiproducts (C : Scheme.{u}) :
    HasFiniteBiproducts (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def kummerInsertionAddHom (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :
    A →+ (C.rootsOfUnitySheaf m ⟶ (kummerAbelianTwist C m).obj A) where
  toFun := kummerCoefficientInsertion C m A
  map_zero' := by
    ext U x
    change (toSheafify C.smallEtaleTopology
      (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
        (x ⊗ₜ (0 : A)) = 0
    rw [TensorProduct.tmul_zero, map_zero]
  map_add' a b := by
    ext U x
    change (toSheafify C.smallEtaleTopology
      (kummerRootModulePresheaf C m ⊗ (Functor.const C.Etaleᵒᵖ).obj A)).app U
        (x ⊗ₜ (a + b)) = _
    rw [TensorProduct.tmul_add, map_add]
    rfl

private lemma kummer_exponent_unit (P : WeilConjectures.PurityFiniteSetting.{u})
    (C : Scheme.{u}) (f : C ⟶ Spec (CommRingCat.of P.field.k)) (N : ℕ) (_hN : 1 ≤ N) :
    IsUnit ((P.coefficients.l ^ N : ℕ) : Γ(C, ⊤)) := by
  let D := P.field
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hl : IsUnit (P.coefficients.l : D.k) :=
    (CharP.isUnit_natCast_iff (R := D.k) D.prime).2 (fun h ↦
      P.coefficients.different
        ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : P.coefficients.l.Prime)).1 h).symm)
  let phi := (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ f.appTop
  simpa only [map_pow, map_natCast, Nat.cast_pow] using (hl.pow N).map phi.hom

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

set_option backward.isDefEq.respectTransparency false in
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
  classical
  let m := P.coefficients.l ^ N
  let R := ULift.{u + 1} (ZMod m)
  have hm : IsUnit (m : Γ(C, ⊤)) := kummer_exponent_unit P C f N hN
  obtain ⟨beta, hbeta⟩ := kummer_finite_free_comparison C m A
  let boundary := C.kummerSequence_shortExact m hm
  let pair (q : ℕ) : Sheaf.H C.gmSheaf q →+
      A →+ Sheaf.H ((kummerAbelianTwist C m).obj A) (q + 1) :=
    { toFun := fun x ↦ (beta (q + 1)).toAddEquiv.toAddMonoidHom.comp
        ((TensorProduct.mk R (Sheaf.H (C.rootsOfUnitySheaf m) (q + 1)) A
          (Sheaf.H.δSucc boundary q x)).toAddMonoidHom)
      map_zero' := by
        apply AddMonoidHom.ext
        intro a
        change beta (q + 1) (Sheaf.H.δSucc boundary q 0 ⊗ₜ a) = 0
        rw [map_zero, TensorProduct.zero_tmul, map_zero]
      map_add' := by
        intro x y
        apply AddMonoidHom.ext
        intro a
        change beta (q + 1) (Sheaf.H.δSucc boundary q (x + y) ⊗ₜ a) =
          beta (q + 1) (Sheaf.H.δSucc boundary q x ⊗ₜ a) +
            beta (q + 1) (Sheaf.H.δSucc boundary q y ⊗ₜ a)
        rw [map_add, TensorProduct.add_tmul, map_add] }
  let delta (q : ℕ) : (Sheaf.H C.gmSheaf q ⊗[ℤ] A) →+
      Sheaf.H ((kummerAbelianTwist C m).obj A) (q + 1) :=
    TensorProduct.liftAddHom (pair q) (by
      intro n x a
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul])
  have hdelta (q : ℕ) (x : Sheaf.H C.gmSheaf q) (a : A) :
      delta q (x ⊗ₜ[ℤ] a) = beta (q + 1) (Sheaf.H.δSucc boundary q x ⊗ₜ a) :=
    TensorProduct.liftAddHom_tmul _ _ _ _
  refine ⟨hm, beta, hbeta, delta, hdelta, ?_⟩
  intro q L r b e
  obtain ⟨w, hS⟩ := kummer_biproduct_shortExact C m hm r
  obtain ⟨alpha, halpha⟩ := integral_cohomology_biproduct C C.gmSheaf L r b q
  obtain ⟨theta, htheta⟩ := kummer_integral_root_comparison C m A L r b e
  refine ⟨w, hS, alpha, theta, halpha, htheta, ?_⟩
  intro x l
  let J (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) : G ⟶ ⨁ fun _ : Fin r ↦ G :=
    ∑ j : Fin r, (b.repr l j) • biproduct.ι (fun _ : Fin r ↦ G) j
  have hJ {G G' : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : G ⟶ G') :
      J G ≫ biproduct.map (fun _ : Fin r ↦ a) = a ≫ J G' := by
    simp only [J, Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, biproduct.ι_map]
  let phi : C.kummerSequence m ⟶ ShortComplex.mk _ _ w :=
    { τ₁ := J (C.rootsOfUnitySheaf m)
      τ₂ := J C.gmSheaf
      τ₃ := J C.gmSheaf
      comm₁₂ := hJ (C.kummerSequence m).f
      comm₂₃ := hJ (C.kummerSequence m).g }
  have hleft : phi.τ₁ ≫ theta.hom = kummerCoefficientInsertion C m A
      (e (Submodule.Quotient.mk l)) := by
    change (∑ j : Fin r, (b.repr l j) •
      biproduct.ι (fun _ : Fin r ↦ C.rootsOfUnitySheaf m) j) ≫ theta.hom = _
    rw [Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, htheta]
    let v : L →+ A := e.toAddEquiv.toAddMonoidHom.comp
      (Submodule.mkQ _).toAddMonoidHom
    change (∑ j : Fin r, (b.repr l j) • kummerInsertionAddHom C m A (v (b j))) =
      kummerInsertionAddHom C m A (v l)
    let g := (kummerInsertionAddHom C m A).comp v
    change (∑ j : Fin r, (b.repr l j) • g (b j)) = g l
    calc
      _ = g (∑ j : Fin r, (b.repr l j) • b j) := by simp only [map_sum, map_zsmul]
      _ = g l := congrArg g (by
        calc
          _ = ∑ j : Fin r, L.isModule.smul (b.repr l j) (b j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact (int_smul_eq_zsmul L.isModule _ _).symm
          _ = l := b.sum_repr l)
  rw [hdelta, hbeta, halpha]
  change Sheaf.H.map (kummerCoefficientInsertion C m A
    (e (Submodule.Quotient.mk l))) (q + 1) (Sheaf.H.δSucc boundary q x) =
      Sheaf.H.map theta.hom (q + 1)
        (Sheaf.H.δSucc hS q (Sheaf.H.map phi.τ₃ q x))
  rw [← hleft, Sheaf.H.map_comp_apply]
  exact congrArg (Sheaf.H.map theta.hom (q + 1))
    (Sheaf.H.map_δSucc boundary hS phi q x)

end AlgebraicGeometry.Scheme
