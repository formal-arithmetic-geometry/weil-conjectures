/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.Etale
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Polynomial solution algebras for Frobenius equations -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AlgebraicGeometry.Scheme

noncomputable section

variable (R : Type u) [CommRing R] (p n : ℕ)

/-- The equations b_i + X_i - sum_j c_ij X_j^p. -/
private def frobeniusSolutionRelation (c : Fin n → Fin n → R) (b : Fin n → R)
    (i : Fin n) : MvPolynomial (Fin n) R :=
  C (b i) + X i - ∑ j, C (c i j) * X j ^ p

/-- The explicit ideal of Frobenius solution equations. -/
private def frobeniusSolutionIdeal (c : Fin n → Fin n → R) (b : Fin n → R) :
    Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range (frobeniusSolutionRelation R p n c b))

/-- The explicit affine solution ring, including for n=0 or the zero ring. -/
private abbrev FrobeniusSolutionRing (c : Fin n → Fin n → R) (b : Fin n → R) :=
  MvPolynomial (Fin n) R ⧸ frobeniusSolutionIdeal R p n c b

private def solutionPresentation (c : Fin n → Fin n → R) (b : Fin n → R)
    (hp : (p : R) = 0) :
    Algebra.SquareJacobianPresentation R (FrobeniusSolutionRing R p n c b) (Fin n) where
  __ := Algebra.PreSubmersivePresentation.naive
    (v := frobeniusSolutionRelation R p n c b) id Function.injective_id
  map_eq_id := rfl
  jacobian_isUnit := by
    classical
    have hp' : (p : MvPolynomial (Fin n) R) = 0 := by
      rw [← map_natCast (algebraMap R _), hp, map_zero]
    have hJ : (Algebra.PreSubmersivePresentation.naive
        (v := frobeniusSolutionRelation R p n c b) id Function.injective_id).jacobiMatrix = 1 := by
      ext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      simp [frobeniusSolutionRelation, hp', Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hJ, Matrix.det_one]
    exact isUnit_one.map _

private theorem solutionRingEtale (c : Fin n → Fin n → R) (b : Fin n → R)
    (hp : (p : R) = 0) : Algebra.Etale R (FrobeniusSolutionRing R p n c b) :=
  (solutionPresentation R p n c b hp).etale

private theorem matrixEquationSolvable (p : ℕ) [Fact p.Prime]
    (K : Type v) [Field K] [CharP K p] [IsAlgClosed K]
    (n : ℕ) (c : Fin n → Fin n → K) (b : Fin n → K) :
    ∃ x : Fin n → K, ∀ i, ∑ j, c i j * x j ^ p - x i = b i := by
  classical
  let F : (Fin n → K) →ₛₗ[frobenius K p] (Fin n → K) :=
    { toFun := fun x i ↦ ∑ j, c i j * x j ^ p
      map_add' := by
        intro x y
        ext i
        simp only [Pi.add_apply, add_pow_char, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, frobenius_def]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  obtain ⟨x, hx⟩ := LinearMap.Frobenius.surjective_sub_id F b
  exact ⟨x, fun i ↦ congrFun hx i⟩

private theorem solutionRingHomExists (c : Fin n → Fin n → R) (b : Fin n → R)
    [Fact p.Prime] (K : Type v) [Field K] [CharP K p] [IsAlgClosed K] (φ : R →+* K) :
    ∃ ψ : FrobeniusSolutionRing R p n c b →+* K,
      ψ.comp (algebraMap R _) = φ := by
  classical
  obtain ⟨x, hx⟩ := matrixEquationSolvable p K n (fun i j ↦ φ (c i j)) (φ ∘ b)
  let e := MvPolynomial.eval₂Hom φ x
  have he : frobeniusSolutionIdeal R p n c b ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change e (frobeniusSolutionRelation R p n c b i) = 0
    simp only [e, frobeniusSolutionRelation, map_sub, map_add, map_sum, map_mul, map_pow,
      eval₂Hom_C, eval₂Hom_X']
    have hi := hx i
    change ∑ j, φ (c i j) * x j ^ p - x i = φ (b i) at hi
    linear_combination -hi
  refine ⟨Ideal.Quotient.lift _ e he, ?_⟩
  ext a
  simp [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R),
    Ideal.Quotient.algebraMap_eq, e]

private theorem solutionSpectrumSurjective (c : Fin n → Fin n → R) (b : Fin n → R)
    [Fact p.Prime] (hp : (p : R) = 0) :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (FrobeniusSolutionRing R p n c b))) := by
  intro q
  let K := AlgebraicClosure q.asIdeal.ResidueField
  let φ : R →+* K := (algebraMap q.asIdeal.ResidueField K).comp
    (algebraMap R q.asIdeal.ResidueField)
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast φ, hp, map_zero])
  obtain ⟨ψ, hψ⟩ := solutionRingHomExists R p n c b K φ
  refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, ?_⟩
  apply PrimeSpectrum.ext
  change (RingHom.ker ψ).comap (algebraMap R _) = q.asIdeal
  rw [RingHom.comap_ker, hψ]
  dsimp [φ]
  rw [RingHom.ker_comp_of_injective _ (algebraMap q.asIdeal.ResidueField K).injective,
    Ideal.ker_algebraMap_residueField]

private theorem solutionMapEtaleSurjective (c : Fin n → Fin n → R) (b : Fin n → R)
    [Fact p.Prime] (hp : (p : R) = 0) :
    Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (FrobeniusSolutionRing R p n c b)))) ∧
    Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap R (FrobeniusSolutionRing R p n c b)))) := by
  have : Algebra.Etale R (FrobeniusSolutionRing R p n c b) := solutionRingEtale R p n c b hp
  refine ⟨?_, ⟨solutionSpectrumSurjective R p n c b hp⟩⟩
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

private theorem map_toSpec_ext {T : Scheme.{u}} {Q : CommRingCat.{u}}
    {g h : T ⟶ Spec Q}
    (he : (Scheme.ΓSpecIso Q).inv ≫ g.appTop =
      (Scheme.ΓSpecIso Q).inv ≫ h.appTop) : g = h := by
  exact AlgebraicGeometry.ext_to_Spec he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine polynomial solution scheme is étale and surjective and has the expected
universal solution property, even when the matrix is singular or the rank is zero.

Source: Stacks Project, Tag 0GKU, label lemma-frobenius-linear-on-vb,
polynomial presentation in the surjectivity paragraph.
(blueprint: lem-weil-pbc-frobenius-polynomial-solution-cover)

Proof: Take the spectrum of the explicit quotient of Γ(X,O_X)[x_1,...,x_n]
by b_i+x_i-sum_j c_ij x_j^p and use the images of the variables as its sections.
The naive square presentation has identity Jacobian, because p vanishes in the base;
hence its structure morphism is étale. For each base prime, map into an algebraic
closure of its residue field. Lang--Steinberg solves the semilinear matrix equation,
so evaluation factors through the quotient. Its kernel is a prime over the given
prime, proving surjectivity. Evaluation at any solution tuple similarly factors uniquely
through the quotient. The Spec/global-sections adjunction makes this ring map the
unique scheme morphism with the displayed base and coordinate equations. -/
theorem frobenius_polynomial_solution_cover
    (X : Scheme.{u}) [IsAffine X] (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (c : Fin n → Fin n → Γ(X, ⊤)) (b : Fin n → Γ(X, ⊤)) :
    ∃ (P : Scheme.{u}) (π : P ⟶ X) (x : Fin n → Γ(P, ⊤)),
      IsAffine P ∧ Etale π ∧ Surjective π ∧
      (∀ i, ∑ j, π.appTop (c i j) * x j ^ p - x i = π.appTop (b i)) ∧
      ∀ (T : Scheme.{u}) (f : T ⟶ X) (y : Fin n → Γ(T, ⊤)),
        (∀ i, ∑ j, f.appTop (c i j) * y j ^ p - y i = f.appTop (b i)) →
        ∃! g : T ⟶ P, g ≫ π = f ∧ ∀ i, g.appTop (x i) = y i := by
  classical
  let R := Γ(X, ⊤)
  let I := frobeniusSolutionIdeal R p n c b
  let Q := CommRingCat.of (FrobeniusSolutionRing R p n c b)
  let q : R ⟶ Q := CommRingCat.ofHom (algebraMap R Q)
  let π := Spec.map q ≫ X.isoSpec.inv
  let v (i : Fin n) : Q := Ideal.Quotient.mk I (MvPolynomial.X i)
  let x (i : Fin n) : Γ(Spec Q, ⊤) := (Scheme.ΓSpecIso Q).inv (v i)
  have he := solutionMapEtaleSurjective R p n c b hp
  have : Etale (Spec.map q) := he.1
  have : Surjective (Spec.map q) := he.2
  have hπ : π.appTop = q ≫ (Scheme.ΓSpecIso Q).inv := by
    have heq : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso R).inv := by
      apply (cancel_mono X.isoSpec.hom.appTop).mp
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
      simp only [Scheme.Hom.id_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
      change 𝟙 R = (Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom
      exact (Scheme.ΓSpecIso R).inv_hom_id.symm
    rw [Scheme.Hom.comp_appTop, heq, Scheme.ΓSpecIso_inv_naturality]
  refine ⟨Spec Q, π, x, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro i
    have hz : Ideal.Quotient.mk I (frobeniusSolutionRelation R p n c b i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    have hz' : ∑ j, q (c i j) * v j ^ p - v i = q (b i) := by
      simp only [frobeniusSolutionRelation, map_sub, map_add, map_sum, map_mul, map_pow]
        at hz
      change q (b i) + v i - ∑ j, q (c i j) * v j ^ p = 0 at hz
      linear_combination -hz
    simpa only [hπ, CommRingCat.comp_apply, x, ← map_pow, ← map_mul,
      ← map_sum, ← map_sub] using congrArg (Scheme.ΓSpecIso Q).inv hz'
  · intro T f y hy
    let e := MvPolynomial.eval₂Hom f.appTop.hom y
    have heval (r : R) : e (MvPolynomial.C r) = f.appTop r :=
      MvPolynomial.eval₂Hom_C _ _ _
    have hevar (i : Fin n) : e (MvPolynomial.X i) = y i :=
      MvPolynomial.eval₂Hom_X' _ _ _
    have he : I ≤ RingHom.ker e := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change e (frobeniusSolutionRelation R p n c b i) = 0
      simp only [frobeniusSolutionRelation, map_sub, map_add, map_sum, map_mul, map_pow,
        hevar]
      have hs : (∑ j, e (C (c i j)) * y j ^ p) =
          ∑ j, f.appTop (c i j) * y j ^ p := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun a ↦ a * y j ^ p) (heval (c i j))
      erw [heval (b i), hs]
      linear_combination -(hy i)
    let l : Q ⟶ Γ(T, ⊤) := CommRingCat.ofHom (Ideal.Quotient.lift I e he)
    let g := T.toSpecΓ ≫ Spec.map l
    have hgl : (Scheme.ΓSpecIso Q).inv ≫ g.appTop = l := by
      change (Scheme.ΓSpecIso Q).inv ≫
        (Spec.map l).appTop ≫ T.toSpecΓ.appTop = l
      rw [← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop,
        Iso.inv_hom_id, Category.comp_id]
    have hfl : q ≫ l = f.appTop := by
      ext a
      change e (MvPolynomial.C a) = f.appTop a
      exact MvPolynomial.eval₂Hom_C _ _ _
    refine ⟨g, ⟨?_, ?_⟩, ?_⟩
    · change T.toSpecΓ ≫ (Spec.map l ≫ Spec.map q) ≫ X.isoSpec.inv = f
      rw [← Spec.map_comp, hfl, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
        Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
    · intro i
      change ((Scheme.ΓSpecIso Q).inv ≫ g.appTop) (v i) = y i
      rw [hgl]
      change e (MvPolynomial.X i) = y i
      exact MvPolynomial.eval₂Hom_X' _ _ _
    · intro h hh
      apply map_toSpec_ext
      rw [hgl]
      let k := (Scheme.ΓSpecIso Q).inv ≫ h.appTop
      have hfk : q ≫ k = f.appTop := by
        rw [← hh.1, Scheme.Hom.comp_appTop, hπ, Category.assoc]
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        change k (q a) = l (q a)
        exact (ConcreteCategory.congr_hom hfk a).trans
          (ConcreteCategory.congr_hom hfl a).symm
      · intro i
        change h.appTop (x i) = l (v i)
        rw [hh.2 i]
        change y i = e (MvPolynomial.X i)
        exact (MvPolynomial.eval₂Hom_X' _ _ _).symm

end
end AlgebraicGeometry.Scheme
