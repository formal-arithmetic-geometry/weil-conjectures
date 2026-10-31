/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Algebra.Polynomial.Derivation
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import all Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot

/-!
# Regularity and monomial bases of transverse local root families

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133,
full simultaneous parameter-root algebra before invariants; Stacks Tags 00NU and 07PF.
The simultaneous induction over coefficient strata and partial root subsets is the
agent expansion recorded in the DAG.
(blueprint: lem-sfb-transverse-local-root-family-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

/-- The coefficient stratum `R_J = R/(t_j : j ∈ J)` in the local root calculation.
Source: ILO IX, Proposition 2.1 proof, p.133, simultaneous parameter-root presentation
and its coordinate strata (blueprint: lem-sfb-transverse-local-root-family-regular). -/
abbrev transverseRootCoefficientRing {R : Type u} [CommRing R] {I : Type v}
    (t : I → R) (J : Finset I) :=
  R ⧸ Ideal.span (t '' (J : Set I))

/-- The relations `x_i^n - t_i` over the coefficient stratum, for `i ∈ K`.
Source: ILO IX, Proposition 2.1 proof, p.133, full root algebra before invariants
(blueprint: lem-sfb-transverse-local-root-family-regular). -/
noncomputable def transverseRootRelationIdeal {R : Type u} [CommRing R] {I : Type v}
    (t : I → R) (n : ℕ) (J K : Finset I) :
    Ideal (MvPolynomial K (transverseRootCoefficientRing t J)) :=
  Ideal.span (Set.range (fun i : K ↦
    (MvPolynomial.X i : MvPolynomial K (transverseRootCoefficientRing t J)) ^ n -
      MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t i))))

/-- The literal partial-root quotient `B_{J,K}`, with its usual quotient algebra structure.
Source: ILO IX, Proposition 2.1 proof, p.133, full root algebra before invariants
(blueprint: lem-sfb-transverse-local-root-family-regular). -/
abbrev transverseRootAlgebra {R : Type u} [CommRing R] {I : Type v}
    (t : I → R) (n : ℕ) (J K : Finset I) :=
  MvPolynomial K (transverseRootCoefficientRing t J) ⧸ transverseRootRelationIdeal t n J K

/-- The actual quotient class of the monomial with exponent vector `a`, each exponent below `n`.
Source: ILO IX, Proposition 2.1 proof, p.133, monic root presentation, expanded by monic
polynomial division (blueprint: lem-sfb-transverse-local-root-family-regular). -/
noncomputable def transverseRootMonomial {R : Type u} [CommRing R] {I : Type v}
    (t : I → R) (n : ℕ) (J K : Finset I) (a : K → Fin n) :
    transverseRootAlgebra t n J K :=
  Ideal.Quotient.mk (transverseRootRelationIdeal t n J K)
    (∏ i : K, (MvPolynomial.X i : MvPolynomial K (transverseRootCoefficientRing t J)) ^
      (a i).val)

section Proof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The same presentation with an arbitrary coefficient ring and variable type.
private abbrev RootQ {A : Type*} [CommRing A] {σ : Type*} (s : σ → A) (n : ℕ) :=
  MvPolynomial σ A ⧸ Ideal.span (Set.range (fun i : σ ↦
    (MvPolynomial.X i : MvPolynomial σ A) ^ n - MvPolynomial.C (s i)))

private noncomputable def rootVar {A : Type*} [CommRing A] {σ : Type*}
    (s : σ → A) (n : ℕ) (i : σ) : RootQ s n :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

private theorem rootVar_pow {A : Type*} [CommRing A] {σ : Type*}
    (s : σ → A) (n : ℕ) (i : σ) :
    rootVar s n i ^ n = algebraMap A (RootQ s n) (s i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (_ ^ n - MvPolynomial.C (s i)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

private noncomputable def rootLift {A B : Type*} [CommRing A] [CommRing B]
    {σ : Type*} (s : σ → A) (n : ℕ) (f : A →+* B) (x : σ → B)
    (hx : ∀ i, x i ^ n = f (s i)) : RootQ s n →+* B :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f x) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.eval₂Hom f x)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.eval₂Hom f x (_ ^ n - MvPolynomial.C (s i)) = 0
    simp [hx])

@[simp] private theorem rootLift_var {A B : Type*} [CommRing A] [CommRing B]
    {σ : Type*} (s : σ → A) (n : ℕ) (f : A →+* B) (x : σ → B)
    (hx : ∀ i, x i ^ n = f (s i)) (i : σ) :
    rootLift s n f x hx (rootVar s n i) = x i := by
  simp [rootLift, rootVar]

@[simp] private theorem rootLift_coeff {A B : Type*} [CommRing A] [CommRing B]
    {σ : Type*} (s : σ → A) (n : ℕ) (f : A →+* B) (x : σ → B)
    (hx : ∀ i, x i ^ n = f (s i)) (a : A) :
    rootLift s n f x hx (algebraMap A (RootQ s n) a) = f a := by
  change rootLift s n f x hx (Ideal.Quotient.mk _ (MvPolynomial.C a)) = f a
  simp [rootLift]

private theorem root_hom_ext {A B : Type*} [CommRing A] [CommRing B]
    {σ : Type*} (s : σ → A) (n : ℕ) (f g : RootQ s n →+* B)
    (hc : ∀ a, f (algebraMap A _ a) = g (algebraMap A _ a))
    (hx : ∀ i, f (rootVar s n i) = g (rootVar s n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · exact hx

private noncomputable def rootLiftAlg {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {σ : Type*} (s : σ → A) (n : ℕ) (x : σ → B)
    (hx : ∀ i, x i ^ n = algebraMap A B (s i)) : RootQ s n →ₐ[A] B :=
  { rootLift s n (algebraMap A B) x hx with commutes' := by simp }

private noncomputable def tensorLift {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {σ : Type*} [Fintype σ] {T : σ → Type*}
    [∀ i, CommRing (T i)] [∀ i, Algebra A (T i)] (g : ∀ i, T i →ₐ[A] B) :
    PiTensorProduct A T →ₐ[A] B :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra A σ B).compLinearMap (fun i ↦ (g i).toLinearMap))
    (by simp) (by intro x y; simp [Finset.prod_mul_distrib])

@[simp] private theorem tensorLift_single {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {σ : Type*} [Fintype σ] [DecidableEq σ] {T : σ → Type*}
    [∀ i, CommRing (T i)] [∀ i, Algebra A (T i)] (g : ∀ i, T i →ₐ[A] B)
    (i : σ) (x : T i) : tensorLift g (PiTensorProduct.singleAlgHom i x) = g i x := by
  simp only [tensorLift, PiTensorProduct.singleAlgHom_apply,
    PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

-- The universal properties identify the simultaneous quotient with the tensor product.
private noncomputable def rootTensorEquiv {A : Type*} [CommRing A]
    {σ : Type*} [Fintype σ] (s : σ → A) (n : ℕ) :
    RootQ s n ≃ₐ[A] PiTensorProduct A
      (fun i ↦ AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - Polynomial.C (s i))) := by
  classical
  let P := fun i ↦ (Polynomial.X : Polynomial A) ^ n - Polynomial.C (s i)
  let T := PiTensorProduct A (fun i ↦ AdjoinRoot (P i))
  let x := fun i ↦ PiTensorProduct.singleAlgHom (R := A) (A := fun i ↦ AdjoinRoot (P i)) i
    (AdjoinRoot.root (P i))
  have hp (i : σ) : AdjoinRoot.root (P i) ^ n = AdjoinRoot.of (P i) (s i) := by
    have h := AdjoinRoot.eval₂_root (P i)
    simpa [P, sub_eq_zero] using h
  have hx (i : σ) : x i ^ n = algebraMap A T (s i) := by
    simp only [x, ← map_pow, hp]
    exact (PiTensorProduct.singleAlgHom i).commutes (s i)
  let f := rootLiftAlg s n x hx
  let g : T →ₐ[A] RootQ s n := tensorLift (fun i ↦
    AdjoinRoot.liftAlgHom (P i) (Algebra.ofId A _) (rootVar s n i)
      (by simpa [P, sub_eq_zero] using rootVar_pow s n i))
  have hg (i : σ) : g (x i) = rootVar s n i := by
    change tensorLift _ (PiTensorProduct.singleAlgHom i _) = _
    rw [tensorLift_single, AdjoinRoot.liftAlgHom_root]
  apply AlgEquiv.ofAlgHom f g
  · apply PiTensorProduct.algHom_ext
    intro i
    apply AlgHom.coe_ringHom_injective
    apply AdjoinRoot.ringHom_ext
    · ext a
      change f (g ((PiTensorProduct.singleAlgHom i) (algebraMap A (AdjoinRoot (P i)) a))) =
        (PiTensorProduct.singleAlgHom i) (algebraMap A (AdjoinRoot (P i)) a)
      rw [(PiTensorProduct.singleAlgHom i).commutes, g.commutes, f.commutes]
    · change f (g (x i)) = x i
      rw [hg]
      exact rootLift_var s n (algebraMap A T) x hx i
  · apply AlgHom.coe_ringHom_injective
    apply root_hom_ext s n
    · intro a
      simp
    · intro i
      change g (f (rootVar s n i)) = rootVar s n i
      rw [show f (rootVar s n i) = x i from rootLift_var s n (algebraMap A T) x hx i]
      exact hg i

private theorem root_basis {A : Type*} [CommRing A] [Nontrivial A] {σ : Type*} [Fintype σ]
    (s : σ → A) (n : ℕ) (hn : 0 < n) :
    ∃ b : Module.Basis (σ → Fin n) A (RootQ s n),
      ∀ a, b a = ∏ i, rootVar s n i ^ (a i).val := by
  classical
  let P := fun i ↦ (Polynomial.X : Polynomial A) ^ n - Polynomial.C (s i)
  have hm (i : σ) : (P i).Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  have hd (i : σ) : (P i).natDegree = n := Polynomial.natDegree_X_pow_sub_C
  let b := Basis.piTensorProduct (fun i ↦ (AdjoinRoot.powerBasis' (hm i)).basis)
  let e : (∀ i, Fin (P i).natDegree) ≃ (σ → Fin n) :=
    Equiv.piCongrRight (fun i ↦ finCongr (hd i))
  let E := rootTensorEquiv s n
  refine ⟨(b.reindex e).map E.symm.toLinearEquiv, ?_⟩
  intro a
  apply E.injective
  simp only [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    Module.Basis.reindex_apply]
  rw [E.apply_symm_apply]
  change b (e.symm a) = _
  rw [show b (e.symm a) = PiTensorProduct.tprod A
    (fun i ↦ (AdjoinRoot.powerBasis' (hm i)).basis ((e.symm a) i)) from
      Basis.piTensorProduct_apply _ _]
  have hb (i : σ) :
      (AdjoinRoot.powerBasis' (hm i)).basis ((e.symm a) i) =
        AdjoinRoot.root (P i) ^ ((e.symm a) i).val :=
    (AdjoinRoot.powerBasis' (hm i)).basis_eq_pow _
  rw [show (fun i ↦ (AdjoinRoot.powerBasis' (hm i)).basis ((e.symm a) i)) =
    (fun i ↦ AdjoinRoot.root (P i) ^ ((e.symm a) i).val) from funext hb]
  rw [map_prod]
  simp only [map_pow]
  have hx (i : σ) : E (rootVar s n i) =
      PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i)) := by
    simp only [E, rootTensorEquiv, AlgEquiv.ofAlgHom_apply, rootLiftAlg]
    simp only [AlgHom.coe_mk]
    rw [rootLift_var]
  simp only [hx, ← map_pow]
  have he (i : σ) : ((e.symm a) i).val = (a i).val := rfl
  simp only [he]
  simp only [PiTensorProduct.singleAlgHom_apply, ← PiTensorProduct.tprod_prod]
  congr 1
  ext i
  simp

private noncomputable def rootCongr {A B : Type*} [CommRing A] [CommRing B]
    {σ τ : Type*} (s : σ → A) (t : τ → B) (n : ℕ)
    (e : A ≃+* B) (d : σ ≃ τ) (h : ∀ i, e (s i) = t (d i)) :
    RootQ s n ≃+* RootQ t n := by
  let f := rootLift s n ((algebraMap B _).comp e.toRingHom)
    (fun i ↦ rootVar t n (d i)) (by intro i; simp [rootVar_pow, h])
  let g := rootLift t n ((algebraMap A _).comp e.symm.toRingHom)
    (fun i ↦ rootVar s n (d.symm i)) (by
      intro i
      rw [rootVar_pow]
      change algebraMap A _ (s (d.symm i)) = algebraMap A _ (e.symm (t i))
      congr 1
      apply e.injective
      simpa using h (d.symm i))
  apply RingEquiv.ofRingHom f g
  · apply root_hom_ext t n
    · intro a
      change f (g (algebraMap B _ a)) = _
      simp [f, g]
    · intro i
      change f (g (rootVar t n i)) = _
      simp [f, g]
  · apply root_hom_ext s n
    · intro a
      change g (f (algebraMap A _ a)) = _
      simp [f, g]
    · intro i
      change g (f (rootVar s n i)) = _
      simp [f, g]

-- Reducing coefficients imposes exactly one additional scalar relation.
private noncomputable def rootQuotEquiv {A : Type*} [CommRing A] {σ : Type*}
    (s : σ → A) (n : ℕ) (a : A) :
    (RootQ s n ⧸ Ideal.span {algebraMap A (RootQ s n) a}) ≃+*
      RootQ (fun i ↦ Ideal.Quotient.mk (Ideal.span {a}) (s i)) n := by
  let I := Ideal.span ({a} : Set A)
  let Q := RootQ s n
  let H := Ideal.span ({algebraMap A Q a} : Set Q)
  let T := RootQ (fun i ↦ Ideal.Quotient.mk I (s i)) n
  let c : A →+* T := (algebraMap (A ⧸ I) T).comp (Ideal.Quotient.mk I)
  let f0 := rootLift s n c (rootVar _ n) (by intro i; exact rootVar_pow _ _ i)
  have hfa : f0 (algebraMap A Q a) = 0 := by
    rw [rootLift_coeff]
    change c a = 0
    simp [c, I]
  let f := Ideal.Quotient.lift H f0 (by
    change H ≤ RingHom.ker f0
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact hfa)
  let c0 := (Ideal.Quotient.mk H).comp (algebraMap A Q)
  have hc : c0 a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let c1 : A ⧸ I →+* Q ⧸ H := Ideal.Quotient.lift I c0 (by
    change I ≤ RingHom.ker c0
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact hc)
  let g := rootLift (fun i ↦ Ideal.Quotient.mk I (s i)) n c1
    (fun i ↦ Ideal.Quotient.mk H (rootVar s n i)) (by
      intro i
      rw [← map_pow, rootVar_pow]
      rfl)
  apply RingEquiv.ofRingHom f g
  · apply root_hom_ext _ n
    · intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      change f (g (algebraMap (A ⧸ I) T (Ideal.Quotient.mk I b))) = _
      rw [rootLift_coeff]
      change f (Ideal.Quotient.mk H (algebraMap A Q b)) = _
      change f0 (algebraMap A Q b) = _
      exact rootLift_coeff _ _ _ _ _ _
    · intro i
      change f (g (rootVar _ n i)) = _
      rw [show g (rootVar _ n i) = Ideal.Quotient.mk H (rootVar s n i) from
        rootLift_var _ _ _ _ _ _]
      exact rootLift_var s n c (rootVar _ n) (fun i ↦ rootVar_pow _ _ i) i
  · apply Ideal.Quotient.ringHom_ext
    apply root_hom_ext s n
    · intro b
      change g (f0 (algebraMap A Q b)) = Ideal.Quotient.mk H (algebraMap A Q b)
      rw [rootLift_coeff]
      change g (algebraMap (A ⧸ I) T (Ideal.Quotient.mk I b)) = _
      rw [rootLift_coeff]
      rfl
    · intro i
      change g (f0 (rootVar s n i)) = Ideal.Quotient.mk H (rootVar s n i)
      rw [rootLift_var]
      exact rootLift_var _ _ _ _ _ _

-- Separate the new root from the other labelled coordinates.
private noncomputable def rootOptionEquiv {A : Type*} [CommRing A] {σ : Type*}
    (s : Option σ → A) (n : ℕ) :
    RootQ s n ≃+* AdjoinRoot ((Polynomial.X : Polynomial (RootQ (s ∘ some) n)) ^ n -
      Polynomial.C (algebraMap A _ (s none))) := by
  let Q := RootQ (s ∘ some) n
  let P := (Polynomial.X : Polynomial Q) ^ n - Polynomial.C (algebraMap A Q (s none))
  let B := AdjoinRoot P
  let c : A →+* B := (AdjoinRoot.of P).comp (algebraMap A Q)
  let x : Option σ → B := fun i ↦ i.elim (AdjoinRoot.root P)
    (fun j ↦ AdjoinRoot.of P (rootVar (s ∘ some) n j))
  have hp : AdjoinRoot.root P ^ n = AdjoinRoot.of P (algebraMap A Q (s none)) := by
    have h := AdjoinRoot.eval₂_root P
    simpa [P, sub_eq_zero] using h
  have hx (i : Option σ) : x i ^ n = c (s i) := by
    cases i with
    | none => exact hp
    | some i =>
      change AdjoinRoot.of P (rootVar (s ∘ some) n i) ^ n =
        AdjoinRoot.of P (algebraMap A Q (s (some i)))
      rw [← map_pow, rootVar_pow]
      rfl
  let f := rootLift s n c x hx
  let c0 : Q →+* RootQ s n := rootLift (s ∘ some) n (algebraMap A _)
    (fun i ↦ rootVar s n (some i)) (by intro i; exact rootVar_pow s n (some i))
  let g := AdjoinRoot.lift (f := P) c0 (rootVar s n none) (by
    change Polynomial.eval₂ c0 (rootVar s n none)
      (Polynomial.X ^ n - Polynomial.C (algebraMap A Q (s none))) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, rootLift_coeff, rootVar_pow, sub_self])
  have hfc (b : Q) : f (c0 b) = AdjoinRoot.of P b := by
    have hh : f.comp c0 = AdjoinRoot.of P := by
      apply root_hom_ext (s ∘ some) n
      · intro a
        change f (c0 (algebraMap A Q a)) = _
        rw [rootLift_coeff, rootLift_coeff]
        rfl
      · intro i
        change f (c0 (rootVar (s ∘ some) n i)) = _
        rw [rootLift_var, rootLift_var]
        rfl
    exact DFunLike.congr_fun hh b
  apply RingEquiv.ofRingHom f g
  · apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro b
      change f (g (AdjoinRoot.of P b)) = _
      rw [AdjoinRoot.lift_of, hfc]
      rfl
    · change f (g (AdjoinRoot.root P)) = _
      rw [AdjoinRoot.lift_root, rootLift_var]
      rfl
  · apply root_hom_ext s n
    · intro a
      change g (f (algebraMap A _ a)) = _
      rw [rootLift_coeff]
      change g (AdjoinRoot.of P (algebraMap A Q a)) = _
      rw [AdjoinRoot.lift_of, rootLift_coeff]
      rfl
    · intro i
      change g (f (rootVar s n i)) = _
      rw [rootLift_var]
      cases i with
      | none => exact AdjoinRoot.lift_root _
      | some i =>
        change g (AdjoinRoot.of P (rootVar (s ∘ some) n i)) = _
        rw [AdjoinRoot.lift_of, rootLift_var]
        rfl

private noncomputable def rootEmptyEquiv {A : Type*} [CommRing A] {σ : Type*}
    [IsEmpty σ] (s : σ → A) (n : ℕ) : RootQ s n ≃+* A := by
  let f := rootLift s n (RingHom.id A) (fun i ↦ isEmptyElim i)
    (fun i ↦ isEmptyElim i)
  apply RingEquiv.ofRingHom f (algebraMap A _)
  · ext a
    exact rootLift_coeff s n (RingHom.id A) (fun i ↦ isEmptyElim i)
      (fun i ↦ isEmptyElim i) a
  · apply root_hom_ext s n
    · intro a
      change algebraMap A _ (f (algebraMap A _ a)) = _
      rw [rootLift_coeff]
      rfl
    · exact fun i ↦ isEmptyElim i

-- Apply the local argument of Stacks 07PF directly in the localized polynomial ring.
private theorem root_regular_off {A : Type*} [CommRing A] [IsRegularRing A]
    (a : A) (n : ℕ) (hu : IsUnit (n : A))
    (q : Ideal (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - Polynomial.C a)))
    [q.IsPrime]
    (hx : AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ n - Polynomial.C a) ∉ q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  let P := (Polynomial.X : Polynomial A) ^ n - Polynomial.C a
  let B := AdjoinRoot P
  let I := Ideal.span ({P} : Set (Polynomial A))
  let p := q.comap (AdjoinRoot.mk P)
  have hp : p.IsPrime := Ideal.comap_isPrime _ q
  let L := Localization.AtPrime p
  let c := algebraMap (Polynomial A) L
  have hcP : c P ∈ IsLocalRing.maximalIdeal L := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff L p P).mpr
    change AdjoinRoot.mk P P ∈ q
    rw [AdjoinRoot.mk_self]
    exact q.zero_mem
  have hcx : IsUnit (c Polynomial.X) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff L p Polynomial.X).mpr
    exact hx
  let D : Derivation ℤ (Polynomial A) (Polynomial A) :=
    Polynomial.derivative'.restrictScalars ℤ
  obtain ⟨Dl, hDl, -, -⟩ := (D.exists_completion_and_unique_localization _).2 p.primeCompl
  have hDP : IsUnit (Dl (c P)) := by
    rw [hDl]
    change IsUnit (c (Polynomial.derivative P))
    have hder : Polynomial.derivative P = (n : Polynomial A) * Polynomial.X ^ (n - 1) := by
      simp [P, Polynomial.derivative_X_pow]
    rw [hder, map_mul, map_pow]
    exact ((hu.map Polynomial.C).map c).mul (hcx.pow _)
  have hcP2 : c P ∉ IsLocalRing.maximalIdeal L ^ 2 := by
    intro h
    rw [pow_two] at h
    have hd : Dl (c P) ∈ IsLocalRing.maximalIdeal L := by
      refine Submodule.mul_induction_on h ?_ ?_
      · intro x hx y hy
        rw [Dl.leibniz]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_right _ _ hy)
      · intro x y hx hy
        rw [map_add]
        exact Ideal.add_mem _ hx hy
    exact (IsLocalRing.mem_maximalIdeal _).mp hd hDP
  obtain ⟨hlocal, hregular, -⟩ := IsRegularLocalRing.quotient_span_singleton hcP hcP2
  have hm : I.map c = Ideal.span {c P} := by rw [Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing (L ⧸ I.map c) := by rw [hm]; infer_instance
  have hcompl : Algebra.algebraMapSubmonoid (Polynomial A ⧸ I) p.primeCompl =
      q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q
  let : Algebra B (L ⧸ I.map c) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsLocalization q.primeCompl (L ⧸ I.map c) := by
    rw [← hcompl]
    exact IsLocalization.of_surjective p.primeCompl L (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (I.map c))
      Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker])
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (L ⧸ I.map c)
      (Localization.AtPrime q)).toRingEquiv

private noncomputable def coeffInsertEquiv {R : Type*} [CommRing R] {I : Type*}
    [DecidableEq I] (t : I → R) (J : Finset I) (a : I) :
    (transverseRootCoefficientRing t J ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t a)}) ≃+*
      transverseRootCoefficientRing t (insert a J) := by
  let H := Ideal.span (t '' (J : Set I))
  let F := Ideal.span ({t a} : Set R)
  have hmap : F.map (Ideal.Quotient.mk H) =
      Ideal.span {Ideal.Quotient.mk H (t a)} := by
    rw [Ideal.map_span, Set.image_singleton]
  have heq : H ⊔ F = Ideal.span (t '' (↑(insert a J) : Set I)) := by
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, sup_comm]
  exact (Ideal.quotEquivOfEq hmap.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup H F).trans (Ideal.quotEquivOfEq heq))

private theorem coeffInsertEquiv_mk {R : Type*} [CommRing R] {I : Type*}
    [DecidableEq I] (t : I → R) (J : Finset I) (a : I) (r : R) :
    coeffInsertEquiv t J a (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ r := by
  simp only [coeffInsertEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rw [show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r) =
    DoubleQuot.quotQuotMk _ _ r from rfl,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

private theorem coeff_nonzero {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {I : Type*} (t : I → R)
    (hs : ∀ J : Finset I, (∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R) →
      IsRegularLocalRing (transverseRootCoefficientRing t J) ∧
        ringKrullDim (transverseRootCoefficientRing t J) + (J.card : WithBot ℕ∞) =
          ringKrullDim R)
    (J : Finset I) (hJ : ∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R)
    (a : I) (ha : a ∉ J) (ham : t a ∈ IsLocalRing.maximalIdeal R) :
    Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t a) ≠ 0 := by
  classical
  intro hz
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have heq : Ideal.span (t '' (↑(insert a J) : Set I)) =
      Ideal.span (t '' (J : Set I)) := by
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert,
      sup_eq_right.mpr (Ideal.span_le.mpr (by rintro _ rfl; exact hmem))]
  have hi : ∀ j ∈ insert a J, t j ∈ IsLocalRing.maximalIdeal R := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ham
    · exact hJ j hj
  have hdim := (hs (insert a J) hi).2
  have hdimJ := (hs J hJ).2
  have : IsRegularLocalRing (transverseRootCoefficientRing t J) := (hs J hJ).1
  change ringKrullDim (R ⧸ Ideal.span (t '' (↑(insert a J) : Set I))) + _ = _ at hdim
  rw [heq, Finset.card_insert_of_notMem ha] at hdim
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := transverseRootCoefficientRing t J),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)] at hdimJ
  change ringKrullDim (transverseRootCoefficientRing t J) + _ = _ at hdim
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := transverseRootCoefficientRing t J),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)] at hdim
  norm_cast at hdim hdimJ
  omega

-- Generalizing over J makes reduction by the next parameter available to the induction.
private theorem family_regular
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (I : Type v) [Finite I] (t : I → R)
    (hs : ∀ J : Finset I, (∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R) →
      IsRegularLocalRing (transverseRootCoefficientRing t J) ∧
        ringKrullDim (transverseRootCoefficientRing t J) + (J.card : WithBot ℕ∞) =
          ringKrullDim R)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R))
    (K : Finset I) : ∀ (J : Finset I),
      (∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R) → Disjoint J K →
      IsRegularRing (transverseRootAlgebra t n J K) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    intro J hJ _
    have : IsRegularLocalRing (transverseRootCoefficientRing t J) := (hs J hJ).1
    have : IsRegularRing (transverseRootCoefficientRing t J) :=
      (IsRegularLocalRing.localization_at_prime_and_isRegularRing
        (IsLocalRing.maximalIdeal _)).2
    exact IsRegularRing.of_ringEquiv (rootEmptyEquiv _ n).symm
  | @insert a K ha ih =>
    intro J hJ hdis
    let C := transverseRootCoefficientRing t J
    let c := Ideal.Quotient.mk (Ideal.span (t '' (J : Set I)))
    let s : K → C := fun i ↦ c (t i)
    let A := RootQ s n
    let f := algebraMap C A (c (t a))
    let P := (Polynomial.X : Polynomial A) ^ n - Polynomial.C f
    let B := AdjoinRoot P
    have hdisK : Disjoint J K := Finset.disjoint_of_subset_right
      (Finset.subset_insert a K) hdis
    have hnotJ : a ∉ J := by
      intro h
      exact Finset.disjoint_left.mp hdis h (Finset.mem_insert_self _ _)
    have hC : IsRegularLocalRing C := (hs J hJ).1
    have hA : IsRegularRing A := ih J hJ hdisK
    obtain ⟨b, _⟩ := root_basis s n hn
    have : Module.Free C A := Module.Free.of_basis b
    have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
    have : Module.Finite A B := hmonic.finite_adjoinRoot
    have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    let d := Finset.subtypeInsertEquivOption ha
    let z : Option K → C := fun i ↦ i.elim (c (t a)) s
    have hd (i : (insert a K : Finset I)) : c (t i) = z (d i) := by
      rcases i with ⟨i, hi⟩
      by_cases h : i = a
      · subst i
        simp [d, Finset.subtypeInsertEquivOption, z]
      · simp [d, Finset.subtypeInsertEquivOption, z, s, h]
    let E : transverseRootAlgebra t n J (insert a K) ≃+* B :=
      (rootCongr (fun i : (insert a K : Finset I) ↦ c (t i)) z n (RingEquiv.refl C) d hd).trans
        (rootOptionEquiv z n)
    have hB : IsRegularRing B := by
      apply isRegularRing_iff.mpr
      intro q hq
      by_cases hx : AdjoinRoot.root P ∈ q
      · have ham : t a ∈ IsLocalRing.maximalIdeal R := by
          by_contra h
          have hunit : IsUnit (t a) := not_not.mp ((IsLocalRing.mem_maximalIdeal _).not.mp h)
          have hfunit : IsUnit (AdjoinRoot.of P f) :=
            ((hunit.map c).map (algebraMap C A)).map (AdjoinRoot.of P)
          have hp : AdjoinRoot.root P ^ n = AdjoinRoot.of P f := by
            have hp := AdjoinRoot.eval₂_root P
            simpa [P, sub_eq_zero] using hp
          exact Ideal.notMem_of_isUnit q hfunit
            (hp ▸ q.pow_mem_of_mem hx n hn)
        have hJa : ∀ j ∈ insert a J, t j ∈ IsLocalRing.maximalIdeal R := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ham
          · exact hJ j hj
        have hdisJa : Disjoint (insert a J) K := by
          rw [Finset.disjoint_insert_left]
          exact ⟨ha, hdisK⟩
        have hAQ : IsRegularRing (transverseRootAlgebra t n (insert a J) K) :=
          ih (insert a J) hJa hdisJa
        let e := coeffInsertEquiv t J a
        let Q := C ⧸ Ideal.span {c (t a)}
        let sQ : K → Q := fun i ↦ Ideal.Quotient.mk _ (s i)
        let s' : K → transverseRootCoefficientRing t (insert a J) :=
          fun i ↦ Ideal.Quotient.mk _ (t i)
        have he (i : K) : e (sQ i) = s' i := coeffInsertEquiv_mk t J a (t i)
        let EQ := (rootQuotEquiv s n (c (t a))).trans
          (rootCongr sQ s' n e (Equiv.refl K) he)
        have : IsRegularRing (RootQ s' n) := hAQ
        have : IsRegularRing (A ⧸ Ideal.span {f}) :=
          IsRegularRing.of_ringEquiv EQ.symm
        have : IsDomain C := IsRegularLocalRing.isDomain C
        have hcnz : c (t a) ≠ 0 := coeff_nonzero t hs J hJ a hnotJ ham
        have hcreg : IsSMulRegular C (c (t a)) := by
          apply IsSMulRegular.of_right_eq_zero_of_smul
          intro x hx
          exact (mul_eq_zero.mp hx).resolve_left hcnz
        have hfreg : IsSMulRegular A f := hcreg.of_flat
        exact AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem A f hfreg n hn q hx
      · exact root_regular_off f n (hu.map (algebraMap R A)) q hx
    exact IsRegularRing.of_ringEquiv E.symm

/-- Every allowed partial root algebra over every transverse coefficient stratum is regular
Noetherian and has the specified finite monomial basis over that stratum. Membership in `S`
is written as membership of the parameter in the maximal ideal, and `Disjoint J K` means
`K ⊆ I ∖ J`. The basis has finite index type `K → Fin n`, so includes finite freeness.

Source: ILO IX, Proposition 2.1 proof, p.133; Stacks Tags 00NU and 07PF.
(blueprint: lem-sfb-transverse-local-root-family-regular).

Proof:
1. For fixed J, induct on card K and use `lem-weil-pbc-monic-quotient-free` on
   A[T]/(T^n-t_a). Its degree-below-n expansion, followed by the induction basis
   for each coefficient, gives precisely the monomials indexed by K → Fin n.
   For K empty the single monomial is 1. The algebras are module-finite, hence
   Noetherian by `lem-weil-pbc-finite-algebra-noetherian`.
2. For a in S minus J, subtract the dimension equalities for J and J union {a}.
   Both dimensions are finite by `lem-weil-pbc-noetherian-local-finite-krull-dimension`.
   Thus dim R_(J+a) + 1 = dim R_J, so the image of t_a is nonzero.
   By `lem-sc-regular-local-domain`, R_J is a domain and t_a acts injectively.
3. Prove regularity simultaneously over J by strong induction on card K. The empty
   case uses `lem-weil-pbc-regular-local-localization`. For K = L union {a},
   put A = B_(J,L), f = t_a and B = A[T]/(T^n-f). Fix a prime q of B and root x.
4. If x belongs to q, then a belongs to S: otherwise t_a, and therefore x^n, is a unit.
   Multiplication by f is injective on A coefficientwise in its free basis.
   Reducing coefficients identifies A/(f) with B_(J+a,L): the forward and reverse
   maps fix the coefficients modulo t_a and every remaining variable. The pair is
   allowed, so the simultaneous induction makes A/(f) regular.
5. Apply `lem-sbc-root-algebra-regular-at-root` to A, f, n and q to obtain regular
   locality of B_q. No assertion that the root algebra itself is a domain is needed.
6. If x does not belong to q, then f = x^n does not belong to q. By
   `lem-weil-pbc-localization-of-regular-ring`, C = A[1/f] is regular, and C[T] is
   regular by `lem-trf-polynomial-ring-regular-base`. In E = C[T]/(T^n-f), T has
   inverse f^(-1)T^(n-1). As n is a unit, the derivative nT^(n-1) is a unit,
   including n = 1. Apply `lem-weil-pbc-hypersurface-derivation-regular`.
   The presentations identify E with B[1/f] by maps fixing coefficients and T.
7. Since f is outside q, localizing B[1/f] at the induced prime is B_q: both
   localizations invert exactly B minus q. Thus B_q is regular local in both cases.
   Together with step 1 this gives `IsRegularRing` and the claimed basis for every
   allowed pair. Empty I, empty K, and J = S are all included.
-/
theorem isRegularRing_transverseLocalRootFamily
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (I : Type v) [Finite I] (t : I → R)
    (hstrata : ∀ J : Finset I, (∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R) →
      IsRegularLocalRing (transverseRootCoefficientRing t J) ∧
        ringKrullDim (transverseRootCoefficientRing t J) + (J.card : WithBot ℕ∞) =
          ringKrullDim R)
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (J K : Finset I) (hJ : ∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R)
    (hK : Disjoint J K) :
    IsRegularRing (transverseRootAlgebra t n J K) ∧
      ∃ b : Module.Basis (K → Fin n) (transverseRootCoefficientRing t J)
          (transverseRootAlgebra t n J K),
        ∀ a : K → Fin n, b a = transverseRootMonomial t n J K a := by
  classical
  have hC : IsRegularLocalRing (transverseRootCoefficientRing t J) := (hstrata J hJ).1
  refine ⟨family_regular R I t hstrata n hn hnunit K J hJ hK, ?_⟩
  obtain ⟨b, hb⟩ := root_basis
    (fun i : K ↦ Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t i)) n hn
  refine ⟨b, ?_⟩
  intro a
  change b a = Ideal.Quotient.mk _ _
  rw [hb]
  exact (map_prod (Ideal.Quotient.mk (transverseRootRelationIdeal t n J K))
    (fun i : K ↦ MvPolynomial.X i ^ (a i).val) Finset.univ).symm

end Proof

end RingTheory
