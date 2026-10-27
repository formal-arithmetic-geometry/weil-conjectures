/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.SNCFiniteRootFaceRegular
import Sheaf.AlgebraicGeometry.SNCBranchEquationNonzerodivisor
import Sheaf.RingTheory.HenselianParameterRootRegularity
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# The regular SNC root-stage system and affine base change

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Stacks Tag 0BIA and Tags 00DD, 00DK, 01I4, 01YW, 092H.
(blueprint: lem-sfb-snc-root-stage-system).

The finite and full root quotients are the existing `sncRootLevel` and `tameRootAlgebra`.
The auxiliary abbreviations name exactly the partial localizations and coordinate
closed subschemes introduced in the node. All asserted maps are fixed on generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.ProEtale

/-- The ring C_n, inverting the original parameters indexed by J.
Source: ILO IX 2.1, partial puncture (blueprint: lem-sfb-snc-root-stage-system). -/
abbrev sncStageLocalization {B : Type u} [CommRing B] {r : ℕ}
    (t : Fin r → B) (J : Finset (Fin r)) (n : ℕ) :=
  Localization.Away (algebraMap B (sncRootLevel t n) (∏ b ∈ J, t b))

/-- The specified coordinate x_(a,n) in C_n.
Source: ILO IX 2.1, coordinate divisor (blueprint: lem-sfb-snc-root-stage-system). -/
def sncLocalizedRoot {B : Type u} [CommRing B] {r : ℕ}
    (t : Fin r → B) (J : Finset (Fin r)) (n : ℕ) (a : Fin r) :
    sncStageLocalization t J n :=
  algebraMap (sncRootLevel t n) _ (sncRootCoordinate t n a)

/-- The actual compatible-root algebra with u_J inverted; the theorem states its
localized colimit universal property, not a choice of an unspecified colimit ring.
Source: ILO IX 2.1 and Stacks 01YW (blueprint: lem-sfb-snc-root-stage-system). -/
abbrev sncLimitLocalization (p : ℕ) {B : Type u} [CommRing B] {r : ℕ}
    (t : Fin r → B) (J : Finset (Fin r)) :=
  Localization.Away (algebraMap B (tameRootAlgebra p t) (∏ b ∈ J, t b))

/-- The coordinate ideal sheaf defining D_n on Spec C_n, using the existing
ideal-of-global-sections construction and the canonical Gamma-Spec identification.
Source: ILO IX 2.1 and Stacks Cartier ideals
(blueprint: lem-sfb-snc-root-stage-system). -/
def sncStageCoordinateIdeal {B : Type u} [CommRing B] {r : ℕ}
    (t : Fin r → B) (J : Finset (Fin r)) (n : ℕ) (a : Fin r) :
    (Spec (.of (sncStageLocalization t J n))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span
    {(Scheme.ΓSpecIso (.of (sncStageLocalization t J n))).inv (sncLocalizedRoot t J n a)})

-- Present the existing coordinate API in the SNC notation for rewriting.
private theorem rootCoordinate_pow {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :
    sncRootCoordinate t n i ^ n = algebraMap R _ (t i) :=
  Algebra.rootCoordinate_pow t n i

private theorem rootHom_ext {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S]
    (f g : sncRootLevel t n →+* S)
    (hc : ∀ a : R, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hx : ∀ i, f (sncRootCoordinate t n i) = g (sncRootCoordinate t n i)) :
    f = g :=
  Algebra.rootHom_ext t f g hc hx

@[irreducible] private def rootEvalAlg {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] [Algebra R S]
    (x : Fin r → S) (hx : ∀ i, x i ^ n = algebraMap R S (t i)) :
    sncRootLevel t n →ₐ[R] S where
  __ := Algebra.rootEval t (algebraMap R S) x hx
  commutes' := Algebra.rootEval_scalar t (algebraMap R S) x hx

private theorem rootAlgHom_ext {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] [Algebra R S]
    (f g : sncRootLevel t n →ₐ[R] S)
    (hx : ∀ i, f (sncRootCoordinate t n i) = g (sncRootCoordinate t n i)) :
    f = g := by
  apply AlgHom.coe_ringHom_injective
  exact rootHom_ext t f.toRingHom g.toRingHom (fun a ↦ by simp) hx

@[irreducible] private def rootTransition {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)
    (n m : ℕ) (h : n ∣ m) : sncRootLevel t n →ₐ[R] sncRootLevel t m :=
  rootEvalAlg t (fun i ↦ sncRootCoordinate t m i ^ (m / n)) (fun i ↦ by
    rw [← pow_mul, Nat.div_mul_cancel h, rootCoordinate_pow])

private theorem rootTransition_coordinate {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : ℕ) (h : n ∣ m) (i : Fin r) :
    rootTransition t n m h (sncRootCoordinate t n i) =
      sncRootCoordinate t m i ^ (m / n) := by
  unfold rootTransition rootEvalAlg
  exact Algebra.rootEval_coordinate t (algebraMap R _) _
    (fun j ↦ by rw [← pow_mul, Nat.div_mul_cancel h, rootCoordinate_pow]) i

private theorem rootTransition_id {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    rootTransition t n n (dvd_refl n) = AlgHom.id R _ := by
  apply rootAlgHom_ext t
  intro i
  simp [rootTransition_coordinate, Nat.div_self hn]

private theorem rootTransition_comp {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m l : ℕ) (h : n ∣ m) (h' : m ∣ l) :
    (rootTransition t m l h').comp (rootTransition t n m h) =
      rootTransition t n l (h.trans h') := by
  apply rootAlgHom_ext t
  intro i
  simp only [AlgHom.comp_apply, rootTransition_coordinate, map_pow, ← pow_mul]
  congr 1
  rw [← Nat.mul_div_assoc _ h, Nat.div_mul_cancel h']

private theorem fullRoot_pow (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : TameRootOrder p) (i : Fin r) :
    sncFullRootCoordinate p t n i ^ n.val = algebraMap R _ (t i) := by
  apply sub_eq_zero.mp
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inl ⟨i, n, rfl⟩))

private theorem fullRoot_compatible (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : TameRootOrder p) (h : n.val ∣ m.val) (i : Fin r) :
    sncFullRootCoordinate p t m i ^ (m.val / n.val) =
      sncFullRootCoordinate p t n i := by
  apply sub_eq_zero.mp
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Or.inr ⟨i, n, m, h, rfl⟩))

@[irreducible] private def rootInclusion (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : TameRootOrder p) :
    sncRootLevel t n.val →ₐ[R] tameRootAlgebra p t :=
  rootEvalAlg t (sncFullRootCoordinate p t n) (fullRoot_pow p t n)

private theorem rootInclusion_coordinate (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : TameRootOrder p) (i : Fin r) :
    rootInclusion p t n (sncRootCoordinate t n.val i) = sncFullRootCoordinate p t n i := by
  unfold rootInclusion rootEvalAlg
  exact Algebra.rootEval_coordinate t (algebraMap R _) _ (fullRoot_pow p t n) i

private theorem rootInclusion_compatible (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : TameRootOrder p) (h : n.val ∣ m.val) :
    (rootInclusion p t m).comp (rootTransition t n.val m.val h) = rootInclusion p t n := by
  apply rootAlgHom_ext t
  intro i
  simp only [AlgHom.comp_apply, rootTransition_coordinate, map_pow,
    rootInclusion_coordinate]
  exact fullRoot_compatible p t n m h i

private theorem root_iterated {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : n ∣ m) :
    (∃ e : sncRootLevel (sncRootCoordinate t n) (m / n) ≃+* sncRootLevel t m,
      (∀ c, e (algebraMap _ _ c) = rootTransition t n m h c) ∧
      ∀ i, e (sncRootCoordinate (sncRootCoordinate t n) (m / n) i) =
        sncRootCoordinate t m i) ∧
    ∃ b : @Module.Basis (Fin r → Fin (m / n)) (sncRootLevel t n)
        (sncRootLevel t m) _ _
        (@Algebra.toModule _ _ _ _ (rootTransition t n m h).toRingHom.toAlgebra),
      ∀ d, b d = ∏ i, sncRootCoordinate t m i ^ (d i).val := by
  let A := sncRootLevel t n
  let E := sncRootLevel (sncRootCoordinate t n) (m / n)
  let T := rootTransition t n m h
  let F : E →+* sncRootLevel t m :=
    Algebra.rootEval (sncRootCoordinate t n) T.toRingHom (sncRootCoordinate t m)
      (fun i ↦ (rootTransition_coordinate t n m h i).symm)
  have hFc (c : A) : F (algebraMap A E c) = T c := Algebra.rootEval_scalar ..
  have hFx (i : Fin r) :
      F (sncRootCoordinate (sncRootCoordinate t n) (m / n) i) = sncRootCoordinate t m i :=
    Algebra.rootEval_coordinate ..
  let G : sncRootLevel t m →+* E :=
    Algebra.rootEval t ((algebraMap A E).comp (algebraMap R A))
      (sncRootCoordinate (sncRootCoordinate t n) (m / n)) (fun i ↦ by
        calc
          _ = (sncRootCoordinate (sncRootCoordinate t n) (m / n) i ^ (m / n)) ^ n :=
            congrArg (fun q ↦ sncRootCoordinate (sncRootCoordinate t n) (m / n) i ^ q)
              (Nat.div_mul_cancel h).symm |>.trans (pow_mul _ _ _)
          _ = _ := by rw [rootCoordinate_pow, ← map_pow, rootCoordinate_pow]; rfl)
  have hGc (c : R) : G (algebraMap R _ c) =
      algebraMap A E (algebraMap R A c) := Algebra.rootEval_scalar ..
  have hGx (i : Fin r) : G (sncRootCoordinate t m i) =
      sncRootCoordinate (sncRootCoordinate t n) (m / n) i := Algebra.rootEval_coordinate ..
  have hGT : G.comp T.toRingHom = algebraMap A E := by
    apply rootHom_ext t
    · intro c
      change G (T (algebraMap R A c)) = _
      rw [T.commutes, hGc]
    · intro i
      change G (rootTransition t n m h (sncRootCoordinate t n i)) = _
      rw [rootTransition_coordinate, map_pow, hGx, rootCoordinate_pow]
  have hGF : G.comp F = RingHom.id E := by
    apply rootHom_ext (sncRootCoordinate t n)
    · intro c
      change G (F (algebraMap A E c)) = algebraMap A E c
      rw [hFc]
      exact DFunLike.congr_fun hGT c
    · intro i
      change G (F (sncRootCoordinate (sncRootCoordinate t n) (m / n) i)) = _
      rw [hFx, hGx]
      rfl
  have hFG : F.comp G = RingHom.id _ := by
    apply rootHom_ext t
    · intro c
      change F (G (algebraMap R _ c)) = _
      rw [hGc, hFc]
      exact T.commutes c
    · intro i
      simp only [RingHom.comp_apply, hGx, hFx, RingHom.id_apply]
  let e : E ≃+* sncRootLevel t m :=
    { F with
      invFun := G
      left_inv := DFunLike.congr_fun hGF
      right_inv := DFunLike.congr_fun hFG }
  refine ⟨⟨e, hFc, hFx⟩, ?_⟩
  let : Algebra A (sncRootLevel t m) := T.toRingHom.toAlgebra
  let ea : E ≃ₐ[A] sncRootLevel t m := { e with commutes' := hFc }
  obtain ⟨b, hb⟩ := Algebra.root_basis (sncRootCoordinate t n)
    (Nat.div_pos (Nat.le_of_dvd hm h) hn)
  refine ⟨b.map ea.toLinearEquiv, ?_⟩
  intro d
  simp only [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, hb, map_prod, map_pow]
  exact Finset.prod_congr rfl (fun i _ ↦ congrArg (· ^ (d i).val) (hFx i))

@[irreducible] private def localizedMap {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (z : R) :
    Localization.Away (algebraMap R A z) →+* Localization.Away (algebraMap R C z) :=
  IsLocalization.Away.lift (algebraMap R A z) (g := (algebraMap C _).comp f.toRingHom)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (algebraMap R C z))

private theorem localizedMap_apply {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (z : R) (a : A) :
    localizedMap f z (algebraMap A _ a) = algebraMap C _ (f a) := by
  unfold localizedMap
  exact IsLocalization.Away.lift_eq ..

private theorem localizedMap_id {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (z : R) : localizedMap (AlgHom.id R A) z = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A z))
  ext a
  exact localizedMap_apply (AlgHom.id R A) z a

private theorem localizedMap_comp {R A C D : Type u} [CommRing R] [CommRing A]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : C →ₐ[R] D) (z : R) :
    (localizedMap g z).comp (localizedMap f z) = localizedMap (g.comp f) z := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A z))
  ext a
  simp only [RingHom.comp_apply, localizedMap_apply, AlgHom.comp_apply]

private theorem fullHom_ext (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S]
    (f g : tameRootAlgebra p t →+* S)
    (hc : ∀ c : R, f (algebraMap R _ c) = g (algebraMap R _ c))
    (hx : ∀ (n : TameRootOrder p) i,
      f (sncFullRootCoordinate p t n i) = g (sncFullRootCoordinate p t n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hc (fun i ↦ hx i.2 i.1)

private theorem rootInclusion_universal (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (S : Type u) [CommRing S]
    (f : ∀ n : TameRootOrder p, sncRootLevel t n.val →+* S)
    (hc : ∀ n m : TameRootOrder p,
      (f n).comp (algebraMap R _) = (f m).comp (algebraMap R _))
    (hf : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (f m).comp (rootTransition t n.val m.val h).toRingHom = f n) :
    ∃! F : tameRootAlgebra p t →+* S,
      ∀ n, F.comp (rootInclusion p t n).toRingHom = f n := by
  let one : TameRootOrder p := ⟨1, Nat.one_pos, Nat.coprime_one_left p⟩
  let c : R →+* S := (f one).comp (algebraMap R _)
  let x : Fin r × TameRootOrder p → S := fun i ↦ f i.2 (sncRootCoordinate t i.2.val i.1)
  let F : tameRootAlgebra p t →+* S := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom c x) (by
      change Ideal.span (tameRootRelations p t) ≤ RingHom.ker (MvPolynomial.eval₂Hom c x)
      apply Ideal.span_le.mpr
      intro z hz
      rcases hz with ⟨i, n, rfl⟩ | ⟨i, n, m, h, rfl⟩
      · change MvPolynomial.eval₂Hom c x _ = 0
        simp only [map_sub, map_pow, MvPolynomial.eval₂Hom_X',
          MvPolynomial.eval₂Hom_C, sub_eq_zero]
        change f n (sncRootCoordinate t n.val i) ^ n.val = c (t i)
        rw [← map_pow, rootCoordinate_pow]
        exact DFunLike.congr_fun (hc n one) (t i)
      · change MvPolynomial.eval₂Hom c x _ = 0
        simp only [map_sub, map_pow, MvPolynomial.eval₂Hom_X', sub_eq_zero]
        change f m (sncRootCoordinate t m.val i) ^ (m.val / n.val) =
          f n (sncRootCoordinate t n.val i)
        rw [← map_pow, ← rootTransition_coordinate t n.val m.val h]
        exact DFunLike.congr_fun (hf n m h) _)
  have hFc (a : R) : F (algebraMap R _ a) = c a := by
    change MvPolynomial.eval₂Hom c x (MvPolynomial.C a) = c a
    simp
  have hFx (n : TameRootOrder p) (i : Fin r) :
      F (sncFullRootCoordinate p t n i) = f n (sncRootCoordinate t n.val i) := by
    change MvPolynomial.eval₂Hom c x (MvPolynomial.X (i,n)) = _
    simp [x]
  refine ⟨F, ?_, ?_⟩
  · intro n
    apply rootHom_ext t
    · intro a
      change F (rootInclusion p t n (algebraMap R _ a)) = f n (algebraMap R _ a)
      rw [AlgHom.commutes, hFc]
      exact DFunLike.congr_fun (hc one n) a
    · intro i
      change F (rootInclusion p t n (sncRootCoordinate t n.val i)) = _
      rw [rootInclusion_coordinate, hFx]
  · intro G hG
    apply fullHom_ext p t
    · intro a
      have h := DFunLike.congr_fun (hG one) (algebraMap R _ a)
      change G (rootInclusion p t one (algebraMap R _ a)) = _ at h
      rw [AlgHom.commutes] at h
      exact h.trans (hFc a).symm
    · intro n i
      have h := DFunLike.congr_fun (hG n) (sncRootCoordinate t n.val i)
      change G (rootInclusion p t n (sncRootCoordinate t n.val i)) = _ at h
      rw [rootInclusion_coordinate] at h
      exact h.trans (hFx n i).symm

private theorem localizedInclusion_universal (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (z : R) (S : Type u) [CommRing S]
    (f : ∀ n : TameRootOrder p, Localization.Away (algebraMap R (sncRootLevel t n.val) z) →+* S)
    (hf : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (f m).comp (localizedMap (rootTransition t n.val m.val h) z) = f n) :
    ∃! F : Localization.Away (algebraMap R (tameRootAlgebra p t) z) →+* S,
      ∀ n, F.comp (localizedMap (rootInclusion p t n) z) = f n := by
  let one : TameRootOrder p := ⟨1, Nat.one_pos, Nat.coprime_one_left p⟩
  let f' (n : TameRootOrder p) : sncRootLevel t n.val →+* S :=
    (f n).comp (algebraMap _ _)
  have hf' (n m : TameRootOrder p) (h : n.val ∣ m.val) :
      (f' m).comp (rootTransition t n.val m.val h).toRingHom = f' n := by
    apply RingHom.ext
    intro c
    have hh := DFunLike.congr_fun (hf n m h)
      (algebraMap (sncRootLevel t n.val) _ c)
    simpa only [f', RingHom.comp_apply, localizedMap_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using hh
  have hc (n : TameRootOrder p) :
      (f' n).comp (algebraMap R _) = (f' one).comp (algebraMap R _) := by
    ext c
    have h := DFunLike.congr_fun (hf' one n (one_dvd n.val))
      (algebraMap R _ c)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] using h
  obtain ⟨F, hF, huniq⟩ := rootInclusion_universal p t S f'
    (fun n m ↦ (hc n).trans (hc m).symm) hf'
  have hFc (c : R) : F (algebraMap R _ c) = f' one (algebraMap R _ c) := by
    have h := DFunLike.congr_fun (hF one) (algebraMap R _ c)
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] using h
  have hz : IsUnit (F (algebraMap R _ z)) := by
    rw [hFc]
    exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R (sncRootLevel t one.val) z)).map
      (f one)
  let FL : Localization.Away (algebraMap R (tameRootAlgebra p t) z) →+* S :=
    IsLocalization.Away.lift _ hz
  have hFL (n : TameRootOrder p) :
      FL.comp (localizedMap (rootInclusion p t n) z) = f n := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (sncRootLevel t n.val) z))
    apply RingHom.ext
    intro c
    simp only [RingHom.comp_apply, localizedMap_apply]
    rw [show FL (algebraMap _ _ (rootInclusion p t n c)) = F (rootInclusion p t n c) from
      IsLocalization.Away.lift_eq ..]
    exact DFunLike.congr_fun (hF n) c
  refine ⟨FL, hFL, ?_⟩
  intro G hG
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (tameRootAlgebra p t) z))
  have hGF : G.comp (algebraMap _ _) = F := by
    apply huniq
    intro n
    apply RingHom.ext
    intro c
    have h := DFunLike.congr_fun (hG n) (algebraMap (sncRootLevel t n.val) _ c)
    simpa only [f', RingHom.comp_apply, localizedMap_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using h
  exact hGF.trans (IsLocalization.Away.lift_comp _ hz).symm

private theorem localized_basis {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (z : R)
    {ι : Type*} (b : @Module.Basis ι A C _ _
      (@Algebra.toModule _ _ _ _ f.toRingHom.toAlgebra)) :
    ∃ b' : @Module.Basis ι (Localization.Away (algebraMap R A z))
        (Localization.Away (algebraMap R C z)) _ _
        (@Algebra.toModule _ _ _ _ (localizedMap f z).toAlgebra),
      ∀ i, b' i = algebraMap C _ (b i) := by
  let AL := Localization.Away (algebraMap R A z)
  let CL := Localization.Away (algebraMap R C z)
  let : Algebra A C := f.toRingHom.toAlgebra
  let : Algebra AL CL := (localizedMap f z).toAlgebra
  have : IsScalarTower A C CL := inferInstance
  have : IsScalarTower A AL CL := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (localizedMap_apply f z a).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid C
      (Submonoid.powers (algebraMap R A z))) CL := by
    change IsLocalization (Submonoid.map f.toRingHom
      (Submonoid.powers (algebraMap R A z))) CL
    rw [Submonoid.map_powers]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] using
      (inferInstance : IsLocalization (Submonoid.powers (algebraMap R C z)) CL)
  exact ⟨b.localizationLocalization AL (Submonoid.powers (algebraMap R A z)) CL,
    fun i ↦ b.localizationLocalization_apply AL _ CL i⟩

private def specPull {Z : Scheme.{u}} {A : Type u} [CommRing A]
    (f : Z ⟶ Spec (.of A)) : A →+* Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

private theorem specPull_comp {Z : Scheme.{u}} {A C : Type u} [CommRing A] [CommRing C]
    (f : Z ⟶ Spec (.of C)) (g : A →+* C) :
    specPull (f ≫ Spec.map (CommRingCat.ofHom g)) = (specPull f).comp g := by
  change ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ Spec.map (CommRingCat.ofHom g)).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

private def specDesc {Z : Scheme.{u}} {A : Type u} [CommRing A]
    (f : A →+* Γ(Z, ⊤)) : Z ⟶ Spec (.of A) :=
  ΓSpec.adjunction.homEquiv Z (Opposite.op (.of A)) (CommRingCat.ofHom f).op

private theorem specPull_desc {Z : Scheme.{u}} {A : Type u} [CommRing A]
    (f : A →+* Γ(Z, ⊤)) : specPull (specDesc f) = f := by
  exact congrArg CommRingCat.Hom.hom (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom f))

private theorem specPull_injective {Z : Scheme.{u}} {A : Type u} [CommRing A] :
    Function.Injective (specPull (Z := Z) (A := A)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

private theorem localizedSpec_universal (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (z : R) (Z : Scheme.{u})
    (f : ∀ n : TameRootOrder p,
      Z ⟶ Spec (.of (Localization.Away (algebraMap R (sncRootLevel t n.val) z))))
    (hf : ∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      f m ≫ Spec.map (CommRingCat.ofHom (localizedMap (rootTransition t n.val m.val h) z)) =
        f n) :
    ∃! F : Z ⟶ Spec (.of (Localization.Away (algebraMap R (tameRootAlgebra p t) z))),
      ∀ n, F ≫ Spec.map (CommRingCat.ofHom (localizedMap (rootInclusion p t n) z)) = f n := by
  obtain ⟨F, hF, huniq⟩ := localizedInclusion_universal p t z Γ(Z, ⊤)
    (fun n ↦ specPull (f n)) (fun n m h ↦ by
      rw [← specPull_comp, hf n m h])
  refine ⟨specDesc F, ?_, ?_⟩
  · intro n
    apply specPull_injective
    rw [specPull_comp, specPull_desc, hF]
  · intro G hG
    apply specPull_injective
    rw [specPull_desc]
    exact huniq (specPull G) (fun n ↦ by rw [← specPull_comp, hG])

private theorem chart_regular {X Y : Scheme.{u}} (hY : IsRegularScheme Y)
    (v : X ⟶ Y) [Etale v] : IsRegularScheme X := by
  have := hY.1
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian v,
    ⟨isRegularLocalRing_stalk_of_etale v hY.2.isRegularLocalRing_stalk⟩⟩

private theorem spec_regular {A : Type u} [CommRing A] [IsRegularRing A] :
    IsRegularScheme (Spec (.of A)) := by
  refine ⟨inferInstance, ⟨fun x ↦ ?_⟩⟩
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv.symm

private theorem unit_order {p : ℕ} (hp : p.Prime) {k B : Type u}
    [Field k] [CharP k p] [CommRing B] [Algebra k B] (n : TameRootOrder p) :
    IsUnit (n.val : B) := by
  have hn : (n.val : k) ≠ 0 := by
    intro hz
    have : p ∣ n.val := (CharP.cast_eq_zero_iff k p _).mp hz
    exact hp.not_dvd_one (by
      rw [← n.property.2.gcd_eq_one]
      exact Nat.dvd_gcd this (dvd_refl p))
  have hu : IsUnit (n.val : k) := isUnit_iff_ne_zero.mpr hn
  simpa using hu.map (algebraMap k B)

private theorem localized_regular_mul {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (z c : R) (hc : Function.Injective (fun x : A ↦ algebraMap R A c * x)) :
    Function.Injective (fun x : Localization.Away (algebraMap R A z) ↦
      algebraMap R _ c * x) := by
  have hreg : IsSMulRegular A (algebraMap R A c) := hc
  have h := hreg.of_flat (S := Localization.Away (algebraMap R A z))
  simpa only [IsSMulRegular, Algebra.smul_def, ← IsScalarTower.algebraMap_apply] using h

private theorem coordinate_regular_mul {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n) (a : Fin r)
    (hc : Function.Injective (fun x : R ↦ t a * x)) :
    Function.Injective (fun x : sncRootLevel t n ↦ algebraMap R _ (t a) * x) := by
  obtain ⟨b, _⟩ := Algebra.root_basis t hn
  have : Module.Free R (sncRootLevel t n) := Module.Free.of_basis b
  have hreg : IsSMulRegular R (t a) := hc
  exact hreg.of_flat (S := sncRootLevel t n)

private theorem regular_quotient_localization {A S : Type u} [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] (I : Ideal A)
    [IsRegularRing (A ⧸ I)] : IsRegularRing (S ⧸ I.map (algebraMap A S)) := by
  let N := Algebra.algebraMapSubmonoid (A ⧸ I) M
  let Q := S ⧸ I.map (algebraMap A S)
  apply RingTheory.isRegularRing_of_localization (A ⧸ I) Q N (algebraMap (A ⧸ I) Q)
  · exact IsLocalization.map_units Q
  · intro y
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj N y
    obtain ⟨z, hz⟩ := IsLocalization.map_units Q s
    refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
    · rw [← hz]
      exact z.mul_inv
    · calc
        y = (y * algebraMap (A ⧸ I) Q s) * ↑z⁻¹ := by rw [← hz]; simp
        _ = algebraMap (A ⧸ I) Q r * ↑z⁻¹ := by rw [hy]
  · intro r hr
    exact (IsLocalization.map_eq_zero_iff N Q r).mp hr

private theorem regular_subscheme {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [IsRegularRing (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩)] :
    IsRegularScheme I.subscheme := by
  let f := I.subschemeCover.f ⟨⊤, isAffineOpen_top X⟩
  have : IsIso f := isIso_of_isOpenImmersion_of_opensRange_eq_top f (by
    simp only [f, Scheme.IdealSheafData.opensRange_subschemeCover_map,
      Scheme.Hom.preimage_top])
  exact chart_regular (spec_regular (A := Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩))
    (inv f)

private theorem regular_equation_subscheme {A : Type u} [CommRing A] (x : A)
    [IsRegularRing (A ⧸ Ideal.span {x})] :
    IsRegularScheme (Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (.of A)).inv x})).subscheme := by
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  have he : Ideal.span {e x} = (Ideal.span {x}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have : IsRegularRing (Γ(Spec (.of A), ⊤) ⧸ Ideal.span {e x}) :=
    IsRegularRing.of_ringEquiv (Ideal.quotientEquiv _ _ e he)
  have hI : IsRegularRing (Γ(Spec (.of A), ⊤) ⧸
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso (.of A)).inv x})).ideal
        ⟨⊤, isAffineOpen_top _⟩) := by
    rw [Scheme.IdealSheafData.ideal_top_ofIdealTop]
    exact this
  exact regular_subscheme _


/-- Evaluation on a compatible family of roots.
Source: the quotient universal property (blueprint: lem-sfb-snc-root-stage-system). -/
private def sncFullRootLift (p : ℕ) {B Q : Type u} [CommRing B] [CommRing Q] {r : ℕ}
    (t : Fin r → B) (g : B →+* Q) (x : TameRootOrder p → Fin r → Q)
    (hx : ∀ n i, x n i ^ n.val = g (t i))
    (hc : ∀ n m, n.val ∣ m.val → ∀ i, x m i ^ (m.val / n.val) = x n i) :
    tameRootAlgebra p t →+* Q :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom g (fun z ↦ x z.2 z.1)) (by
    change Ideal.span (tameRootRelations p t) ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro _ (⟨i, n, rfl⟩ | ⟨i, n, m, h, rfl⟩)
    · simp [hx]
    · simp [hc n m h])

private theorem sncFullRootLift_coeff (p : ℕ) {B Q : Type u} [CommRing B] [CommRing Q]
    {r : ℕ} (t : Fin r → B) (g : B →+* Q) (x : TameRootOrder p → Fin r → Q)
    (hx : ∀ n i, x n i ^ n.val = g (t i))
    (hc : ∀ n m, n.val ∣ m.val → ∀ i, x m i ^ (m.val / n.val) = x n i) (b : B) :
    sncFullRootLift p t g x hx hc (algebraMap B _ b) = g b := by
  change MvPolynomial.eval₂Hom g _ (MvPolynomial.C b) = _
  simp

private theorem sncFullRootLift_root (p : ℕ) {B Q : Type u} [CommRing B] [CommRing Q]
    {r : ℕ} (t : Fin r → B) (g : B →+* Q) (x : TameRootOrder p → Fin r → Q)
    (hx : ∀ n i, x n i ^ n.val = g (t i))
    (hc : ∀ n m, n.val ∣ m.val → ∀ i, x m i ^ (m.val / n.val) = x n i)
    (n : TameRootOrder p) (i : Fin r) :
    sncFullRootLift p t g x hx hc (sncFullRootCoordinate p t n i) = x n i := by
  change MvPolynomial.eval₂Hom g _ (MvPolynomial.X (i, n)) = _
  simp

private theorem full_ext (p : ℕ) {B Q : Type u} [CommRing B] [CommRing Q]
    {r : ℕ} (t : Fin r → B) (f g : tameRootAlgebra p t →+* Q)
    (hc : ∀ b : B, f (algebraMap B _ b) = g (algebraMap B _ b))
    (hx : ∀ n i, f (sncFullRootCoordinate p t n i) = g (sncFullRootCoordinate p t n i)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · intro i
    exact hx i.2 i.1

/-- Coefficient change on the literal compatible-root quotient, fixing every label.
Source: polynomial evaluation; ILO IX 2.1
(blueprint: lem-sfb-snc-root-stage-system). -/
private def sncFullRootMap (p : ℕ) {B R : Type u} [CommRing B] [CommRing R] {r : ℕ}
    (t : Fin r → B) (f : B →+* R) :
    tameRootAlgebra p t →+* tameRootAlgebra p (fun i ↦ f (t i)) :=
  sncFullRootLift p t ((algebraMap R _).comp f)
    (sncFullRootCoordinate p (fun i ↦ f (t i)))
    (fullRoot_pow p _) (fullRoot_compatible p _)

@[simp] private theorem sncFullRootMap_coeff (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) (b : B) :
    sncFullRootMap p t f (algebraMap B _ b) = algebraMap R _ (f b) :=
  sncFullRootLift_coeff ..

@[simp] private theorem sncFullRootMap_root (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) (n : TameRootOrder p) (i : Fin r) :
    sncFullRootMap p t f (sncFullRootCoordinate p t n i) =
      sncFullRootCoordinate p (fun i ↦ f (t i)) n i := sncFullRootLift_root ..

/-- The full root presentation commutes with every coefficient change.
Source: ILO IX 2.1; Stacks Tag 01I4.
(blueprint: lem-sfb-snc-root-stage-system).

Proof: for maps from the old root algebra and the new coefficient ring agreeing
on the old coefficients, evaluate a new labelled root at the image of the old
labelled root. The power relations hold by agreement on coefficients, and the
compatibility relations hold by applying the old-root map. Quotient evaluation
therefore defines the desired factor. It restricts to the prescribed maps on
coefficients and roots. Every new-root quotient element is a polynomial in those
generators, which proves uniqueness. This includes zero rings and empty tuples.
-/
private theorem snc_full_root_base_change (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) :
    IsPushout (CommRingCat.ofHom (algebraMap B (tameRootAlgebra p t)))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (sncFullRootMap p t f))
      (CommRingCat.ofHom (algebraMap R (tameRootAlgebra p (fun i ↦ f (t i))))) := by
  classical
  have w : CommRingCat.ofHom (algebraMap B (tameRootAlgebra p t)) ≫
      CommRingCat.ofHom (sncFullRootMap p t f) = CommRingCat.ofHom f ≫
      CommRingCat.ofHom (algebraMap R _) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact sncFullRootMap_coeff p t f b
  refine ⟨⟨w⟩, ⟨PushoutCocone.isColimitAux' _ (fun s ↦ ?_)⟩⟩
  have hs (b : B) : s.inl.hom (algebraMap B _ b) = s.inr.hom (f b) :=
    congr($(s.condition).hom b)
  let lift := sncFullRootLift p (fun i ↦ f (t i)) s.inr.hom
    (fun n i ↦ s.inl.hom (sncFullRootCoordinate p t n i))
    (fun n i ↦ by rw [← map_pow, fullRoot_pow, hs])
    (fun n m h i ↦ by rw [← map_pow, fullRoot_compatible p t n m h i])
  refine ⟨CommRingCat.ofHom lift, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply full_ext p t
    · intro b
      change lift (sncFullRootMap p t f (algebraMap B _ b)) = s.inl.hom _
      rw [sncFullRootMap_coeff, sncFullRootLift_coeff, hs]
    · intro n i
      change lift (sncFullRootMap p t f (sncFullRootCoordinate p t n i)) = _
      rw [sncFullRootMap_root, sncFullRootLift_root]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change lift (algebraMap R _ b) = s.inr.hom b
    exact sncFullRootLift_coeff ..
  · intro m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply full_ext p (fun i ↦ f (t i))
    · intro b
      have hh := congr($(hm₂).hom b)
      change m.hom (algebraMap R (tameRootAlgebra p (fun i ↦ f (t i))) b) = s.inr.hom b at hh
      change m.hom (algebraMap R (tameRootAlgebra p (fun i ↦ f (t i))) b) = lift (algebraMap R _ b)
      rw [sncFullRootLift_coeff]
      exact hh
    · intro n i
      have hh := congr($(hm₁).hom (sncFullRootCoordinate p t n i))
      change m.hom (sncFullRootMap p t f (sncFullRootCoordinate p t n i)) = _ at hh
      rw [sncFullRootMap_root] at hh
      change m.hom _ = lift (sncFullRootCoordinate p (fun i ↦ f (t i)) n i)
      rw [sncFullRootLift_root]
      exact hh


private def fullLocalizedMap (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) (J : Finset (Fin r)) :
    sncLimitLocalization p t J →+*
      sncLimitLocalization p (fun i ↦ f (t i)) J :=
  IsLocalization.Away.lift (algebraMap B (tameRootAlgebra p t) (∏ b ∈ J, t b))
    (g := (algebraMap (tameRootAlgebra p (fun i ↦ f (t i)))
      (sncLimitLocalization p (fun i ↦ f (t i)) J)).comp
      (sncFullRootMap p t f)) (by
        simp only [RingHom.comp_apply, sncFullRootMap_coeff, map_prod]
        simpa only [map_prod] using IsLocalization.Away.algebraMap_isUnit
          (S := sncLimitLocalization p (fun i ↦ f (t i)) J)
          (algebraMap R (tameRootAlgebra p (fun i ↦ f (t i))) (∏ b ∈ J, f (t b))))

private theorem fullLocalizedMap_apply (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) (J : Finset (Fin r))
    (x : tameRootAlgebra p t) :
    fullLocalizedMap p t f J (algebraMap _ _ x) =
      algebraMap _ _ (sncFullRootMap p t f x) := IsLocalization.Away.lift_eq ..

private theorem localizedPushout (p : ℕ) {B R : Type u} [CommRing B] [CommRing R]
    {r : ℕ} (t : Fin r → B) (f : B →+* R) (J : Finset (Fin r)) :
    IsPushout (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (fullLocalizedMap p t f J))
      (CommRingCat.ofHom (algebraMap R (sncLimitLocalization p (fun i ↦ f (t i)) J))) := by
  let A := tameRootAlgebra p t
  let D := tameRootAlgebra p (fun i ↦ f (t i))
  let L := sncLimitLocalization p t J
  let M := sncLimitLocalization p (fun i ↦ f (t i)) J
  let s := algebraMap B A (∏ b ∈ J, t b)
  have hden : (Submonoid.powers s).map (sncFullRootMap p t f) =
      Submonoid.powers (algebraMap R D (∏ b ∈ J, f (t b))) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (by
      change sncFullRootMap p t f (algebraMap B _ _) = _
      rw [sncFullRootMap_coeff, map_prod, map_prod])
  have : IsLocalization ((Submonoid.powers s).map (sncFullRootMap p t f)) M := by
    rw [hden]
    infer_instance
  have hl := CommRingCat.isPushout_of_isLocalization (sncFullRootMap p t f)
    (fullLocalizedMap p t f J) (by
      apply RingHom.ext
      exact fullLocalizedMap_apply p t f J) (Submonoid.powers s)
  exact (snc_full_root_base_change p t f).paste_horiz hl.flip

private theorem section_pullback {A D : Type u} [CommRing A] [CommRing D]
    {X : Scheme.{u}} (e : X ⟶ Spec (.of D)) (q : X ⟶ Spec (.of A))
    (f : A →+* D) (h : e ≫ Spec.map (CommRingCat.ofHom f) = q) (x : A) :
    e.appTop ((Scheme.ΓSpecIso (.of D)).inv (f x)) =
      q.appTop ((Scheme.ΓSpecIso (.of A)).inv x) := by
  have hh := congr(((Scheme.ΓSpecIso (.of A)).inv ≫ $(congrArg Scheme.Hom.appTop h)) x)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality] at hh
  exact hh

private theorem productLocalizationOpen {D : Type u} [CommRing D] (x y : D) :
    let M := Localization.Away x
    let N := Localization.Away (x * y)
    ∃ f : M →+* N, (∀ d : D, f (algebraMap D M d) = algebraMap D N d) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) ∧
      Set.range (Spec.map (CommRingCat.ofHom f)) =
        (PrimeSpectrum.basicOpen (algebraMap D M y) : Set (PrimeSpectrum M)) := by
  let M := Localization.Away x
  let N := Localization.Away (x * y)
  let T := Localization.Away (algebraMap D M y)
  have : IsLocalization.Away (x * y) T := inferInstance
  let e : T ≃ₐ[D] N := IsLocalization.algEquiv (Submonoid.powers (x * y)) T N
  let f : M →+* N := e.toRingHom.comp (algebraMap M T)
  let : Algebra M N := f.toAlgebra
  let e' : T ≃ₐ[M] N := { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  have : IsLocalization.Away (algebraMap D M y) N :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap D M y)) e'
  have he : Spec.map (CommRingCat.ofHom f) =
      (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap M T)) := by
    change Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap M T))
    rw [← Spec.map_comp]
    rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · intro d
    change e (algebraMap M T (algebraMap D M d)) = algebraMap D N d
    rw [← IsScalarTower.algebraMap_apply D M T]
    exact e.commutes d
  · rw [he]
    infer_instance
  · exact PrimeSpectrum.localization_away_comap_range N (algebraMap D M y)

set_option backward.isDefEq.respectTransparency false in
/-- Affine base change identifies the localized full root pair with the root pair
of the base-changed parameter tuple, with the displayed section normalization.
Source: ILO IX Proposition 2.1, p.133; Stacks Tags 00DD, 00DK, 01I4, 092H.
(blueprint: lem-sfb-snc-root-stage-system).

Proof: the polynomial quotient presentation commutes with scalar extension: map
coefficients to the new ring and each labelled root to the same labelled root.
Inverse tensor evaluation sends a root to its tensor with one. Quotient relations
and compatibility are preserved on generators, so these maps are inverse.
Localizing commutes with this scalar extension by the universal property of
inverting the common denominator. Taking spectra and the affine pullback formula
gives the normalized isomorphism over the new affine base; its generator formula
also fixes each original parameter. Affineness and weak etaleness of the projection
follow by base change. Pullback of a basic open is the basic open of the pulled-back
section. Finally inverting u_J and t_a is equivalent to inverting u_J*t_a. The
resulting open comparison commutes with inclusion by these localization maps.
No SNC or regularity assumption is needed here; all maps allow the zero ring.
-/
private theorem snc_localized_root_base_change (p : ℕ) {B : Type u} [CommRing B]
    {r : ℕ} (t : Fin r → B) (J : Finset (Fin r)) (a : Fin r) :
        ∀ (R : Type u) [CommRing R] [Algebra B R]
          (u : Spec (.of R) ⟶ Spec (.of B))
          (_hu : u = Spec.map (CommRingCat.ofHom (algebraMap B R)))
          (_hpro : WeaklyEtale u),
          IsAffineHom (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u) ∧
          WeaklyEtale (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u) ∧
          ∃ e : pullback
              (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u ≅
              Spec (.of (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J)),
            e.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J))) =
                pullback.snd _ _ ∧
            (∀ (n : TameRootOrder p) (b : Fin r),
              e.hom.appTop ((Scheme.ΓSpecIso
                  (.of (sncLimitLocalization p (fun i ↦ algebraMap B R (t i)) J))).inv
                  (algebraMap (tameRootAlgebra p (fun i ↦ algebraMap B R (t i))) _
                    (sncFullRootCoordinate p (fun i ↦ algebraMap B R (t i)) n b))) =
                (pullback.fst
                  (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J))))
                  u).appTop ((Scheme.ΓSpecIso (.of (sncLimitLocalization p t J))).inv
                    (algebraMap (tameRootAlgebra p t) _ (sncFullRootCoordinate p t n b)))) ∧
            e.hom.appTop
                ((Scheme.ΓSpecIso
                  (.of (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J))).inv
                  (algebraMap R _ (algebraMap B R (t a)))) =
              (pullback.fst
                (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J))))
                u).appTop ((Scheme.ΓSpecIso (.of (sncLimitLocalization p t J))).inv
                  (algebraMap B _ (t a))) ∧
            ∃ (openMap : sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J →+*
                Localization.Away (algebraMap R
                  (tameRootAlgebra p (fun b ↦ algebraMap B R (t b)))
                  ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a)))),
              (∀ c : tameRootAlgebra p (fun b ↦ algebraMap B R (t b)),
                openMap (algebraMap _ _ c) = algebraMap _ _ c) ∧
              ∃ ew : pullback
                  (Scheme.Opens.ι (X := Spec (.of (sncLimitLocalization p t J)))
                    (PrimeSpectrum.basicOpen
                      (algebraMap B (sncLimitLocalization p t J) (t a))))
                  (pullback.fst
                    (Spec.map (CommRingCat.ofHom
                      (algebraMap B (sncLimitLocalization p t J)))) u) ≅
                  Spec (.of (Localization.Away (algebraMap R
                    (tameRootAlgebra p (fun b ↦ algebraMap B R (t b)))
                    ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a))))),
                ew.hom ≫ Spec.map (CommRingCat.ofHom openMap) =
                  pullback.snd _ _ ≫ e.hom := by
  classical
  intro R _ _ u hu hpro
  subst u
  let : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap B R))) := hpro
  refine ⟨inferInstance, inferInstance, ?_⟩
  let map := fullLocalizedMap p t (algebraMap B R) J
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (localizedPushout p t (algebraMap B R) J)
  let e := hpb.isoPullback.symm
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom map) = pullback.fst _ _ :=
    hpb.isoPullback_inv_fst
  refine ⟨e, hpb.isoPullback_inv_snd, ?_, ?_, ?_⟩
  · intro n b
    have hh := section_pullback e.hom (pullback.fst _ _) map he
      (algebraMap (tameRootAlgebra p t) _ (sncFullRootCoordinate p t n b))
    simpa only [map, fullLocalizedMap_apply, sncFullRootMap_root] using hh
  · have hh := section_pullback e.hom (pullback.fst _ _) map he
      (algebraMap B (sncLimitLocalization p t J) (t a))
    have hm : map (algebraMap B (sncLimitLocalization p t J) (t a)) =
        algebraMap R (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J)
          (algebraMap B R (t a)) := by
      change map (algebraMap (tameRootAlgebra p t) _ (algebraMap B _ (t a))) = _
      rw [fullLocalizedMap_apply, sncFullRootMap_coeff]
      rfl
    rwa [hm] at hh
  · let D := tameRootAlgebra p (fun b ↦ algebraMap B R (t b))
    let x : D := algebraMap R D (∏ b ∈ J, algebraMap B R (t b))
    let y : D := algebraMap R D (algebraMap B R (t a))
    let M := sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J
    let N := Localization.Away (algebraMap R D
      ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a)))
    have hxy : x * y = algebraMap R D
        ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a)) :=
      (map_mul (algebraMap R D) _ _).symm
    have hopen := productLocalizationOpen x y
    rw [hxy] at hopen
    obtain ⟨om, hom, hoi, hor⟩ := hopen
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom om)) := hoi
    let pr := pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J))))
      (Spec.map (CommRingCat.ofHom (algebraMap B R)))
    let U : (Spec (.of (sncLimitLocalization p t J))).Opens :=
      PrimeSpectrum.basicOpen (algebraMap B (sncLimitLocalization p t J) (t a))
    have hm : map (algebraMap B (sncLimitLocalization p t J) (t a)) =
        algebraMap D M y := by
      change map (algebraMap (tameRootAlgebra p t) _ (algebraMap B _ (t a))) = _
      rw [fullLocalizedMap_apply, sncFullRootMap_coeff]
    have hr : Set.range (pullback.snd U.ι pr) =
        Set.range (Spec.map (CommRingCat.ofHom om) ≫ e.inv) := by
      rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
      have hh : (pr ⁻¹ᵁ U : Set _) = e.hom ⁻¹'
          (PrimeSpectrum.basicOpen (algebraMap D M y) : Set (PrimeSpectrum M)) := by
        dsimp only [pr]
        rw [← he]
        change (e.hom ≫ Spec.map (CommRingCat.ofHom map)) ⁻¹' (U : Set _) = _
        change e.hom ⁻¹' (PrimeSpectrum.comap map ⁻¹'
          (PrimeSpectrum.basicOpen (algebraMap B (sncLimitLocalization p t J) (t a)) :
            Set (PrimeSpectrum (sncLimitLocalization p t J)))) = _
        congr 1
        change (PrimeSpectrum.basicOpen (map (algebraMap B _ (t a))) :
          Set (PrimeSpectrum M)) = _
        rw [hm]
      rw [hh, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hor]
      change _ = e.inv '' _
      ext z
      constructor
      · intro hz
        refine ⟨e.hom z, hz, ?_⟩
        change (e.hom ≫ e.inv) z = z
        rw [e.hom_inv_id]
        rfl
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_preimage, Scheme.inv_hom_apply] using hw
    let ew := IsOpenImmersion.isoOfRangeEq (pullback.snd U.ι pr)
      (Spec.map (CommRingCat.ofHom om) ≫ e.inv) hr
    refine ⟨om, hom, ew, ?_⟩
    have hh := IsOpenImmersion.isoOfRangeEq_hom_fac (pullback.snd U.ι pr)
      (Spec.map (CommRingCat.ofHom om) ≫ e.inv) hr
    rw [← cancel_mono e.inv]
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hh

set_option linter.unusedVariables false in
/-- Regular finite root stages, their monomial bases and coordinate Cartier divisors,
and the normalized affine pro-etale base change of the localized inverse-limit pair.
Source: ILO IX Proposition 2.1 proof, printed p.133; Stacks 0BIA, 01YW, 092H.
(blueprint: lem-sfb-snc-root-stage-system).

Proof (the nine steps of the DAG):
1. Etale regularity gives regularity of Spec B from Y. Its affine coordinate ring
   is Noetherian. Since Y is separated of finite type over k, both source and
   target are qcqs and the etale affine chart is quasi-compact, hence of finite type.
2. For n dividing m, eliminate the old variables from the iterated presentation
   y_b^(m/n)=x_(b,n). The inverse homomorphisms fix coefficients and send y_b to
   x_(b,m). The existing generic root_basis theorem of
   HenselianParameterRootRegularity supplies the bases over B and B_n, also for r=0.
3. Localizing these coefficient expansions at u_J preserves their existence and
   uniqueness: a fraction is zero exactly when a power of u_J kills its numerator.
   The argument does not require u_J to be a nonzerodivisor.
4. The prime-to-p order is a unit. Apply lem-sfb-snc-finite-root-face-regular to
   the empty face and the singleton face, then localization-of-regular-ring to
   C_n and C_n/(x_a). Finite polynomial presentations and adjoining 1/u_J give
   finite type over k, hence regular Noetherian affine schemes X_n and D_n.
5. The reduced SNC boundary is Cartier, so its product equation is a nonzerodivisor.
   Each t_a is one as well. Transfer injectivity coefficientwise through the B-basis
   and then to fractions. Since x_a^n=t_a, x_a also acts injectively, giving D_n Cartier.
6. Inverting x_a^n is equivalent to inverting x_a. This identifies the complement
   with W_n. Transitions pull x_(a,n) back to x_(a,m)^(m/n); power multiplication
   gives the identity and composition laws, also after localization.
7. Evaluate the compatible-root quotient on a compatible family of finite-stage
   maps. The order-one stage identifies their coefficient maps. The inverted
   denominator is a unit, so localization gives the unique full-stage map.
   The Gamma-Spec adjunction gives the scheme inverse-limit universal property.
8. For coefficient change, evaluate the new quotient on the images of all old
   labelled roots. Generator extensionality proves the pushout universal property.
   Paste this square with the localization pushout and apply Spec to obtain
   the canonical affine pullback. Weak etaleness is stable under base change.
9. Taking Spec gives the pair isomorphism. Principal opens pull back to the open
   on which the same section is invertible. Inverting u_J and t_a is equivalent
   to inverting u_J*t_a, so the open inclusion and t_a are preserved. Zero rings,
   empty localizations and divisors are permitted. When r=0 only the finite-algebra
   and colimit clauses apply: there is no coordinate a.
-/
theorem snc_root_stage_system
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k))
    (hY : IsRegularScheme Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (B : Type u) [CommRing B] [Algebra k B]
    (v : Spec (.of B) ⟶ Y) [Etale v]
    (hv : v ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (r : ℕ) (t : Fin r → B)
    (H : (Spec (.of B)).IdealSheafData)
    (hH : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (.of B)).inv (∏ b, t b)}))
    (hsnc : IsStrictNormalCrossingsBoundary H)
    (hreduced : ∀ b, _root_.IsReduced (B ⧸ Ideal.span ({t b} : Set B)))
    (hdistinct : Function.Injective
      (fun b : Fin r ↦ PrimeSpectrum.zeroLocus ({t b} : Set B)))
    (hbranches : Set.range (fun b : Fin r ↦ PrimeSpectrum.zeroLocus ({t b} : Set B)) =
      Set.image (Set.image Subtype.val)
        (irreducibleComponents (H.support : Set (Spec (.of B))))) :
    ∃ (transition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
        sncRootLevel t n.val →ₐ[B] sncRootLevel t m.val)
      (inclusion : ∀ n : TameRootOrder p, sncRootLevel t n.val →ₐ[B] tameRootAlgebra p t),
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) (b : Fin r),
      transition n m h (sncRootCoordinate t n.val b) =
        sncRootCoordinate t m.val b ^ (m.val / n.val)) ∧
    (∀ n, transition n n (dvd_refl n.val) = AlgHom.id B _) ∧
    (∀ (n m l : TameRootOrder p) (h : n.val ∣ m.val) (h' : m.val ∣ l.val),
      (transition m l h').comp (transition n m h) = transition n l (h.trans h')) ∧
    (∀ (n : TameRootOrder p) (b : Fin r),
      inclusion n (sncRootCoordinate t n.val b) = sncFullRootCoordinate p t n b) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (inclusion m).comp (transition n m h) = inclusion n) ∧
    (∀ n : TameRootOrder p,
      ∃ b : Module.Basis (Fin r → Fin n.val) B (sncRootLevel t n.val),
        ∀ d, b d = ∏ i, sncRootCoordinate t n.val i ^ (d i).val) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (∃ e : sncRootLevel (sncRootCoordinate t n.val) (m.val / n.val) ≃+*
          sncRootLevel t m.val,
        (∀ c, e (algebraMap _ _ c) = transition n m h c) ∧
        ∀ b, e (sncRootCoordinate (sncRootCoordinate t n.val) (m.val / n.val) b) =
          sncRootCoordinate t m.val b) ∧
      ∃ b : @Module.Basis (Fin r → Fin (m.val / n.val))
          (sncRootLevel t n.val) (sncRootLevel t m.val) _ _
          (@Algebra.toModule _ _ _ _ (transition n m h).toRingHom.toAlgebra),
        ∀ d, b d = ∏ i, sncRootCoordinate t m.val i ^ (d i).val) ∧
    ∀ J : Finset (Fin r),
      ∃ (localizedTransition : ∀ (n m : TameRootOrder p), n.val ∣ m.val →
          sncStageLocalization t J n.val →+* sncStageLocalization t J m.val)
        (localizedInclusion : ∀ n : TameRootOrder p,
          sncStageLocalization t J n.val →+* sncLimitLocalization p t J),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val) (c : sncRootLevel t n.val),
        localizedTransition n m h (algebraMap _ _ c) =
          algebraMap _ _ (transition n m h c)) ∧
      (∀ n, localizedTransition n n (dvd_refl n.val) = RingHom.id _) ∧
      (∀ (n m l : TameRootOrder p) (h : n.val ∣ m.val) (h' : m.val ∣ l.val),
        (localizedTransition m l h').comp (localizedTransition n m h) =
          localizedTransition n l (h.trans h')) ∧
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        ∃ b : @Module.Basis (Fin r → Fin (m.val / n.val))
            (sncStageLocalization t J n.val) (sncStageLocalization t J m.val) _ _
            (@Algebra.toModule _ _ _ _ (localizedTransition n m h).toAlgebra),
          ∀ d, b d = ∏ i, sncLocalizedRoot t J m.val i ^ (d i).val) ∧
      (∀ (n : TameRootOrder p) (c : sncRootLevel t n.val),
        localizedInclusion n (algebraMap _ _ c) = algebraMap _ _ (inclusion n c)) ∧
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        (localizedInclusion m).comp (localizedTransition n m h) = localizedInclusion n) ∧
      (∀ (Q : Type u) [CommRing Q]
          (f : ∀ n : TameRootOrder p, sncStageLocalization t J n.val →+* Q),
        (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
          (f m).comp (localizedTransition n m h) = f n) →
        ∃! fLimit : sncLimitLocalization p t J →+* Q,
          ∀ n, fLimit.comp (localizedInclusion n) = f n) ∧
      (∀ (Z : Scheme.{u})
          (f : ∀ n : TameRootOrder p, Z ⟶ Spec (.of (sncStageLocalization t J n.val))),
        (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
          f m ≫ Spec.map (CommRingCat.ofHom (localizedTransition n m h)) = f n) →
        ∃! fLimit : Z ⟶ Spec (.of (sncLimitLocalization p t J)),
          ∀ n, fLimit ≫ Spec.map (CommRingCat.ofHom (localizedInclusion n)) = f n) ∧
      (∀ n : TameRootOrder p,
        IsRegularScheme (Spec (.of (sncStageLocalization t J n.val))) ∧
        IsNoetherian (Spec (.of (sncStageLocalization t J n.val))) ∧
        LocallyOfFiniteType (Spec.map
          (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val))) ≫ v ≫ g) ∧
        QuasiCompact (Spec.map
          (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val))) ≫ v ≫ g)) ∧
      ∀ (a : Fin r), a ∉ J →
        (∀ n : TameRootOrder p,
          IsRegularScheme (sncStageCoordinateIdeal t J n.val a).subscheme ∧
          IsNoetherian (sncStageCoordinateIdeal t J n.val a).subscheme ∧
          IsAffine (sncStageCoordinateIdeal t J n.val a).subscheme ∧
          LocallyOfFiniteType ((sncStageCoordinateIdeal t J n.val a).subschemeι ≫
            Spec.map (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val))) ≫
              v ≫ g) ∧
          QuasiCompact ((sncStageCoordinateIdeal t J n.val a).subschemeι ≫
            Spec.map (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val))) ≫
              v ≫ g) ∧
          Function.Injective (fun c : sncStageLocalization t J n.val ↦
            algebraMap B _ (t a) * c) ∧
          Function.Injective (fun c : sncStageLocalization t J n.val ↦
            sncLocalizedRoot t J n.val a * c) ∧
          (sncStageCoordinateIdeal t J n.val a).IsInvertible ∧
          ((sncStageCoordinateIdeal t J n.val a).support).compl =
            PrimeSpectrum.basicOpen (algebraMap B (sncStageLocalization t J n.val) (t a)) ∧
          PrimeSpectrum.basicOpen (algebraMap B (sncStageLocalization t J n.val) (t a)) =
            PrimeSpectrum.basicOpen (sncLocalizedRoot t J n.val a)) ∧
        (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
          localizedTransition n m h (sncLocalizedRoot t J n.val a) =
            sncLocalizedRoot t J m.val a ^ (m.val / n.val)) ∧
        ∀ (R : Type u) [CommRing R] [Algebra B R]
          (u : Spec (.of R) ⟶ Spec (.of B))
          (hu : u = Spec.map (CommRingCat.ofHom (algebraMap B R)))
          (hpro : WeaklyEtale u),
          IsAffineHom (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u) ∧
          WeaklyEtale (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u) ∧
          ∃ e : pullback
              (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J)))) u ≅
              Spec (.of (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J)),
            e.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J))) =
                pullback.snd _ _ ∧
            (∀ (n : TameRootOrder p) (b : Fin r),
              e.hom.appTop ((Scheme.ΓSpecIso
                  (.of (sncLimitLocalization p (fun i ↦ algebraMap B R (t i)) J))).inv
                  (algebraMap (tameRootAlgebra p (fun i ↦ algebraMap B R (t i))) _
                    (sncFullRootCoordinate p (fun i ↦ algebraMap B R (t i)) n b))) =
                (pullback.fst
                  (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J))))
                  u).appTop ((Scheme.ΓSpecIso (.of (sncLimitLocalization p t J))).inv
                    (algebraMap (tameRootAlgebra p t) _ (sncFullRootCoordinate p t n b)))) ∧
            e.hom.appTop
                ((Scheme.ΓSpecIso
                  (.of (sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J))).inv
                  (algebraMap R _ (algebraMap B R (t a)))) =
              (pullback.fst
                (Spec.map (CommRingCat.ofHom (algebraMap B (sncLimitLocalization p t J))))
                u).appTop ((Scheme.ΓSpecIso (.of (sncLimitLocalization p t J))).inv
                  (algebraMap B _ (t a))) ∧
            ∃ (openMap : sncLimitLocalization p (fun b ↦ algebraMap B R (t b)) J →+*
                Localization.Away (algebraMap R
                  (tameRootAlgebra p (fun b ↦ algebraMap B R (t b)))
                  ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a)))),
              (∀ c : tameRootAlgebra p (fun b ↦ algebraMap B R (t b)),
                openMap (algebraMap _ _ c) = algebraMap _ _ c) ∧
              ∃ ew : pullback
                  (Scheme.Opens.ι (X := Spec (.of (sncLimitLocalization p t J)))
                    (PrimeSpectrum.basicOpen
                      (algebraMap B (sncLimitLocalization p t J) (t a))))
                  (pullback.fst
                    (Spec.map (CommRingCat.ofHom
                      (algebraMap B (sncLimitLocalization p t J)))) u) ≅
                  Spec (.of (Localization.Away (algebraMap R
                    (tameRootAlgebra p (fun b ↦ algebraMap B R (t b)))
                    ((∏ b ∈ J, algebraMap B R (t b)) * algebraMap B R (t a))))),
                ew.hom ≫ Spec.map (CommRingCat.ofHom openMap) =
                  pullback.snd _ _ ≫ e.hom := by
  refine ⟨fun n m h ↦ rootTransition t n.val m.val h, rootInclusion p t,
    fun n m h b ↦ rootTransition_coordinate t n.val m.val h b,
    fun n ↦ rootTransition_id t n.property.1,
    fun n m l h h' ↦ rootTransition_comp t n.val m.val l.val h h',
    rootInclusion_coordinate p t, rootInclusion_compatible p t,
    fun n ↦ Algebra.root_basis t n.property.1,
    fun n m h ↦ root_iterated t n.val m.val n.property.1 m.property.1 h, ?_⟩
  intro J
  refine ⟨fun n m h ↦ localizedMap (rootTransition t n.val m.val h) (∏ b ∈ J, t b),
    fun n ↦ localizedMap (rootInclusion p t n) (∏ b ∈ J, t b),
    fun n m h c ↦ localizedMap_apply _ _ c, ?_, ?_, ?_,
    fun n c ↦ localizedMap_apply _ _ c, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    rw [rootTransition_id t n.property.1]
    exact localizedMap_id _
  · intro n m l h h'
    rw [localizedMap_comp, rootTransition_comp]
  · intro n m h
    obtain ⟨b, hb⟩ := (root_iterated t n.val m.val n.property.1 m.property.1 h).2
    obtain ⟨b', hb'⟩ := localized_basis (rootTransition t n.val m.val h) (∏ b ∈ J, t b) b
    refine ⟨b', ?_⟩
    intro d
    rw [hb', hb, map_prod]
    simp only [map_pow, sncLocalizedRoot]
  · intro n m h
    rw [localizedMap_comp, rootInclusion_compatible]
  · exact localizedInclusion_universal p t (∏ b ∈ J, t b)
  · exact localizedSpec_universal p t (∏ b ∈ J, t b)
  · intro n
    have hB := chart_regular hY v
    have hroot := isRegularRing_snc_finiteRoot_face B hB r t H hsnc hreduced hdistinct
      hbranches n.val n.property.1 (unit_order (k := k) hp n) ∅
    have : IsRegularRing (sncRootLevel t n.val) := by
      have he : Ideal.map (Ideal.Quotient.mk
          (Ideal.span (Set.range (fun i : Fin r ↦
            MvPolynomial.X i ^ n.val - MvPolynomial.C (t i)))))
          (Ideal.span ((fun j : Fin r ↦ (MvPolynomial.X j : MvPolynomial (Fin r) B)) ''
            (∅ : Set (Fin r)))) = ⊥ := by simp
      rw [he] at hroot
      have : IsRegularRing (sncRootLevel t n.val ⧸ (⊥ : Ideal (sncRootLevel t n.val))) := hroot
      exact IsRegularRing.of_ringEquiv (RingEquiv.quotientBot _)
    have : IsRegularRing (sncStageLocalization t J n.val) := by
      let A := sncRootLevel t n.val
      let C := sncStageLocalization t J n.val
      let M := Submonoid.powers (algebraMap B A (∏ b ∈ J, t b))
      apply RingTheory.isRegularRing_of_localization A C M (algebraMap A C)
      · exact IsLocalization.map_units C
      · intro y
        obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
        obtain ⟨z, hz⟩ := IsLocalization.map_units C s
        refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
        · rw [← hz]
          exact z.mul_inv
        · calc
            y = (y * algebraMap A C s) * ↑z⁻¹ := by rw [← hz]; simp
            _ = algebraMap A C r * ↑z⁻¹ := by rw [hy]
      · intro r hr
        exact (IsLocalization.map_eq_zero_iff M C r).mp hr
    have hregular := spec_regular (A := sncStageLocalization t J n.val)
    have : IsLocallyNoetherian (Spec (.of (sncStageLocalization t J n.val))) := hregular.1
    have : Algebra.FiniteType B (sncRootLevel t n.val) := inferInstance
    have : Algebra.FiniteType B (sncStageLocalization t J n.val) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType B (sncRootLevel t n.val))
        (inferInstance : Algebra.FiniteType (sncRootLevel t n.val) _)
    have : LocallyOfFiniteType (Spec.map
        (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    have : QuasiSeparatedSpace Y :=
      quasiSeparatedSpace_of_quasiSeparated g
    have : QuasiCompact v := quasiCompact_of_compactSpace v
    exact ⟨hregular, inferInstance, inferInstance, inferInstance⟩
  · intro a ha
    refine ⟨?_, ?_, ?_⟩
    · intro n
      have hB := chart_regular hY v
      have hface := isRegularRing_snc_finiteRoot_face B hB r t H hsnc hreduced hdistinct
        hbranches n.val n.property.1 (unit_order (k := k) hp n) {a}
      have hface' : IsRegularRing (sncRootLevel t n.val ⧸
          Ideal.span {sncRootCoordinate t n.val a}) := by
        change IsRegularRing (sncRootLevel t n.val ⧸ _) at hface
        have he : Ideal.map (Ideal.Quotient.mk _)
            (Ideal.span ((fun j : Fin r ↦ (MvPolynomial.X j : MvPolynomial (Fin r) B)) ''
              ({a} : Set (Fin r)))) = Ideal.span {sncRootCoordinate t n.val a} := by
          rw [Set.image_singleton, Ideal.map_span, Set.image_singleton]
          rfl
        rwa [he] at hface
      have hquot : IsRegularRing (sncStageLocalization t J n.val ⧸
          Ideal.span {sncLocalizedRoot t J n.val a}) := by
        have := regular_quotient_localization
          (S := sncStageLocalization t J n.val)
          (Submonoid.powers (algebraMap B (sncRootLevel t n.val) (∏ b ∈ J, t b)))
          (Ideal.span {sncRootCoordinate t n.val a})
        have he : (Ideal.span {sncRootCoordinate t n.val a}).map
            (algebraMap (sncRootLevel t n.val) (sncStageLocalization t J n.val)) =
            Ideal.span {sncLocalizedRoot t J n.val a} := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl
        rwa [he] at this
      have hD := regular_equation_subscheme (sncLocalizedRoot t J n.val a)
      have : IsLocallyNoetherian (sncStageCoordinateIdeal t J n.val a).subscheme := hD.1
      have : IsAffine (sncStageCoordinateIdeal t J n.val a).subscheme :=
        isAffine_of_isAffineHom (sncStageCoordinateIdeal t J n.val a).subschemeι
      have : IsNoetherian (sncStageCoordinateIdeal t J n.val a).subscheme := ⟨⟩
      have ht := localized_regular_mul (∏ b ∈ J, t b) (t a)
        (coordinate_regular_mul t n.val n.property.1 a
          ((sncBranchEquation_mul_injective B hB r t H hsnc hreduced hdistinct hbranches).1 a))
      have hpow : sncLocalizedRoot t J n.val a ^ n.val =
          algebraMap B (sncStageLocalization t J n.val) (t a) := by
        rw [sncLocalizedRoot, ← map_pow, rootCoordinate_pow]
        rfl
      have hx : IsSMulRegular (sncStageLocalization t J n.val) (sncLocalizedRoot t J n.val a) :=
        (IsSMulRegular.pow_iff n.property.1).mp (hpow.symm ▸ ht)
      have heq : PrimeSpectrum.basicOpen
          (algebraMap B (sncStageLocalization t J n.val) (t a)) =
          PrimeSpectrum.basicOpen (sncLocalizedRoot t J n.val a) := by
        rw [← hpow, PrimeSpectrum.basicOpen_pow _ _ n.property.1]
      have : Algebra.FiniteType B (sncStageLocalization t J n.val) :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType B (sncRootLevel t n.val)) inferInstance
      have : LocallyOfFiniteType (Spec.map
          (CommRingCat.ofHom (algebraMap B (sncStageLocalization t J n.val)))) :=
        HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
      have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
      have : QuasiCompact v := quasiCompact_of_compactSpace v
      refine ⟨hD, inferInstance, inferInstance, inferInstance, inferInstance, ht, hx, ?_, ?_, heq⟩
      · apply Scheme.IdealSheafData.IsInvertible.of_isAffine
        rw [sncStageCoordinateIdeal, Scheme.IdealSheafData.ideal_top_ofIdealTop]
        apply Ideal.isRegularPrincipal_span_singleton
        let e := Iso.commRingCatIsoToRingEquiv
          (Scheme.ΓSpecIso (.of (sncStageLocalization t J n.val)))
        apply mem_nonZeroDivisors_of_injective
          (f := (Scheme.ΓSpecIso (.of (sncStageLocalization t J n.val))).hom.hom)
          e.injective
        change ((Scheme.ΓSpecIso (.of (sncStageLocalization t J n.val))).inv ≫
          (Scheme.ΓSpecIso (.of (sncStageLocalization t J n.val))).hom)
          (sncLocalizedRoot t J n.val a) ∈ nonZeroDivisors _
        rw [Iso.inv_hom_id]
        apply isRegular_iff_mem_nonZeroDivisors.mp
        refine ⟨hx, ?_⟩
        intro x y hxy
        apply hx
        exact (mul_comm _ _).trans (hxy.trans (mul_comm _ _))
      · apply TopologicalSpace.Opens.ext
        change ((sncStageCoordinateIdeal t J n.val a).support :
          Set (Spec (.of (sncStageLocalization t J n.val))))ᶜ = _
        have hs : ((sncStageCoordinateIdeal t J n.val a).support :
            Set (Spec (.of (sncStageLocalization t J n.val)))) =
            PrimeSpectrum.zeroLocus ({sncLocalizedRoot t J n.val a} :
              Set (sncStageLocalization t J n.val)) := by
          dsimp only [sncStageCoordinateIdeal]
          rw [Scheme.IdealSheafData.coe_support_ofIdealTop]
          simpa only [Scheme.zeroLocus_span, Set.image_singleton] using
            Spec_zeroLocus_eq_zeroLocus (R := CommRingCat.of (sncStageLocalization t J n.val))
              ({sncLocalizedRoot t J n.val a} : Set (sncStageLocalization t J n.val))
        rw [hs, ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
        exact congrArg SetLike.coe heq.symm
    · intro n m h
      simp only [sncLocalizedRoot, localizedMap_apply, rootTransition_coordinate, map_pow]
    · exact snc_localized_root_base_change p t J a

end AlgebraicGeometry.ProEtale
