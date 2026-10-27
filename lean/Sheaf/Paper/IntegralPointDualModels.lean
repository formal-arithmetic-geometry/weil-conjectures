/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.PointFgCompleteComplexes
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.CategoryTheory.DerivedCategory.PerfectOverDerivedCompleteRing
import Mathlib.Algebra.Category.ModuleCat.Products
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Integral point dual models and canonical reductions

Source: blueprint main-20261015, thm-pod-point-perfectness, Proof Step 2, final paragraph;
Stacks Project, Tags 091R, 091S, 07VI, 0A66 and 0A6A.
(blueprint: lem-sf-integral-point-dual-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CochainComplex

/-- The signed dual complex is the existing module Hom complex into the ring in
 degree zero. Its differential is d(f)=(-1)^(i+1) f d in degree i.
Source: Stacks 07VI and 0A66 (blueprint: lem-sf-integral-point-dual-models). -/
def integralPointSignedDual {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  moduleHomComplex P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    (ModuleCat.of R R))

private def signedDualDegreeEquiv {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (integralPointSignedDual P).X i ≃ₗ[R] Module.Dual R (P.X (-i)) :=
  { (HomComplex.Cochain.toSingleEquiv (K := P) (X := ModuleCat.of R R)
      (neg_add_cancel i)).trans (ModuleCat.homLinearEquiv (S := R)).toAddEquiv with
    map_smul' := by
      intro r f
      ext x
      rfl }

private theorem signedDualDegreeEquiv_d {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (f : (integralPointSignedDual P).X i) :
    signedDualDegreeEquiv P (i + 1) ((integralPointSignedDual P).d i (i + 1) f) =
      (i + 1).negOnePow •
        ((signedDualDegreeEquiv P i f).comp (P.d (-(i + 1)) (-i)).hom) := by
  obtain ⟨g, rfl⟩ := HomComplex.Cochain.toSingleMk_surjective f (-i) (by omega)
  change signedDualDegreeEquiv P (i + 1)
      (HomComplex.δ i (i + 1) (HomComplex.Cochain.toSingleMk g _)) = _
  rw [HomComplex.Cochain.δ_toSingleMk _ _ _ (-(i + 1)) (by omega)]
  rw [map_zsmul_unit]
  congr 1
  change ((HomComplex.Cochain.toSingleEquiv _
    (HomComplex.Cochain.toSingleMk (P.d (-(i + 1)) (-i) ≫ g) _)).hom) = _
  rw [HomComplex.Cochain.toSingleEquiv_toSingleMk]
  change (P.d (-(i + 1)) (-i) ≫ g).hom =
    (HomComplex.Cochain.toSingleEquiv _ (HomComplex.Cochain.toSingleMk g _)).hom.comp _
  rw [HomComplex.Cochain.toSingleEquiv_toSingleMk]
  rfl

private theorem signedDual_bounds {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    (integralPointSignedDual P).IsStrictlyGE (-b) ∧
      (integralPointSignedDual P).IsStrictlyLE (-a) := by
  have hz (i : ℤ) (h : IsZero (P.X (-i))) : IsZero ((integralPointSignedDual P).X i) := by
    have : Subsingleton (P.X (-i)) := ModuleCat.isZero_iff_subsingleton.mp h
    have : Subsingleton (Module.Dual R (P.X (-i))) := inferInstance
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (signedDualDegreeEquiv P i).injective.subsingleton
  constructor
  · rw [isStrictlyGE_iff]
    intro i hi
    exact hz i (P.isZero_of_isStrictlyLE b (-i) (by omega))
  · rw [isStrictlyLE_iff]
    intro i hi
    exact hz i (P.isZero_of_isStrictlyGE a (-i) (by omega))

private theorem signedDual_model {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (hp : ∀ i : ℤ, Module.Projective R (P.X i)) :
    Nonempty (DerivedCategory.Q.obj (integralPointSignedDual P) ≅
      (ihom (DerivedCategory.Q.obj P)).obj (𝟙_ _)) := by
  obtain ⟨_, _, _, _, e, _, _⟩ := projective_hom_evaluation_model R
  refine ⟨e P ⟨b, fun i hi ↦ P.isZero_of_isStrictlyLE b i hi⟩ hp _ ≪≫ ?_⟩
  exact (ihom _).mapIso (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} R))

end CochainComplex

namespace Padic

/-- Positive-level ordinary derived coefficient reduction. Index n denotes exponent n+1.
The functor is the universal K-flat scalar extension, normalized on ordinary tensors.
Source: Stacks 06YY, 0A6A (blueprint: lem-sf-integral-point-dual-models). -/
def integralPointReduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (coefficientExtensionIntegers l E)) ⥤
      DerivedCategory (ModuleCat.{u} (coefficientExtensionRing l E (n + 1))) :=
  ModuleCat.ordinaryDerivedExtendScalars
    (Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)))

/-- The reduction's tensor structure is inherited from the normalized universal pair.
Source: Stacks 06YY, 0A6A (blueprint: lem-sf-integral-point-dual-models). -/
instance integralPointReductionMonoidal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    (integralPointReduction l E n).Monoidal :=
  ModuleCat.ordinaryDerivedExtendScalarsMonoidal _

end Padic

namespace ModuleCat

private def sequenceDifference {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] (f : A) :
    (ℕ → M) →ₗ[A] (ℕ → M) where
  toFun a n := a n - f • a (n + 1)
  map_add' a b := by ext n; simp [smul_add, sub_add_sub_comm]
  map_smul' r a := by
    ext n
    change r • a n - f • (r • a (n + 1)) = r • (a n - f • a (n + 1))
    rw [smul_sub, smul_comm f r]

private theorem difference_of_complete {A : Type u} [CommRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [IsAdicComplete I M]
    (f : A) (hf : f ∈ I) : Function.Bijective (sequenceDifference (M := M) f) := by
  classical
  constructor
  · suffices hz : ∀ a : ℕ → M, sequenceDifference f a = 0 → a = 0 by
      intro a b hab
      exact sub_eq_zero.mp (hz (a - b) (by rw [map_sub, hab, sub_self]))
    intro a ha
    have he (n k : ℕ) : a n = f ^ k • a (n + k) := by
      induction k generalizing n with
      | zero => simp
      | succ k ih =>
        have hn : a n = f • a (n + 1) := sub_eq_zero.mp (congrFun ha n)
        rw [hn, ih (n + 1), ← mul_smul, ← pow_succ']
        congr 2; omega
    ext n
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := M))
    intro k
    apply SModEq.zero.mpr
    rw [he n k]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hf k) Submodule.mem_top
  · intro b
    let S (n k : ℕ) : M := ∑ j ∈ Finset.range k, f ^ j • b (n + j)
    have hc (n : ℕ) : ∀ k l, k ≤ l →
        S n k ≡ S n l [SMOD (I ^ k • ⊤ : Submodule A M)] := by
      intro k l hkl
      rw [SModEq.sub_mem]
      dsimp [S]
      rw [← Nat.add_sub_of_le hkl, Finset.sum_range_add, ← sub_sub, sub_self,
        zero_sub, neg_mem_iff]
      apply Submodule.sum_mem
      intro j hj
      rw [pow_add, mul_smul]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hf k) Submodule.mem_top
    choose a ha using fun n ↦ IsPrecomplete.prec
      (IsAdicComplete.toIsPrecomplete (I := I) (M := M))
      (f := S n) (fun {k l} h ↦ hc n k l h)
    refine ⟨a, ?_⟩
    ext n
    change a n - f • a (n + 1) = b n
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro k
    have hs : S n (k + 1) = b n + f • S (n + 1) k := by
      simp only [S, Finset.sum_range_succ', pow_zero, one_smul, Nat.add_zero,
        Finset.smul_sum, pow_succ', mul_smul]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_left_comm, Nat.add_comm]
    have h1 : S n (k + 1) ≡ a n [SMOD (I ^ k • ⊤ : Submodule A M)] :=
      (ha n (k + 1)).mono (Submodule.pow_smul_top_le I M k.le_succ)
    calc
      a n - f • a (n + 1) ≡ S n (k + 1) - f • S (n + 1) k
          [SMOD (I ^ k • ⊤ : Submodule A M)] := h1.symm.sub ((ha (n + 1) k).smul f).symm
      _ = b n := by rw [hs]; abel

set_option backward.isDefEq.respectTransparency false in
private theorem derivedComplete_of_adic {A : Type u} [CommRing A]
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [IsAdicComplete I M] :
    IsDerivedComplete I (ModuleCat.of A M) := by
  classical
  obtain ⟨hP, hprops⟩ := derivedCategory_countableProducts_and_towerLimit (ModuleCat.{u} A)
  let := hP
  let G := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let K := G.obj (ModuleCat.of A M)
  intro f hf _ T ⟨p, δ, hT⟩
  apply (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hT).mpr
  apply (DerivedCategory.isIso_iff (ModuleCat.{u} A) _).mpr
  intro i
  let F := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let : PreservesLimitsOfShape (Discrete ℕ) F := hprops.2.1 ℕ i
  let d := towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K)
  change IsIso (F.map d)
  by_cases hi : i = 0
  · subst i
    let e : F.obj K ≅ ModuleCat.of A M :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app _
    let E : F.obj (Limits.piObj (fun _ : ℕ ↦ K)) ≅ ModuleCat.of A (ℕ → M) :=
      Limits.PreservesProduct.iso F (fun _ : ℕ ↦ K) ≪≫
        Limits.Pi.mapIso (fun _ : ℕ ↦ e) ≪≫ ModuleCat.piIsoPi (fun _ : ℕ ↦ ModuleCat.of A M)
    have hE (n : ℕ) : E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
        F.map (Limits.Pi.π (fun _ : ℕ ↦ K) n) ≫ e.hom := by
      simp [E, Category.assoc]
    have hnat : F.map (f • 𝟙 K) ≫ e.hom = e.hom ≫ (f • 𝟙 (ModuleCat.of A M)) := by
      have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} A) 0).hom.naturality (f • 𝟙 (ModuleCat.of A M))
      simpa [F, G, K, e, Functor.map_smul] using hn
    have hconj : E.inv ≫ F.map d ≫ E.hom = ModuleCat.ofHom (sequenceDifference f) := by
      apply (cancel_epi E.hom).mp
      simp only [Iso.hom_inv_id_assoc]
      apply ModuleCat.hom_ext
      ext a n
      have hn := congrArg (fun k ↦ k.hom a) (show
          F.map d ≫ E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
            E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) -
              E.hom ≫ ModuleCat.ofHom (LinearMap.proj (n + 1)) ≫
                (f • 𝟙 (ModuleCat.of A M)) by
        rw [hE, ← Category.assoc, ← F.map_comp,
          (towerTransitionEndomorphism_eq_iff _ d).mp rfl n,
          F.map_sub, F.map_comp, Preadditive.sub_comp, Category.assoc, hnat,
          ← hE, ← Category.assoc, ← hE, Category.assoc])
      simpa [sequenceDifference] using hn
    have : IsIso (ModuleCat.ofHom (sequenceDifference (M := M) f)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (difference_of_complete I M f hf)
    have : IsIso (E.inv ≫ F.map d ≫ E.hom) := hconj.symm ▸ this
    have : IsIso (F.map d ≫ E.hom) := IsIso.of_isIso_comp_left E.inv _
    exact IsIso.of_isIso_comp_right _ E.hom
  · have hz : IsZero (F.obj K) := by
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K 0 i hi
      · exact DerivedCategory.isZero_of_isLE K 0 i hi
    have hzero : IsZero (F.obj (Limits.piObj (fun _ : ℕ ↦ K))) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (cancel_mono (Limits.PreservesProduct.iso F (fun _ : ℕ ↦ K)).hom).mp
      apply Pi.hom_ext
      intro n
      exact hz.eq_of_tgt _ _
    exact hzero.isIso hzero _

end ModuleCat

namespace WeilConjectures

/-- Integral perfect duals, their signed models, and their canonical coefficient reductions.
The tensor units are the existing degree-zero regular module complexes. Every positive
exponent occurs uniquely as n+1. The final interval is independent of this n.
Source: blueprint main-20261015, thm-pod-point-perfectness, Proof Step 2, final paragraph;
Stacks 091R, 091S, 07VI, 0A66, 0A6A (blueprint: lem-sf-integral-point-dual-models).

Proof, following the six steps of the node:
1. Put t=ϖ_E. The DVR theorem makes R Noetherian. For f in (t), the nonarchimedean
   geometric series a_n=sum_j f^j b_(n+j) converges in E and lies in R. It is the inverse
   of (a_n) ↦ (a_n-f a_(n+1)); uniqueness follows from |a_n| ≤ |f|^N for every N.
   For f=0 the inverse is the identity.
2. Products of modules are exact, so `lem-weil-derived-limit-existence` computes the
   multiplication tower's Roos arrow on R[0] by this same invertible module map.
   Every Roos triangle therefore has zero first vertex. This is derived completeness.
3. For any bounded finite projective P representing C, apply
   `lem-pod-projective-hom-evaluation-model` with N=R[0]. Its Hom complex represents
   RHom(C,R), and projection to degree -i identifies its degree i with Hom(P^(-i),R).
   Its differential is (-1)^(i+1) precomposition with d_P. The finite projective module
   dual lemma supplies finite projective terms; the support interval reverses.
4. Noetherianity makes the cycles finite; their quotient cohomology modules are finite
   and bounded. By `lem-sf-perfect-over-derived-complete-ring` the perfect dual is
   derived complete. These are exactly the three clauses of `pointFgComplete`.
5. Apply `lem-pc-base-change-rhom-perfect` to R→A_n, C and R[0]. The coefficient
   comparison is transposed derived evaluation followed by the unit comparison,
   precisely `ihomUnitComparison`. The normalized K-flat tensor square identifies
   the ordinary-module presentation with that theorem's ringed-site comparison.
   Hence this canonical arrow is invertible, without flatness of R→A_n.
6. For each n, dualize a finite free model in [a,b] of the reduction of C. Its dual
   basis is finite free in [-b,-a], by the signed Hom computation over A_n.
   Step 5 identifies it with the reduction of C's dual. No compatible bases are needed.
The zero complex, negative or empty intervals, n=1, and arbitrary ramification all
satisfy the same construction. -/
theorem integral_point_dual_models (D : FiniteFieldDatum.{v}) (L : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic L.l) E] [FiniteDimensional (Padic L.l) E] :
    ModuleCat.IsDerivedComplete
        (Ideal.span ({Padic.coefficientExtensionUniformizer L.l E} :
          Set (Padic.coefficientExtensionIntegers L.l E)))
        (ModuleCat.of (Padic.coefficientExtensionIntegers L.l E)
          (Padic.coefficientExtensionIntegers L.l E)) ∧
    ∀ C : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionIntegers L.l E)),
      DerivedCategory.IsPerfectRingComplex C →
      DerivedCategory.pointFgComplete (Padic.coefficientExtensionIntegers L.l E)
          (Ideal.span ({Padic.coefficientExtensionUniformizer L.l E} :
            Set (Padic.coefficientExtensionIntegers L.l E)))
          ((ordinaryModuleDerivedInternalHom _).obj (op C, 𝟙_ _)) ∧
      DerivedCategory.IsPerfectRingComplex
          ((ordinaryModuleDerivedInternalHom _).obj (op C, 𝟙_ _)) ∧
      (∀ (P : CochainComplex (ModuleCat.{u}
          (Padic.coefficientExtensionIntegers L.l E)) ℤ) (a b : ℤ),
        P.IsStrictlyGE a → P.IsStrictlyLE b →
        (∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers L.l E) (P.X i) ∧
          Module.Finite (Padic.coefficientExtensionIntegers L.l E) (P.X i)) →
        Nonempty (DerivedCategory.Q.obj P ≅ C) →
        Nonempty (DerivedCategory.Q.obj (CochainComplex.integralPointSignedDual P) ≅
          (ordinaryModuleDerivedInternalHom _).obj (op C, 𝟙_ _)) ∧
        (∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers L.l E)
            ((CochainComplex.integralPointSignedDual P).X i) ∧
          Module.Finite (Padic.coefficientExtensionIntegers L.l E)
            ((CochainComplex.integralPointSignedDual P).X i)) ∧
        ∃ e : ∀ i : ℤ, ((CochainComplex.integralPointSignedDual P).X i) ≃ₗ[
            Padic.coefficientExtensionIntegers L.l E]
            ((P.X (-i)) →ₗ[Padic.coefficientExtensionIntegers L.l E]
              Padic.coefficientExtensionIntegers L.l E),
          ∀ (i : ℤ) (f : (CochainComplex.integralPointSignedDual P).X i),
            e (i + 1) ((CochainComplex.integralPointSignedDual P).d i (i + 1) f) =
              (i + 1).negOnePow •
                ((e i f).comp (P.d (-(i + 1)) (-i)).hom)) ∧
      (∀ n : ℕ, IsIso (MonoidalClosed.ihomUnitComparison
        (Padic.integralPointReduction L.l E n) C)) ∧
      ∀ a b : ℤ,
        (∀ n : ℕ, ∃ P : CochainComplex (ModuleCat.{u}
            (Padic.coefficientExtensionRing L.l E (n + 1))) ℤ,
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Free (Padic.coefficientExtensionRing L.l E (n + 1)) (P.X i) ∧
            Module.Finite (Padic.coefficientExtensionRing L.l E (n + 1)) (P.X i)) ∧
          Nonempty (DerivedCategory.Q.obj P ≅ (Padic.integralPointReduction L.l E n).obj C)) →
        ∀ n : ℕ, ∃ Q : CochainComplex (ModuleCat.{u}
            (Padic.coefficientExtensionRing L.l E (n + 1))) ℤ,
          Q.IsStrictlyGE (-b) ∧ Q.IsStrictlyLE (-a) ∧
          (∀ i : ℤ, Module.Free (Padic.coefficientExtensionRing L.l E (n + 1)) (Q.X i) ∧
            Module.Finite (Padic.coefficientExtensionRing L.l E (n + 1)) (Q.X i)) ∧
          Nonempty (DerivedCategory.Q.obj Q ≅
            (Padic.integralPointReduction L.l E n).obj
              ((ordinaryModuleDerivedInternalHom _).obj (op C, 𝟙_ _))) := by
  classical
  let R := Padic.coefficientExtensionIntegers L.l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer L.l E} : Set R)
  have hr := (Padic.extension_integers_dvr L.l E
    (Padic.coefficientExtensionAbsoluteValue L.l E)
    (spectralNorm_extends (K := Padic L.l) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing R := hr.2.2.2.2.2.2.2.1
  have hIJ : I = Padic.coefficientExtensionMaximalIdeal L.l E :=
    hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let : IsAdicComplete I R := hIJ.symm ▸
    ((Padic.finite_module_adic_complete_and_hom.{u, u, u} L.l E).1 R).1
  have hR : ModuleCat.IsDerivedComplete I (ModuleCat.of R R) :=
    ModuleCat.derivedComplete_of_adic I R
  refine ⟨hR, ?_⟩
  intro C hC
  have hpC : DerivedCategory.IsPerfect C := hC
  have hpD : DerivedCategory.IsPerfect
      ((ordinaryModuleDerivedInternalHom R).obj (op C, 𝟙_ _)) := hpC.ihom_unit
  have hD : DerivedCategory.IsPerfectRingComplex
      ((ordinaryModuleDerivedInternalHom R).obj (op C, 𝟙_ _)) := hpD
  refine ⟨?_, hD, ?_, ?_, ?_⟩
  · refine ⟨?_, hpD.finite_homology, DerivedCategory.perfect_of_derivedComplete I hR _ hD⟩
    obtain ⟨a, b, ha, hb⟩ := hpD.exists_homologyConcentratedIn
    refine ⟨Finset.Icc a b, ?_⟩
    intro i hi
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ a i hi
    · exact DerivedCategory.isZero_of_isLE _ b i hi
  · intro P a b ha hb hP he
    let := ha
    let := hb
    obtain ⟨e⟩ := he
    obtain ⟨d⟩ := CochainComplex.signedDual_model P b (fun i ↦ (hP i).1)
    refine ⟨⟨d ≪≫ ((MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _))⟩, ?_,
      CochainComplex.signedDualDegreeEquiv P, CochainComplex.signedDualDegreeEquiv_d P⟩
    intro i
    let := (hP (-i)).1
    let := (hP (-i)).2
    exact ⟨Module.Projective.of_equiv (CochainComplex.signedDualDegreeEquiv P i).symm,
      Module.Finite.equiv (CochainComplex.signedDualDegreeEquiv P i).symm⟩
  · intro n
    obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (ModuleCat.{u} R)
    let : HasRightDual C := hpC.isDualizable.some
    let := BraidedCategory.exactPairing_swap C Cᘁ
    have := Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing
      (Padic.integralPointReduction L.l E n) Cᘁ C (𝟙_ _)
    unfold MonoidalClosed.ihomUnitComparison
    infer_instance
  · intro a b h n
    obtain ⟨P, ha, hb, hP, ⟨e⟩⟩ := h n
    let := ha
    let := hb
    obtain ⟨hge, hle⟩ := CochainComplex.signedDual_bounds P a b
    obtain ⟨d⟩ := CochainComplex.signedDual_model P b (fun i ↦ by
      let := (hP i).1
      infer_instance)
    have hcmp : IsIso (MonoidalClosed.ihomUnitComparison
        (Padic.integralPointReduction L.l E n) C) := by
      obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (ModuleCat.{u} R)
      let : HasRightDual C := hpC.isDualizable.some
      let := BraidedCategory.exactPairing_swap C Cᘁ
      have := Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing
        (Padic.integralPointReduction L.l E n) Cᘁ C (𝟙_ _)
      unfold MonoidalClosed.ihomUnitComparison
      infer_instance
    refine ⟨CochainComplex.integralPointSignedDual P, hge, hle, ?_, ?_⟩
    · intro i
      let := (hP (-i)).1
      let := (hP (-i)).2
      exact ⟨Module.Free.of_equiv (CochainComplex.signedDualDegreeEquiv P i).symm,
        Module.Finite.equiv (CochainComplex.signedDualDegreeEquiv P i).symm⟩
    · exact ⟨d ≪≫ ((MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _)) ≪≫
        (asIso (MonoidalClosed.ihomUnitComparison (Padic.integralPointReduction L.l E n)
          C)).symm⟩

end WeilConjectures
