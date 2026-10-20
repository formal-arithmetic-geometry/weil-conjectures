/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
/-!
# Bounded cohomological power torsion implies rational vanishing

Source: Weil blueprint main-20261015, sec-six-functors/sk-prop-sf-dualizable-biduality,
local bounded-complex argument and its rational supplement; Stacks Tags 05RU, 08J5,
0149 and 0118 (blueprint: lem-sf-rational-bounded-cone-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

private lemma scalar_homology_zero_of_mono
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {R : Type*} [CommRing R] [Linear R (DerivedCategory A)]
    {K L : DerivedCategory A} (r : R) (f : K ⟶ L) (d : ℤ)
    [Mono ((DerivedCategory.homologyFunctor A d).map f)]
    (h : (DerivedCategory.homologyFunctor A d).map (r • 𝟙 L) = 0) :
    (DerivedCategory.homologyFunctor A d).map (r • 𝟙 K) = 0 := by
  apply (cancel_mono ((DerivedCategory.homologyFunctor A d).map f)).1
  rw [zero_comp, ← Functor.map_comp]
  have he : (r • 𝟙 K) ≫ f = f ≫ (r • 𝟙 L) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  rw [he, Functor.map_comp, h, comp_zero]

private lemma scalar_homology_zero_of_epi
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {R : Type*} [CommRing R] [Linear R (DerivedCategory A)]
    {K L : DerivedCategory A} (r : R) (f : K ⟶ L) (d : ℤ)
    [Epi ((DerivedCategory.homologyFunctor A d).map f)]
    (h : (DerivedCategory.homologyFunctor A d).map (r • 𝟙 K) = 0) :
    (DerivedCategory.homologyFunctor A d).map (r • 𝟙 L) = 0 := by
  apply (cancel_epi ((DerivedCategory.homologyFunctor A d).map f)).1
  rw [comp_zero, ← Functor.map_comp]
  have he : f ≫ (r • 𝟙 L) = (r • 𝟙 K) ≫ f := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  rw [he, Functor.map_comp, h, zero_comp]

private lemma single_map_zero_of_homology
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (q : ℤ) (M : A)
    (f : (DerivedCategory.singleFunctor A q).obj M ⟶
      (DerivedCategory.singleFunctor A q).obj M)
    (hf : (DerivedCategory.homologyFunctor A q).map f = 0) : f = 0 := by
  obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor A q).map_surjective f
  have hg := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso A q) g
  change _ ≫ (DerivedCategory.homologyFunctor A q).map
    ((DerivedCategory.singleFunctor A q).map g) ≫ _ = g at hg
  have : g = 0 := by simpa only [hf, comp_zero, zero_comp] using hg.symm
  simp [this]

private lemma truncation_homology_inclusion_iso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K : CochainComplex A ℤ) (q d : ℤ) (hd : d ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor A d).map
      (DerivedCategory.Q.map (K.ιTruncLE q))) := by
  have := K.quasiIsoAt_ιTruncLE q d hd
  have : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE q) d) := inferInstance
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A d)
    (K.ιTruncLE q)).2 this

/-- A uniform power annihilating all cohomology of an integral constructible object
annihilates its identity after multiplication of the exponent by the interval length
plus one, and its image in raw rationalization is zero.
The scalar-torsion hypothesis is written as the cohomology functor applied to the
canonical scalar endomorphism: this is multiplication by the same constant section
on the cohomology sheaf, without choosing an additional module structure.
Source: Weil blueprint main-20261015, sec-six-functors/sk-prop-sf-dualizable-biduality,
local bounded-complex argument and rational supplement; Stacks Tags 05RU, 08J5,
0149 and 0118 (blueprint: lem-sf-rational-bounded-cone-torsion).

Proof:
1. The completed coefficient sheaf has its constant O_E scalars. The canonical
ambient action and the inherited full-subcategory action are those of
`lem-weil-integral-constructible-linear`; `lem-weil-linear-abelian-derived-category`
makes localization and shifts linear. Put r = uniformizer^N.
2. In the ambient derived category set K_q = tau_{<=q} C. By
`lem-weil-pbc-truncation-cohomology`, K_{u-1} is acyclic and hence zero, while
K_v -> C is a quasi-isomorphism and hence an isomorphism. No constructibility of
these intermediate truncations is needed.
3. By `lem-weil-pbc-truncation-triangle` there is a distinguished triangle
K_{q-1} -> K_q -> H^q(C)[-q] -> K_{q-1}[1]. Multiplication by r on the third
term is zero: it is already zero on its single nonzero cohomology term, and
localization and shifts preserve the scalar action.
4. Induct from q=u-1 to v. If s=r^(q-u) kills the identity of K_{q-1}, then
s id_{K_q} vanishes after precomposition with K_{q-1} -> K_q. Clause (i) of
`lem-weil-pbc-hom-out-of-triangle-exact` factors it through H^q(C)[-q].
Multiplication by r kills this factorization, proving r^(q-u+1) id_{K_q}=0.
5. Transport the equality at q=v across K_v isomorphic to C. Multiplying once
more by r gives uniformizer^(N*(v-u+2)) id_C=0. The inclusion is full and its
scalar structure is inherited, so this is the required ambient identity.
6. In the Hom tensor E description of `def-weil-rationalization-karoubi`, with
m=N*(v-u+2), tensor balancing gives id_C tensor 1 =
(uniformizer^m id_C) tensor uniformizer^(-m)=0. This also covers m=0.
An object with zero identity has every incoming and outgoing map zero, so its
rational image is a zero object. -/
theorem sfRationalBoundedConeTorsion
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u})
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : sfIntegralConstructibleCategory l E X)
    (a b : ℤ) (_hab : a ≤ b) (N : ℕ)
    (_hBounds : ∀ d : ℤ, d ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) d).obj C.obj))
    (_hTorsion : ∀ d : ℤ,
      (DerivedCategory.homologyFunctor (scalarReductionSource l E X) d).map
        ((Padic.coefficientExtensionUniformizer l E) ^ N • 𝟙 C.obj) = 0) :
    (Padic.coefficientExtensionUniformizer l E) ^ (N * (b - a + 2).toNat) •
        𝟙 C.obj = 0 ∧
      IsZero ((sfRationalConstructibleLocalization l E X).obj C) := by
  let A := scalarReductionSource l E X
  let R := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  let r := π ^ N
  let K : CochainComplex A ℤ := DerivedCategory.Q.objPreimage C.obj
  let e : DerivedCategory.Q.obj K ≅ C.obj := DerivedCategory.Q.objObjPreimageIso C.obj
  have hK (d : ℤ) :
      (DerivedCategory.homologyFunctor A d).map (r • 𝟙 (DerivedCategory.Q.obj K)) = 0 :=
    scalar_homology_zero_of_mono r e.hom d (_hTorsion d)
  have hB (d : ℤ) (hd : d ∉ Set.Icc a b) :
      IsZero ((DerivedCategory.homologyFunctor A d).obj (DerivedCategory.Q.obj K)) :=
    (_hBounds d hd).of_iso ((DerivedCategory.homologyFunctor A d).mapIso e)
  have htr (q d : ℤ) (hd : d ≤ q) :
      IsIso ((DerivedCategory.homologyFunctor A d).map
        (DerivedCategory.Q.map (K.ιTruncLE q))) :=
    truncation_homology_inclusion_iso K q d hd
  have hbase : IsZero (DerivedCategory.Q.obj (K.truncLE (a - 1))) := by
    have : (DerivedCategory.Q.obj (K.truncLE (a - 1))).IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro d hd
      have := htr (a - 1) d (by omega)
      exact (hB d (by simp only [Set.mem_Icc, not_and_or]; omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor A d).map
          (DerivedCategory.Q.map (K.ιTruncLE (a - 1)))))
    exact DerivedCategory.TStructure.t.isZero _ (a - 1) a (by omega)
  have hind (n : ℕ) :
      r ^ n • 𝟙 (DerivedCategory.Q.obj (K.truncLE (a - 1 + n))) = 0 := by
    induction n with
    | zero =>
      rw [Int.natCast_zero, add_zero, pow_zero, one_smul]
      exact hbase.eq_of_src _ _
    | succ n ih =>
      let q : ℤ := a + n
      obtain ⟨i, j, _, _, k, ht, _⟩ := (DerivedCategory.truncation_triangle A q).1 K
      let T := Pretriangulated.Triangle.mk (DerivedCategory.Q.map i) (DerivedCategory.Q.map j) k
      have hprev : r ^ n • 𝟙 (DerivedCategory.Q.obj (K.truncLE (q - 1))) = 0 := by
        have heq : q - 1 = a - 1 + n := by dsimp [q]; omega
        rw [heq]
        exact ih
      have hq : (DerivedCategory.homologyFunctor A q).map
          (r • 𝟙 (DerivedCategory.Q.obj (K.truncLE q))) = 0 := by
        have := htr q q (le_refl q)
        exact scalar_homology_zero_of_mono r
          (DerivedCategory.Q.map (K.ιTruncLE q)) q (hK q)
      have hjepi : Epi ((DerivedCategory.homologyFunctor A q).map T.mor₂) := by
        apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
          T ht q (q + 1)).2
        exact (DerivedCategory.isZero_of_isLE
          (DerivedCategory.Q.obj (K.truncLE (q - 1)))
          (q - 1) (q + 1) (by omega)).eq_of_tgt _ _
      have hs : r • 𝟙 T.obj₃ = 0 := by
        apply single_map_zero_of_homology q (K.homology q)
        exact scalar_homology_zero_of_epi r T.mor₂ q hq
      obtain ⟨f, hf⟩ := Pretriangulated.Triangle.yoneda_exact₂ T ht
        (r ^ n • 𝟙 T.obj₂) (by
          change DerivedCategory.Q.map i ≫
            (r ^ n • 𝟙 (DerivedCategory.Q.obj (K.truncLE q))) = 0
          calc
            _ = (r ^ n • 𝟙 (DerivedCategory.Q.obj (K.truncLE (q - 1)))) ≫
                DerivedCategory.Q.map i := by
              simp only [Linear.comp_smul, Linear.smul_comp,
                Category.comp_id, Category.id_comp]
            _ = 0 := by rw [hprev, zero_comp])
      have hnext : r ^ (n + 1) • 𝟙 T.obj₂ = 0 := by
        rw [pow_succ', mul_smul, hf, ← Linear.comp_smul]
        have hrf : r • f = 0 := by
          rw [← Category.id_comp f, ← Linear.smul_comp, hs, zero_comp]
        rw [hrf, comp_zero]
      have heq : a - 1 + ((n + 1 : ℕ) : ℤ) = q := by dsimp [q]; omega
      rw [heq]
      exact hnext
  have htop : IsIso (DerivedCategory.Q.map (K.ιTruncLE b)) := by
    rw [DerivedCategory.isIso_iff]
    intro d
    by_cases hd : d ≤ b
    · exact htr b d hd
    · exact (DerivedCategory.isZero_of_isLE
        (DerivedCategory.Q.obj (K.truncLE b)) b d (by omega)).isIso
        (hB d (by simp only [Set.mem_Icc, not_and_or]; omega)) _
  let etop : DerivedCategory.Q.obj (K.truncLE b) ≅ C.obj :=
    asIso (DerivedCategory.Q.map (K.ιTruncLE b)) ≪≫ e
  have hkill : π ^ (N * (b - a + 2).toNat) • 𝟙 C.obj = 0 := by
    have h := hind (b - a + 1).toNat
    have heq : a - 1 + ((b - a + 1).toNat : ℤ) = b := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [heq] at h
    have hc : r ^ (b - a + 1).toNat • 𝟙 C.obj = 0 := by
      apply (cancel_epi etop.hom).1
      rw [comp_zero, Linear.comp_smul, Category.comp_id,
        ← Category.id_comp etop.hom, ← Linear.smul_comp, h, zero_comp]
    have hlen : (b - a + 2).toNat = (b - a + 1).toNat + 1 := by omega
    rw [pow_mul, hlen, pow_succ', mul_smul, hc, smul_zero]
  refine ⟨hkill, ?_⟩
  let m := N * (b - a + 2).toNat
  have hfull : π ^ m • (𝟙 C : C ⟶ C) = 0 := by
    apply ObjectProperty.hom_ext
    exact hkill
  rw [IsZero.iff_id_eq_zero]
  change (1 : Localization.Away π) ⊗ₜ[R] (𝟙 C : C ⟶ C) = 0
  let z : Localization.Away π := IsLocalization.Away.invSelf π ^ m
  have hz : (π ^ m) • z = (1 : Localization.Away π) := by
    rw [Algebra.smul_def]
    simp only [map_pow, z, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  calc
    (1 : Localization.Away π) ⊗ₜ[R] (𝟙 C : C ⟶ C) =
        ((π ^ m) • z) ⊗ₜ[R] (𝟙 C : C ⟶ C) := by rw [hz]
    _ = z ⊗ₜ[R] (π ^ m • (𝟙 C : C ⟶ C)) := TensorProduct.smul_tmul _ _ _
    _ = 0 := by rw [hfull, TensorProduct.tmul_zero]

end WeilConjectures
