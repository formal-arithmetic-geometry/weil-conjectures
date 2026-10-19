/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Unconditional bounds for open complements

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
node thm-pur-open-complement-unconditional, statement and proof Steps 1-8
(blueprint: thm-pur-open-complement-unconditional).

## Main statements

* `hasOpenComplementCondition_of_isSepClosed`: bound `2 * d` for every finite
  prime-power-torsion coefficient ring, fixed after the geometric dimension bound.
* `hasOpenComplementCondition_finiteStage`: the same bound at every finite coefficient stage.
* `hasOpenComplementCondition_affineChart`: the chart bound and dimension inequality.
* `hasOpenComplementCondition_emptyChart`: the bound zero when the chart base is empty.

The dimension-zero and curve computations named in the source are independent earlier
computations, not hypotheses of these assertions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The open-complement condition holds with one geometric bound for every finite
prime-power-torsion coefficient ring away from the characteristic.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Steps 1-4
(blueprint: thm-pur-open-complement-unconditional).

Proof:
1. A quasi-compact open immersion is finite type by
   lem-weil-pbc-qc-open-immersion-finite-type. A finite affine cover of T and the
   quasi-compactness of j give a finite affine cover of V
   (lem-pqf-finite-affine-cover-qc-open). The coordinate algebras are finite type by
   lem-weil-pbc-lft-affine-pairs. Thus V is finite type over k. The open embedding gives
   dim V <= dim T <= d by lem-weil-pbc-open-subspace-dimension-monotone.
2. Choose r >= 1 killing A and apply thm-exc-direct-image-input-holds with N = ell^r,
   invertible in k. Its first clause gives constructibility in nonnegative degrees.
   For negative degrees use lem-weil-pbc-derived-functor-negative-vanishing for j_*,
   additive and left exact by def-weil-pbc-direct-image; its module-sheaf categories
   are Grothendieck abelian by lem-weil-pbc-module-sheaves-grothendieck-abelian.
   The zero sheaf is constructible using the constant finite zero module.
3. Apply lem-kun-relative-torsion-direct-image-dimension-bound with X = V, Y = T,
   f = j and the composite structure map of V. The ring A is additively torsion, and
   dim V <= d. This gives vanishing above 2d for all module sheaves, including those
   which are not constructible.
4. These are exactly the two conjuncts of def-exc-open-complement-bound. The natural
   number d is fixed before A, so the bound is independent of coefficients. A bound
   depending only on T exists by lem-kun-dimension-finite-type; for empty T use d = 0.
-/
theorem hasOpenComplementCondition_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    {T V : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)
    (hkill : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0) :
    HasOpenComplementCondition A j (2 * d) := by
  have hdimV : topologicalKrullDim V ≤ (d : WithBot ℕ∞) :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  obtain ⟨r, hr, hkill⟩ := hkill
  have hell : IsUnit (ℓ : k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime k hprime hchar.symm)
  have hN : IsUnit (((ℓ ^ r : ℕ) : ℤ) : k) := by
    simpa using hell.pow r
  have hA : ∀ a : A, ((ℓ ^ r : ℕ) : ℤ) • a = 0 := by
    intro a
    simpa only [zsmul_eq_mul, Int.cast_natCast, nsmul_eq_mul, mul_one, zero_mul] using
      congrArg (fun x : A ↦ x * a) hkill
  have hinput := hasDirectImageFinitenessInput_of_isSepClosed k
    ((ℓ ^ r : ℕ) : ℤ) hN A hA
  refine ⟨?_, ?_⟩
  · intro M q hq
    exact Etale.isZero_higherDirectImage_of_two_mul_lt isAddTorsion_of_finite
      j (j ≫ T ↘ Spec (.of k)) (T ↘ Spec (.of k)) rfl d hdimV M q (by simpa using hq)
  · intro F q hF
    by_cases hq : 0 ≤ q
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      have hc : IsConstructibleSheaf
          ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
            ((DerivedCategory.Plus.ι ⋙
              (Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
        (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
          (hinput.1 (j ≫ T ↘ Spec (.of k)) (T ↘ Spec (.of k)) j rfl F hF n)
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
        (IsConstructibleSheaf.of_iso
          ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
            ((Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm)
    · apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      apply IsConstructibleSheaf.of_isZero
      exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        (Etale.lowerStar (ModuleCat.{u + 1} A) j)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 (by omega)

/-- Every positive finite coefficient stage in the purity conventions has the same
open-complement bound. The existential finite instance records finiteness of the actual
coefficient quotient, rather than requiring it as an extra hypothesis.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Step 5
(blueprint: thm-pur-open-complement-unconditional).

Proof: In the fixed finite-field datum k is algebraically closed of characteristic p.
The coefficient prime ell is different from p. By def-weil-l-adic-coefficient-extension,
A_{E,n} is finite. The absolute value extends the ell-adic absolute value, so
|ell| = ell^(-1) < 1 by def-weil-l-adic-numbers. Thus ell lies in the maximal ideal
(varpi_E), and ell^n lies in (varpi_E^n), killing A_{E,n}. Apply Steps 1-4 above to the
standard ULift of this quotient. The bound 2d contains neither E nor n. This concerns
ordinary small-etale cohomology and uses no pro-etale comparison.
-/
theorem hasOpenComplementCondition_finiteStage
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {T V : Scheme.{u}} [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ hA : Finite P.Coefficient,
      @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA V T j
        inferInstance inferInstance (2 * d) := by
  classical
  have : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  have hfinite : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have hA : Finite P.Coefficient := inferInstanceAs (Finite (ULift P.Ring))
  refine ⟨hA, hasOpenComplementCondition_of_isSepClosed P.field.k d hdim j
    P.Coefficient P.coefficients.l (Fact.out : P.coefficients.l.Prime) ?_ ?_⟩
  · let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have hcard : Fintype.card P.field.k₀ = P.field.p ^ P.field.a := by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq]
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow hcard
    have : CharP P.field.k P.field.p := (Algebra.charP_iff P.field.k₀ P.field.k _).mp
      inferInstance
    simpa only [ringChar.eq P.field.k P.field.p] using P.coefficients.different
  · refine ⟨P.level, P.level_pos, ?_⟩
    apply (ULift.ringEquiv : P.Coefficient ≃+* P.Ring).injective
    simp only [nsmul_eq_mul, mul_one, map_natCast, map_zero]
    rw [Nat.cast_pow]
    change Ideal.Quotient.mk _ ((P.coefficients.l :
      Padic.coefficientExtensionIntegers P.coefficients.l P.extension) ^ P.level) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h := (Padic.extension_integers_dvr P.coefficients.l P.extension
      (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension)
      (spectralNorm_extends (K := Padic P.coefficients.l) (L := P.extension)))
    have hspec := h.choose_spec.choose_spec
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer
        P.coefficients.l P.extension} :
        Set (Padic.coefficientExtensionIntegers P.coefficients.l P.extension)) =
        Padic.coefficientExtensionMaximalIdeal P.coefficients.l P.extension :=
      hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    change _ ∈ Ideal.span _ ^ P.level
    rw [hgen]
    apply Ideal.pow_mem_pow
    apply (hspec.2.1 _).mpr
    change spectralNorm (Padic P.coefficients.l) P.extension
      (P.coefficients.l : P.extension) < 1
    rw [← map_natCast (algebraMap (Padic P.coefficients.l) P.extension),
      spectralNorm_extends]
    exact Padic.norm_p_lt_one

/-- A nonempty affine chart base B in a finite-type k-scheme Y gives the dimension
inequality m + dim B <= m + dim Y and the bound 2(m + dim B), uniformly at finite stages.
Here b names the natural-number dimension of the nonempty base. Taking a closed chart
inside affine space gives exactly the complements used in thm-pur-general-admissibility.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Steps 6-7
(blueprint: thm-pur-open-complement-unconditional).

Proof: The affine open B has a finite-type coordinate algebra R by
lem-weil-pbc-lft-affine-pairs. The ambient scheme is Spec R[x_1,...,x_m] by
 def-sbc-affine-space. Both rings are Noetherian by lem-wf-affine-noetherian-components.
The polynomial dimension formula lem-sf-noetherian-polynomial-dimension and
lem-weil-pbc-spec-topological-krull-dimension-ring give dim A^m_B = m + b.
The open-subspace dimension inequality gives b <= dim Y. Noetherianity makes the
complement inclusion quasi-compact. Apply the finite-stage assertion with d = m + b.
Every closed affine chart in the separated finite-type assembly has this form; no
preservation or admissibility conclusion of that assembly is used.
-/
theorem hasOpenComplementCondition_affineChart
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (B : Y.Opens) (hB : IsAffineOpen B) [Nonempty B]
    (m b : ℕ) (hb : topologicalKrullDim B.toScheme = (b : WithBot ℕ∞))
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin m)) B.toScheme)
    [IsClosedImmersion i] :
    ((m + b : ℕ) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) + topologicalKrullDim Y ∧
      ∃ hj : QuasiCompact i.openComplement.ι,
        ∃ hA : Finite P.Coefficient,
          @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA
            i.openComplement.toScheme (AffineSpace (ULift.{u} (Fin m)) B.toScheme)
            i.openComplement.ι inferInstance hj (2 * (m + b)) := by
  have : IsAffine B.toScheme := hB
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  have : LocallyOfFiniteType (B.toScheme ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType (B.ι ≫ Y ↘ Spec (.of P.field.k))
    infer_instance
  have : IsLocallyNoetherian B.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (B.toScheme ↘ Spec (.of P.field.k))
  have : LocallyOfFiniteType
      (AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ B.toScheme) ≫
        B.toScheme ↘ Spec (.of P.field.k))
    infer_instance
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin m)) B.toScheme) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ Spec (.of P.field.k))
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin m)) B.toScheme) := {}
  have hbaseDim : topologicalKrullDim B.toScheme = ringKrullDim Γ(B.toScheme, ⊤) := by
    rw [B.toScheme.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  have : IsNoetherianRing Γ(B.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hdimA : topologicalKrullDim (AffineSpace (ULift.{u} (Fin m)) B.toScheme) =
      ((m + b : ℕ) : WithBot ℕ∞) := by
    let e := AffineSpace.isoOfIsAffine (ULift.{u} (Fin m)) B.toScheme
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    change topologicalKrullDim
      (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) Γ(B.toScheme, ⊤))) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ← hbaseDim, hb]
    simp [Nat.cast_add, add_comm]
  refine ⟨?_, inferInstance, ?_⟩
  · rw [Nat.cast_add]
    exact add_le_add le_rfl (hb ▸ B.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le)
  · exact hasOpenComplementCondition_finiteStage P (m + b) hdimA.le i.openComplement.ι

/-- An empty affine chart base may be retained: its ambient affine space and complement
are empty, and the open-complement bound is zero at every finite stage.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Step 7, empty-chart clause
(blueprint: thm-pur-open-complement-unconditional).

Proof: Affine space over the empty scheme is empty, being a fibre product over it.
Its open complement is empty too. All coefficient sheaves on the empty small-etale
site are zero by the empty covering axiom. Hence all higher direct images vanish and
are constructible, for the bound zero. Finite-stage coefficients are finite by
 def-weil-l-adic-coefficient-extension, as in Step 5. Step 8 of the source only compares
these assertions with the independent dimension-zero and curve computations.
-/
theorem hasOpenComplementCondition_emptyChart
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (B : Y.Opens) (hB : IsAffineOpen B) [IsEmpty B] (m : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin m)) B.toScheme)
    [IsClosedImmersion i] :
    IsEmpty (AffineSpace (ULift.{u} (Fin m)) B.toScheme) ∧
      IsEmpty i.openComplement.toScheme ∧
      ∃ hj : QuasiCompact i.openComplement.ι,
        ∃ hA : Finite P.Coefficient,
          @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA
            i.openComplement.toScheme (AffineSpace (ULift.{u} (Fin m)) B.toScheme)
            i.openComplement.ι inferInstance hj 0 := by
  have : IsAffine B.toScheme := hB
  have hEmpty : IsEmpty (AffineSpace (ULift.{u} (Fin m)) B.toScheme) :=
    ⟨fun x ↦ isEmptyElim ((AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ B.toScheme) x)⟩
  have hComplement : IsEmpty i.openComplement.toScheme :=
    ⟨fun x ↦ isEmptyElim (i.openComplement.ι x)⟩
  have : LocallyOfFiniteType (B.toScheme ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType (B.ι ≫ Y ↘ Spec (.of P.field.k))
    infer_instance
  have : IsLocallyNoetherian B.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (B.toScheme ↘ Spec (.of P.field.k))
  have : LocallyOfFiniteType
      (AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ Spec (.of P.field.k)) := by
    change LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin m)) B.toScheme ↘ B.toScheme) ≫
        B.toScheme ↘ Spec (.of P.field.k))
    infer_instance
  have hdim : topologicalKrullDim (AffineSpace (ULift.{u} (Fin m)) B.toScheme) ≤
      (0 : WithBot ℕ∞) := by
    have : DiscreteTopology (AffineSpace (ULift.{u} (Fin m)) B.toScheme) := inferInstance
    exact topologicalKrullDim_zero_of_discreteTopology _
  refine ⟨hEmpty, hComplement, inferInstance, ?_⟩
  simpa using hasOpenComplementCondition_finiteStage P 0 hdim i.openComplement.ι

end AlgebraicGeometry.Scheme
