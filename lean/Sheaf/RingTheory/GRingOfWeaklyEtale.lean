/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import Sheaf.RingTheory.FormallySmoothAdicCompleteSourceTarget
import Sheaf.RingTheory.FormallySmoothCompleteLocalRegular
import Sheaf.RingTheory.GeometricRegularityFieldIso
import Sheaf.RingTheory.GeometricallyRegularFieldExtension
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.LocalizationOfRegularRing
import Sheaf.RingTheory.GeometricRegularitySeparableExtension
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# G-rings ascend along weakly etale homomorphisms

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), 139–149, Theorem 5.3(i), Section 1.1 and Remark 5.2, pp. 139–140 and 146–147;
Stacks Project, More on Algebra, Definition 07GH (blueprint: lem-exc-weakly-etale-g-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

private theorem field_localization_of_absolutelyFlat
    {D : Type u} {K : Type v} [CommRing D] [Field K] [Ring.AbsolutelyFlat D]
    (ε : D →+* K) (hε : ε.SurjectiveOnStalks) :
    let _ := ε.toAlgebra
    let _ := RingHom.ker_isPrime ε
    IsLocalization (RingHom.ker ε).primeCompl K := by
  let _ := ε.toAlgebra
  let _ := RingHom.ker_isPrime ε
  apply (isLocalization_iff (RingHom.ker ε).primeCompl K).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact isUnit_iff_ne_zero.mpr x.2
  · intro y
    obtain ⟨a, r, c, hc, hr, he⟩ :=
      (surjective_localRingHom_iff (⊥ : Ideal K)).mp (hε ⊥ inferInstance) y
    have hc' : c ≠ 0 := hc
    have hr' : ε r ≠ 0 := hr
    refine ⟨⟨a, ⟨r, hr'⟩⟩, ?_⟩
    change y * ε r = ε a
    exact (mul_comm y (ε r)).trans (mul_left_cancel₀ hc' (by
      simpa only [mul_assoc] using he))
  · intro x y hxy
    change ε x = ε y at hxy
    obtain ⟨b, hb⟩ := Ring.AbsolutelyFlat.exists_eq_mul_self_mul (x - y)
    have hεsub : ε (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    refine ⟨⟨1 - (x - y) * b, ?_⟩, ?_⟩
    · change ε (1 - (x - y) * b) ≠ 0
      simp [hεsub]
    · change (1 - (x - y) * b) * x = (1 - (x - y) * b) * y
      apply sub_eq_zero.mp
      calc
        _ = (x - y) - (x - y) * (x - y) * b := by ring
        _ = 0 := sub_eq_zero.mpr hb

private theorem regular_localization (D : Type u) (E : Type v)
    [CommRing D] [CommRing E] [Algebra D E] [IsRegularRing D]
    (M : Submonoid D) [IsLocalization M E] : IsRegularRing E := by
  apply RingTheory.isRegularRing_of_localization D E M (algebraMap D E)
  · exact IsLocalization.map_units E
  · intro y
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
    obtain ⟨z, hz⟩ := (IsLocalization.map_units E s).exists_right_inv
    refine ⟨r, s, z, IsUnit.of_mul_eq_one_right _ hz, hz, ?_⟩
    calc
      y = y * (algebraMap D E s * z) := by rw [hz, mul_one]
      _ = algebraMap D E r * z := by rw [← mul_assoc, hy]
  · intro r hr
    obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M E).mp
      (show algebraMap D E r = algebraMap D E 0 by simpa only [map_zero] using hr)
    exact ⟨s, by simpa only [mul_zero] using hs⟩

private theorem geometric_localization (k : Type u) (D : Type v) (E : Type*)
    [Field k] [CommRing D] [CommRing E] [Algebra k D] [Algebra k E]
    [Algebra D E] [IsScalarTower k D E] (M : Submonoid D) [IsLocalization M E]
    (hD : Algebra.IsGeometricallyRegular k D) : Algebra.IsGeometricallyRegular k E := by
  have : IsNoetherianRing D := hD.1
  refine ⟨IsLocalization.isNoetherianRing M E hD.1, ?_⟩
  intro K _ _ _ _
  have : IsRegularRing (TensorProduct k K D) :=
    Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hD K
      (IntermediateField.fg_top k K)
  let φ : TensorProduct k K D →ₐ[K] TensorProduct k K E :=
    Algebra.TensorProduct.lTensor K (IsScalarTower.toAlgHom k D E)
  let : Algebra (TensorProduct k K D) (TensorProduct k K E) := φ.toRingHom.toAlgebra
  have : IsScalarTower K (TensorProduct k K D) (TensorProduct k K E) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K)))
      (TensorProduct k K E) := by
    apply IsLocalization.tensorProduct_tensorProduct_right k K M E
    ext r
    change φ (TensorProduct.tmul k 1 r) = TensorProduct.tmul k 1 (algebraMap D E r)
    simp [φ]
  exact regular_localization (TensorProduct k K D) (TensorProduct k K E)
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := K)))

private theorem cancel_weaklyEtale_fibres
    (R : Type u) (S : Type v) (C : Type*)
    [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    [Algebra.WeaklyEtale R S] [IsNoetherianRing C]
    (hreg : (algebraMap R C).IsRegular) :
    ∀ (q : Ideal S) [q.IsPrime], Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := by
  rw [IsRegular, toAlgebra_algebraMap] at hreg
  intro q hq
  let p := q.comap (algebraMap R S)
  let k := p.ResidueField
  let L := q.ResidueField
  let F := p.Fiber S
  let ρ : k →ₐ[R] L := Ideal.ResidueField.mapₐ p q (Algebra.ofId R S) rfl
  let : Algebra k L := ρ.toRingHom.toAlgebra
  have : IsScalarTower R k L := IsScalarTower.of_algebraMap_eq' ρ.comp_algebraMap.symm
  let ε : F →ₐ[k] L :=
    { __ := Algebra.TensorProduct.lift ρ (IsScalarTower.toAlgHom R S L)
        (fun _ _ ↦ Commute.all _ _)
      commutes' x := by
        change (Algebra.TensorProduct.lift ρ (IsScalarTower.toAlgHom R S L)
          (fun _ _ ↦ Commute.all _ _)) (TensorProduct.tmul R x 1) = ρ x
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  let : Algebra F L := ε.toRingHom.toAlgebra
  have : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  let : Algebra S F := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower S F L := IsScalarTower.of_algebraMap_eq fun s ↦ by
    change algebraMap S L s = ε (TensorProduct.tmul R 1 s)
    change algebraMap S L s =
      (Algebra.TensorProduct.lift ρ (IsScalarTower.toAlgHom R S L)
        (fun _ _ ↦ Commute.all _ _)) (TensorProduct.tmul R 1 s)
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hε : ε.toRingHom.SurjectiveOnStalks := by
    have heq : ε.toRingHom.comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] F).toRingHom = algebraMap S L := by
      ext s
      change ε (TensorProduct.tmul R 1 s) = algebraMap S L s
      change (Algebra.TensorProduct.lift ρ (IsScalarTower.toAlgHom R S L)
        (fun _ _ ↦ Commute.all _ _)) (TensorProduct.tmul R 1 s) = _
      rw [Algebra.TensorProduct.lift_tmul]
      simp
    exact RingHom.SurjectiveOnStalks.of_comp (heq.symm ▸ q.surjectiveOnStalks_residueField)
  have : Algebra.WeaklyEtale k F := inferInstance
  have : Ring.AbsolutelyFlat F :=
    Ring.AbsolutelyFlat.of_flat_lmul' k F (Algebra.WeaklyEtale.flat_lmul' k F)
  have : (RingHom.ker ε.toRingHom).IsPrime := RingHom.ker_isPrime ε.toRingHom
  have : IsLocalization (RingHom.ker ε.toRingHom).primeCompl L :=
    field_localization_of_absolutelyFlat ε.toRingHom hε
  have : Algebra.WeaklyEtale F L :=
    Algebra.WeaklyEtale.of_isLocalization F (RingHom.ker ε.toRingHom).primeCompl L
  have : Algebra.WeaklyEtale k L := Algebra.WeaklyEtale.trans k F L
  have : Algebra.IsSeparable k L := Algebra.WeaklyEtale.isAlgebraic
  let D := p.Fiber C
  let E := TensorProduct S F C
  let e : E ≃ₐ[k] D := Algebra.IsPushout.cancelBaseChangeAlg R k S F C
  let εS : F →ₐ[S] L :=
    { ε.toRingHom with
      commutes' s := by
        exact (IsScalarTower.algebraMap_apply S F L s).symm }
  let fS : E →ₐ[S] q.Fiber C :=
    Algebra.TensorProduct.map εS (AlgHom.id S C)
  let f : E →ₐ[k] q.Fiber C :=
    { fS.toRingHom with
      commutes' x := by
        change fS (TensorProduct.tmul S (algebraMap k F x) 1) =
          TensorProduct.tmul S (algebraMap k L x) 1
        change ε (algebraMap k F x) ⊗ₜ[S] (1 : C) = _
        rw [ε.commutes] }
  let : Algebra E (q.Fiber C) := f.toRingHom.toAlgebra
  have : IsScalarTower F E (q.Fiber C) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change TensorProduct.tmul S (ε x) 1 = f (TensorProduct.tmul S x 1)
    rfl
  have : IsScalarTower k E (q.Fiber C) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalization
      (Algebra.algebraMapSubmonoid E (RingHom.ker ε.toRingHom).primeCompl) (q.Fiber C) := by
    apply IsLocalization.tensorProduct_tensorProduct S C
      (RingHom.ker ε.toRingHom).primeCompl L
    ext c
    change ε (1 : F) ⊗ₜ[S] c = (1 : L) ⊗ₜ[S] c
    rw [map_one]
  have hD : Algebra.IsGeometricallyRegular k D := by
    simpa [D] using hreg.2 p
  have hE : Algebra.IsGeometricallyRegular k E :=
    Algebra.isGeometricallyRegular_of_fieldIso (RingEquiv.refl k) e.symm.toRingEquiv
      (fun x a ↦ e.symm.toLinearEquiv.map_smul x a) hD
  have hQ := geometric_localization k E (q.Fiber C)
    (Algebra.algebraMapSubmonoid E (RingHom.ker ε.toRingHom).primeCompl) hE
  have : IsNoetherianRing (q.Fiber C) := Ideal.isNoetherianRing_fiber q
  exact Algebra.isGeometricallyRegular_of_isSeparable k L (q.Fiber C) hQ

private theorem closed_fiber_fs
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.WeaklyEtale R S] :
    let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    let := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.le_comap_map : IsLocalRing.maximalIdeal R ≤ I.comap (algebraMap R S))
    Algebra.FormallySmoothAdic (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I)
      ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk I)) := by
  let k := R ⧸ IsLocalRing.maximalIdeal R
  let : Field k := Ideal.Quotient.field _
  let F := TensorProduct R k S
  have : Algebra.WeaklyEtale k F := inferInstance
  have : Ring.AbsolutelyFlat F :=
    Ring.AbsolutelyFlat.of_flat_lmul' k F (Algebra.WeaklyEtale.flat_lmul' k F)
  have : IsLocalRing F := by
    change IsLocalRing (TensorProduct R (IsLocalRing.ResidueField R) S)
    infer_instance
  let : Field F := (Ring.AbsolutelyFlat.isField_of_isLocalRing F).toField
  have : Algebra.IsSeparable k F := Algebra.WeaklyEtale.isAlgebraic
  have : Algebra.FormallyEtale k F := Algebra.FormallyEtale.of_isSeparable k F
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : IsLocalRing.maximalIdeal R ≤ I.comap (algebraMap R S))
  let ek : F ≃ₐ[k] S ⧸ I :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (IsLocalRing.maximalIdeal R)).symm
  have : Algebra.FormallySmooth k (S ⧸ I) := Algebra.FormallySmooth.of_equiv ek
  dsimp only
  intro D _ _ J hJ a _
  exact Algebra.FormallySmooth.comp_surjective k (S ⧸ I) J hJ a

private theorem completion_regular
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (g : R →+* S) [IsLocalHom g]
    (hfs : letI := g.toAlgebra
      Algebra.FormallySmoothAdic R S (IsLocalRing.maximalIdeal S)) :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ψ.comp (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) =
        (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp g ∧
      ψ.IsRegular := by
  obtain ⟨ψ, hψ, hψfs⟩ := Algebra.exists_formallySmoothAdic_completeSourceTarget R S g
  have hcomm : ψ.comp (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) =
      (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)).comp g := by
    apply RingHom.ext
    intro r
    apply AdicCompletion.ext_evalₐ
    intro n
    exact (hψ n _ r (AdicCompletion.evalₐ_of _ n r)).trans
      (AdicCompletion.evalₐ_of _ n (g r)).symm
  have : IsLocalHom ψ := by
    apply ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr
    rw [AdicCompletion.maximalIdeal_eq_map (R := R), Ideal.map_map, hcomm,
      ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map (R := S)]
    exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le g)
  have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing _
  have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    AdicCompletion.isNoetherianRing _
  refine ⟨ψ, hcomm, isRegular_of_formallySmoothAdic ψ ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map (R := S)]
  exact hψfs hfs

/-- The target of a weakly etale homomorphism of Noetherian rings is a G-ring if its
source is a G-ring. Source: Greco, Two theorems on excellent rings, Theorem 5.3(i),
with P = geometrically regular in Section 1.1 and the equivalence in Remark 5.2;
Stacks Project, Definition 07GH (blueprint: lem-exc-weakly-etale-g-ring).

Proof:
1. At a prime q of B, put p = f⁻¹(q), R = Aₚ and S = Bq. The induced local map
   g : R → S is flat. It is weakly etale: compose A → B with B → S, then use
   localization-flatness and the compatible-scalar tensor equivalence to descend
   the two flatness conditions from A to R.
2. The closed fibre F = κ(R) ⊗[R] S is weakly etale over κ(R), hence absolutely
   flat. It is local, so it is a field. The existing weakly-etale field theorem
   makes F/κ(R) separable algebraic, hence formally etale. Transport formal
   smoothness to S/m_R S by the canonical tensor/quotient equivalence. Ordinary
   formal smoothness implies formal smoothness for the closed-fibre adic topology.
3. Apply the flat-local closed-fibre criterion to make S/R adically formally
   smooth, then complete both rings. The coordinate formula for the induced map
   ψ : R̂ → Ŝ proves ψ ∘ u = v ∘ g. The equality of each completion's maximal
   ideal with the extended original maximal ideal proves ψ is local. Both
   completions are Noetherian, so the complete-local formal-smoothness criterion
   makes ψ regular.
4. The G-ring assumption makes u regular. Compose u with ψ, using Noetherianity
   of all fibres of the Noetherian target Ŝ, to make h = v ∘ g regular.
5. For a prime s of S over t of R, put k = κ(t), L = κ(s), F = k ⊗[R] S.
   The natural map ε : F → L is surjective on stalks because S → L is. Absolute
   flatness of F makes L its localization at ker ε: fractions follow from stalk
   surjectivity, and if ε(x) = ε(y), write x-y = (x-y)²b and use the denominator
   1-(x-y)b to annihilate x-y. Thus L/k is weakly etale and hence separable
   algebraic, without any finite-product decomposition of F.
6. Tensor cancellation identifies D = k ⊗[R] Ŝ with E = F ⊗[S] Ŝ. The fibre
   Q = L ⊗[S] Ŝ is the localization of E obtained by base change from ε. The
   regularity of h makes D geometrically regular; transport this to E. For every
   finite purely inseparable extension K/k, K ⊗[k] Q is the corresponding
   localization of K ⊗[k] E, so localization of regular rings makes it regular.
   Noetherianity also localizes. Geometric regularity therefore passes to Q,
   and then from k to L along the separable algebraic field extension.
7. The completion map v is flat and all of its fibres Q are geometrically
   regular by step 6, so it is regular. This holds at every q, proving IsGRing B.
   If B has no prime ideals, the universal condition is vacuous. -/
theorem isGRing_of_weaklyEtale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hA : IsGRing A) : IsGRing B := by
  classical
  let : Algebra A B := f.toAlgebra
  have : Algebra.WeaklyEtale A B := hf
  refine ⟨inferInstance, ?_⟩
  intro q hq
  let p := q.comap f
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q
  let g : R →+* S := Localization.localRingHom p q f rfl
  let : Algebra R S := g.toAlgebra
  have : IsLocalHom g := Localization.isLocalHom_localRingHom p q f rfl
  have hgflat : g.Flat := RingHom.Flat.localRingHom
    (show f.Flat from (RingHom.flat_algebraMap_iff.mpr inferInstance)) q p rfl
  have hweak : Algebra.WeaklyEtale R S := by
    have : IsScalarTower A B S := inferInstance
    have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun a ↦
      (Localization.localRingHom_to_map p q f rfl a).symm
    have : Algebra.WeaklyEtale B S :=
      Algebra.WeaklyEtale.of_isLocalization B q.primeCompl S
    have : Algebra.WeaklyEtale A S := Algebra.WeaklyEtale.trans A B S
    refine ⟨(Module.flat_iff_of_isLocalization R p.primeCompl S).mpr inferInstance, ?_⟩
    have : TensorProduct.CompatibleSMul A R S S :=
      IsLocalization.tensorProduct_compatibleSMul p.primeCompl R S S
    let e : TensorProduct R S S ≃ₐ[R] TensorProduct A S S :=
      Algebra.TensorProduct.equivOfCompatibleSMul A R R S S
    have heq : (Algebra.TensorProduct.lmul' R (S := S)).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := S)).toRingHom.comp e.toRingHom := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        change x * y = (Algebra.TensorProduct.lmul' A) (TensorProduct.tmul A x y)
        rw [Algebra.TensorProduct.lmul'_apply_tmul]
    rw [heq]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective)
      (Algebra.WeaklyEtale.flat_lmul' A S)
  have : Algebra.WeaklyEtale R S := hweak
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom g›
  have hfs : Algebra.FormallySmoothAdic R S (IsLocalRing.maximalIdeal S) :=
    formallySmoothAdic_of_flat_closedFiber R S (algebraMap R S) hgflat
      (by simpa only [toAlgebra_algebraMap] using closed_fiber_fs R S)
  obtain ⟨ψ, hcomm, hψreg⟩ := completion_regular R S g hfs
  let Rh := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let Sh := AdicCompletion (IsLocalRing.maximalIdeal S) S
  have : IsNoetherianRing Sh := AdicCompletion.isNoetherianRing _
  let : Algebra Rh Sh := ψ.toAlgebra
  let : Algebra R Sh := ((algebraMap S Sh).comp g).toAlgebra
  have : IsScalarTower R Rh Sh := IsScalarTower.of_algebraMap_eq' hcomm.symm
  have hcomp : (algebraMap R Sh).IsRegular :=
    (hA.2 p).comp_of_fiber_noetherian hψreg (fun t _ ↦ Ideal.isNoetherianRing_fiber t)
  have : IsScalarTower R S Sh := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  change (algebraMap S Sh).IsRegular
  rw [IsRegular, toAlgebra_algebraMap]
  exact ⟨flat_algebraMap_iff.mpr inferInstance, cancel_weaklyEtale_fibres R S Sh hcomp⟩

end RingHom
