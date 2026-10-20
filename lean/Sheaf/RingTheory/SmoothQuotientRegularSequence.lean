/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Sheaf.RingTheory.FlatQuotientFiberRegularSequence
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.Ideal

/-!
# Local regular generators for a smooth quotient

Source: Stacks Project, Divisors, Tags 067T and 063W
(blueprint: lem-pur-smooth-quotient-regular-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- A surjection between smooth algebras has a regular-sequence kernel near each
prime containing its kernel. The generators are chosen after localization; an
arbitrary list generating the kernel need not be regular.

Source: Stacks Project, Divisors, Tag 067T, smooth special case, using Tag 063W(2)
(blueprint: lem-pur-smooth-quotient-regular-sequence).

Proof: Both algebras are flat and finitely presented over R. Finite presentation
of the quotient over A makes the kernel finitely generated. At Q on the fibre
over its contraction to R, the ambient and quotient local rings are regular.
The regular-local quotient theorem gives a prefix of a regular parameter system
generating the fibre kernel. Lift these parameters to the original kernel,
clearing denominators outside Q. Flatness of the quotient identifies the fibre
kernel with the tensor of the original kernel. Nakayama, applied to the finite
kernel modulo the lifted generators, shows that they generate at Q. Clear
finitely many denominators to make them generate on a principal neighbourhood.
The fibre is Noetherian, so spread its regular sequence to a principal open;
write the fibre denominator as a numerator from A divided by an element from
the base outside the contracted prime, and invert that numerator in A.
Inductively apply the fibre-Cartier criterion to each successive equation.
It gives a smaller principal neighbourhood where this equation is regular and
its quotient is flat over R. Earlier injections survive localization, and each
prefix quotient remains finitely presented. The final quotient retains Q and
is nonzero. The resulting regular list generates the localized kernel. The
same assertion for any model D of that localization follows by its canonical
A-algebra equivalence with Localization.Away g. -/
theorem exists_regularSequence_smooth_surjection
    (R A C : Type u) [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Smooth R A] [Smooth R C]
    (φ : A →ₐ[R] C) (hφ : Function.Surjective φ)
    (Q : PrimeSpectrum A) (hQ : RingHom.ker φ.toRingHom ≤ Q.asIdeal) :
    ∃ g : A, g ∉ Q.asIdeal ∧
      ∀ (D : Type u) [CommRing D] [Algebra A D] [IsLocalization.Away g D],
        ∃ f : List D, RingTheory.Sequence.IsRegular D f ∧
          (RingHom.ker φ.toRingHom).map (algebraMap A D) = Ideal.ofList f := by
  classical
  let I := RingHom.ker φ.toRingHom
  let e : (A ⧸ I) ≃ₐ[R] C := Ideal.quotientKerAlgEquivOfSurjective hφ
  have : Smooth R (A ⧸ I) := Smooth.of_equiv e.symm
  have hI : I.FG := FinitePresentation.ker_fG_of_surjective φ hφ
  let p := Q.comap (algebraMap R A)
  let P := PrimeSpectrum.preimageEquivFiber R A p ⟨Q, rfl⟩
  have hP : P.comap TensorProduct.includeRight.toRingHom = Q := by
    exact congrArg Subtype.val ((PrimeSpectrum.preimageEquivFiber R A p).symm_apply_apply
      ⟨Q, rfl⟩)
  let F := p.asIdeal.Fiber A
  let J : Ideal F := I.map TensorProduct.includeRight.toRingHom
  have hJP : J ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact hQ.trans_eq (congrArg PrimeSpectrum.asIdeal hP).symm
  let L := Localization.AtPrime P.asIdeal
  let K : Ideal L := J.map (algebraMap F L)
  have hK : K ≠ ⊤ := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint P.asIdeal.primeCompl L J).mpr
    exact Set.disjoint_left.mpr (fun x hx hJx ↦ hx (hJP hJx))
  have : IsRegularLocalRing L := (smooth_fibre_regular_local (R := R) (S := A) p).2 P
  have : Smooth p.asIdeal.ResidueField (F ⧸ J) :=
    Smooth.of_equiv (TensorProduct.tensorQuotientEquiv p.asIdeal.ResidueField A
      p.asIdeal.ResidueField I)
  let P' : Ideal (F ⧸ J) := P.asIdeal.map (Ideal.Quotient.mk J)
  have : P'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa using hJP)
  have hM : algebraMapSubmonoid (F ⧸ J) P.asIdeal.primeCompl = P'.primeCompl := by
    have heq : P'.comap (Ideal.Quotient.mk J) = P.asIdeal := Ideal.comap_map_mk hJP
    rw [algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq]
    simpa only [heq] using Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective P'
  have : IsLocalization P'.primeCompl (L ⧸ K) := by
    rw [← hM]
    exact inferInstance
  have : IsRegularLocalRing (Localization.AtPrime P') :=
    smooth_over_field_regular_local p.asIdeal.ResidueField (F ⧸ J) P'
  have : IsRegularLocalRing (L ⧸ K) := .of_ringEquiv
    (IsLocalization.algEquiv P'.primeCompl (L ⧸ K) (Localization.AtPrime P')).symm.toRingEquiv
  let d := (IsLocalRing.maximalIdeal L).spanFinrank
  have hd : ringKrullDim L = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := L)).symm
  obtain ⟨xs, c, -, hxs, hgen⟩ :=
    RingTheory.exists_parameters_regularLocalQuotient L d hd K hK
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    L d hd xs hxs).1
  have hprefix : RingTheory.Sequence.IsRegular L (xs.take c) := by
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (M := L) (fun x hx ↦ hxs.1 ▸ Ideal.subset_span (List.mem_of_mem_take hx))).mpr
    have hw := hreg.toIsWeaklyRegular
    rw [← List.take_append_drop c xs] at hw
    exact ((RingTheory.Sequence.isWeaklyRegular_append_iff L _ _).mp hw).1
  exact exists_regularSequence_of_flat_quotient_fiber R A I hI p Q P hP
    ⟨xs.take c, hprefix, hgen⟩

end Algebra
