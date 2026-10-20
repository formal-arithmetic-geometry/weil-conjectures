/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.RingTheory.FiberRegularSequenceNeighbourhood
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Lifting regular equations from a fibre

Source: Stacks Project, Divisors, Tag 063W(2)
(blueprint: lem-pur-flat-quotient-fiber-regular-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Algebra

open _root_.TensorProduct

private lemma ofList_eq_of_unit_multiples
    {L : Type u} [CommRing L] {xs ys : List L}
    (h : List.Forall₂ (fun x y ↦ ∃ u : L, IsUnit u ∧ y = u * x) xs ys) :
    Ideal.ofList xs = Ideal.ofList ys := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hxy h ih =>
    obtain ⟨u, hu, rfl⟩ := hxy
    rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.span_singleton_mul_left_unit hu, ih]

private lemma regular_of_unit_multiples
    {L : Type u} [CommRing L] {xs ys : List L}
    (h : List.Forall₂ (fun x y ↦ ∃ u : L, IsUnit u ∧ y = u * x) xs ys)
    (hx : RingTheory.Sequence.IsRegular L xs) : RingTheory.Sequence.IsRegular L ys := by
  refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
  · have hlen := h.length_eq
    have hi' : i < xs.length := by omega
    obtain ⟨u, hu, he⟩ := h.get hi' hi
    change ys[i] = u * xs[i] at he
    have hprev := ofList_eq_of_unit_multiples (List.forall₂_take i h)
    have hr := hx.regular_mod_prev i hi'
    change IsSMulRegular _ ys[i]
    change IsSMulRegular _ xs[i] at hr
    rw [← hprev, he]
    exact (hu.isSMulRegular _).mul hr
  · rw [← ofList_eq_of_unit_multiples h]
    exact hx.top_ne_smul

set_option backward.isDefEq.respectTransparency false in
private lemma fiber_ideal_clear_denominator
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) (I : Ideal A) (x : p.asIdeal.Fiber A)
    (hx : x ∈ I.map TensorProduct.includeRight.toRingHom) :
    ∃ r ∉ p.asIdeal, ∃ a ∈ I,
      r • x = (TensorProduct.includeRight a : p.asIdeal.Fiber A) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨1, p.isPrime.one_notMem, a, ha, one_smul _ _⟩
  | zero => exact ⟨1, p.isPrime.one_notMem, 0, I.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨r, hr, a, ha, he⟩ := ihx
    obtain ⟨s, hs, b, hb, he'⟩ := ihy
    refine ⟨r * s, p.asIdeal.primeCompl.mul_mem hr hs, s • a + r • b,
      I.add_mem (I.restrictScalars R |>.smul_mem s ha)
        (I.restrictScalars R |>.smul_mem r hb), ?_⟩
    rw [smul_add, mul_comm r s, mul_smul, he, mul_comm s r, mul_smul, he']
    simp only [map_add, map_smul]
  | smul c x hx ih =>
    obtain ⟨s, hs, b, hb, he⟩ := ih
    obtain ⟨r, hr, a, he'⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal c
    refine ⟨r * s, p.asIdeal.primeCompl.mul_mem hr hs, a * b, I.mul_mem_left a hb, ?_⟩
    change (r * s) • (c * x) = _
    rw [mul_smul, ← mul_smul_comm, he, ← smul_mul_assoc, he']
    exact (map_mul TensorProduct.includeRight a b).symm

set_option backward.isDefEq.respectTransparency false in
private lemma exists_unit_multiple_lift
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) (I : Ideal A) (P : PrimeSpectrum (p.asIdeal.Fiber A))
    (z : Localization.AtPrime P.asIdeal)
    (hz : z ∈ (I.map TensorProduct.includeRight.toRingHom).map
      (algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal))) :
    ∃ a ∈ I, ∃ u : Localization.AtPrime P.asIdeal, IsUnit u ∧
      algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal)
        (TensorProduct.includeRight a) = u * z := by
  let F := p.asIdeal.Fiber A
  let L := Localization.AtPrime P.asIdeal
  obtain ⟨⟨x, t⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff
    P.asIdeal.primeCompl L).mp hz
  obtain ⟨r, hr, a, ha, hrt⟩ := fiber_ideal_clear_denominator p I x x.2
  have hu : IsUnit (algebraMap R F r) := by
    rw [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField F]
    exact (isUnit_iff_ne_zero.mpr (fun h ↦ hr
      (Ideal.algebraMap_residueField_eq_zero.mp h))).map (algebraMap p.asIdeal.ResidueField F)
  refine ⟨a, ha, algebraMap F L (algebraMap R F r) * algebraMap F L t,
    (hu.map (algebraMap F L)).mul (IsLocalization.map_units L t), ?_⟩
  have he' : z * algebraMap F L t = algebraMap F L x := he
  have hrt' : algebraMap R F r * (x : F) = TensorProduct.includeRight a := by
    simpa only [F, Algebra.smul_def] using hrt
  rw [← hrt', map_mul, ← he']
  ring

private lemma exists_list_lifts
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) (I : Ideal A) (P : PrimeSpectrum (p.asIdeal.Fiber A))
    (xs : List (Localization.AtPrime P.asIdeal))
    (hxs : ∀ x ∈ xs, x ∈ (I.map TensorProduct.includeRight.toRingHom).map
      (algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal))) :
    ∃ fs : List A, (∀ f ∈ fs, f ∈ I) ∧
      List.Forall₂ (fun x a ↦ ∃ u : Localization.AtPrime P.asIdeal, IsUnit u ∧
        algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal)
          (TensorProduct.includeRight a) = u * x) xs fs := by
  induction xs with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons x xs ih =>
    obtain ⟨a, ha, u, hu, he⟩ := exists_unit_multiple_lift p I P x (hxs x (by simp))
    obtain ⟨fs, hfs, hrel⟩ := ih (fun y hy ↦ hxs y (List.mem_cons_of_mem x hy))
    refine ⟨a :: fs, ?_, .cons ⟨u, hu, he⟩ hrel⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ha
    · exact hfs f hf

set_option backward.isDefEq.respectTransparency false in
private lemma exists_multiplier_of_fiber_generators
    (R A K : Type u) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] (I J : Ideal A) (hI : I.FG) (hJI : J ≤ I)
    [Module.Flat R (A ⧸ I)]
    (P : Ideal (A ⊗[R] K)) [P.IsPrime]
    (hgen : (I.map TensorProduct.includeLeftRingHom).map
        (algebraMap (A ⊗[R] K) (Localization.AtPrime P)) ≤
      (J.map TensorProduct.includeLeftRingHom).map
        (algebraMap (A ⊗[R] K) (Localization.AtPrime P))) :
    ∃ t ∉ P.comap TensorProduct.includeLeftRingHom, ∀ a ∈ I, t * a ∈ J := by
  classical
  let E := A ⊗[R] K
  let ι : A →+* E := TensorProduct.includeLeftRingHom
  let N : Submodule A I := Submodule.comap (Submodule.subtype I) J
  let ψ : E ⊗[A] I →ₗ[E] E :=
    (AlgebraTensorModule.rid A E E).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor E E I.subtype
  let π : E ⊗[A] I →ₗ[E] E ⊗[A] (I ⧸ N) :=
    AlgebraTensorModule.lTensor E E N.mkQ
  have hψ (e : E) (a : I) : ψ (e ⊗ₜ[A] a) = ι a * e := by
    change (a : A) • e = _
    exact Algebra.smul_def (a : A) e
  have hinj₀ : Function.Injective (I.subtype.lTensor E) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    have hA : Function.Injective ((I.subtype.restrictScalars R).rTensor K) := by
      rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
      refine LinearMap.lTensor_injective_of_exact_of_flat
        (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective _
        Subtype.val_injective ?_ K
      rw [LinearMap.exact_iff]
      ext x
      change (Ideal.Quotient.mk I x = 0) ↔ ∃ a : I, (a : A) = x
      exact Ideal.Quotient.eq_zero_iff_mem.trans
        ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩
    have hcomm : ∀ x, AlgebraTensorModule.cancelBaseChange R A A A K
        (I.subtype.rTensor E x) =
      (I.subtype.restrictScalars R).rTensor K
        (AlgebraTensorModule.cancelBaseChange R A A I K x) := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul a e =>
        induction e using TensorProduct.induction_on with
        | zero => simp
        | add e e' he he' => simp only [tmul_add, map_add, he, he']
        | tmul b k =>
          rw [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
            AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
          rfl
    intro x y hxy
    apply (AlgebraTensorModule.cancelBaseChange R A A I K).injective
    apply hA
    rw [← hcomm, ← hcomm, hxy]
  have hinj : Function.Injective ψ :=
    (AlgebraTensorModule.rid A E E).injective.comp hinj₀
  have hle : J.map ι ≤ (LinearMap.ker π).map ψ := by
    rw [Ideal.map, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨1 ⊗ₜ[A] (⟨a, hJI ha⟩ : I), ?_, ?_⟩
    · change (1 : E) ⊗ₜ[A] (N.mkQ ⟨a, hJI ha⟩) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr ha, tmul_zero]
    · rw [hψ, mul_one]
  have hkey : ∀ a : I, ∃ t ∉ P,
      t ⊗ₜ[A] (Submodule.Quotient.mk a : I ⧸ N) = 0 := by
    intro a
    have ha := hgen (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem ι a.2))
    obtain ⟨t, htP, ht⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      P.primeCompl (Localization.AtPrime P) (J.map ι) (ι a)).mp ha
    obtain ⟨z, hz, he⟩ := hle ht
    have he' : ψ (t ⊗ₜ[A] a) = ψ z := by
      rw [hψ, he]
      ring
    have hz' : π (t ⊗ₜ[A] a) = 0 := by rw [hinj he']; exact hz
    exact ⟨t, htP, hz'⟩
  have : Module.Finite A I := Module.Finite.iff_fg.mpr hI
  have hall : ∀ y : E ⊗[A] (I ⧸ N), ∃ t ∉ P, t • y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨1, Ideal.IsPrime.one_notMem inferInstance, smul_zero _⟩
    | tmul e z =>
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective N z
      obtain ⟨t, ht, he⟩ := hkey a
      refine ⟨t, ht, ?_⟩
      rw [smul_tmul', smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_tmul']
      change e • (t ⊗ₜ[A] (Submodule.Quotient.mk a : I ⧸ N)) = 0
      rw [he, smul_zero]
    | add x y hx hy =>
      obtain ⟨s, hs, he⟩ := hx
      obtain ⟨t, ht, he'⟩ := hy
      refine ⟨s * t, P.primeCompl.mul_mem hs ht, ?_⟩
      rw [smul_add, mul_smul, mul_smul, he', smul_zero, add_zero,
        smul_comm, he, smul_zero]
  obtain ⟨t, ht, he⟩ := Module.exists_notMem_forall_smul_eq_zero_of_tensor P hall
  refine ⟨t, ht, fun a ha ↦ ?_⟩
  have hz := he (Submodule.Quotient.mk (⟨a, ha⟩ : I))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  exact hz

set_option backward.isDefEq.respectTransparency false in
private lemma exists_multiplier_of_right_fiber_generators
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (I J : Ideal A) (hI : I.FG) (hJI : J ≤ I) [Module.Flat R (A ⧸ I)]
    (p : PrimeSpectrum R) (P : PrimeSpectrum (p.asIdeal.Fiber A))
    (hgen : (I.map TensorProduct.includeRight.toRingHom).map
        (algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal)) ≤
      (J.map TensorProduct.includeRight.toRingHom).map
        (algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal))) :
    ∃ t ∉ (P.comap TensorProduct.includeRight.toRingHom).asIdeal,
      ∀ a ∈ I, t * a ∈ J := by
  let E := A ⊗[R] p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber A
  let e : E ≃ₐ[R] F := TensorProduct.comm R A p.asIdeal.ResidueField
  let P₀ := P.asIdeal.comap e.toRingHom
  let l := Localization.localRingEquiv P₀ P.asIdeal e.toRingEquiv rfl
  have he : e.toRingHom.comp TensorProduct.includeLeftRingHom =
      TensorProduct.includeRight.toRingHom := by ext; rfl
  have hl : l.toRingHom.comp (algebraMap E (Localization.AtPrime P₀)) =
      (algebraMap F (Localization.AtPrime P.asIdeal)).comp e.toRingHom := by
    apply RingHom.ext
    intro x
    exact Localization.localRingHom_to_map P₀ P.asIdeal e.toRingHom rfl x
  have hl' : l.toRingHom.comp ((algebraMap E (Localization.AtPrime P₀)).comp
      TensorProduct.includeLeftRingHom) =
        (algebraMap F (Localization.AtPrime P.asIdeal)).comp
          TensorProduct.includeRight.toRingHom := by
    rw [← RingHom.comp_assoc, hl, RingHom.comp_assoc, he]
  obtain ⟨t, ht, hmul⟩ := exists_multiplier_of_fiber_generators R A p.asIdeal.ResidueField
    I J hI hJI P₀ (by
      have hh := Ideal.comap_mono (f := l.toRingHom) (show
          ((I.map TensorProduct.includeLeftRingHom).map
            (algebraMap E (Localization.AtPrime P₀))).map l.toRingHom ≤
          ((J.map TensorProduct.includeLeftRingHom).map
            (algebraMap E (Localization.AtPrime P₀))).map l.toRingHom from by
        simpa only [Ideal.map_map, hl'] using hgen)
      simpa only [Ideal.comap_map_of_bijective l.toRingHom l.bijective] using hh)
  refine ⟨t, ?_, hmul⟩
  change t ∉ P₀.comap TensorProduct.includeLeftRingHom at ht
  change t ∉ (P.asIdeal.comap e.toRingHom).comap TensorProduct.includeLeftRingHom at ht
  rw [Ideal.comap_comap, he] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- Regular equations for a flat finitely presented quotient lift from its fibre
local ring to a principal neighbourhood of the original prime.

Source: Stacks Project, Divisors, Tag 063W(2)
(blueprint: lem-pur-flat-quotient-fiber-regular-sequence).

Proof: Lift the finite regular list in the fibre local ring to elements of I,
clearing denominators outside P. Such denominators are units, so regularity and
the prefix ideals are unchanged. Since A/I is R-flat, tensoring the kernel
sequence identifies the fibre ideal with I tensor the residue field. Nakayama
on the finite module I modulo the lifts shows generation at Q. Clear finitely
many denominators to make generation hold on a principal neighbourhood of Q.
The fibre algebra is Noetherian, since A is finitely presented over R. Spread
the regular list from its local ring to a principal fibre neighbourhood. A fibre
shrinking element is a fraction with numerator in A and denominator from R
outside p; invert its numerator in A. Induct on the list: each prefix quotient
is flat and finitely presented over R. The next equation is regular on its
fibre, so the fibre-Cartier criterion gives a further neighbourhood where it
is regular and its quotient is R-flat. Earlier injections survive localization.
Lift each new denominator to A and multiply with the previous denominator;
Q is retained. The final quotient has the retained prime, so is nonzero.
Transport the result to any model of the principal localization using its
canonical A-algebra equivalence. -/
theorem exists_regularSequence_of_flat_quotient_fiber
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [FinitePresentation R A]
    (I : Ideal A) (hI : I.FG) [Module.Flat R (A ⧸ I)]
    (p : PrimeSpectrum R) (Q : PrimeSpectrum A)
    (P : PrimeSpectrum (p.asIdeal.Fiber A))
    (hP : P.comap TensorProduct.includeRight.toRingHom = Q)
    (hfiber : ∃ f : List (Localization.AtPrime P.asIdeal),
      RingTheory.Sequence.IsRegular (Localization.AtPrime P.asIdeal) f ∧
        (I.map TensorProduct.includeRight.toRingHom).map
          (algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal)) =
            Ideal.ofList f) :
    ∃ g : A, g ∉ Q.asIdeal ∧
      ∀ (D : Type u) [CommRing D] [Algebra A D] [IsLocalization.Away g D],
        ∃ f : List D, RingTheory.Sequence.IsRegular D f ∧
          I.map (algebraMap A D) = Ideal.ofList f := by
  classical
  let F := p.asIdeal.Fiber A
  let L := Localization.AtPrime P.asIdeal
  let α : A →+* L := (algebraMap F L).comp TensorProduct.includeRight.toRingHom
  obtain ⟨xs, hxs, hgen⟩ := hfiber
  obtain ⟨fs, hfsI, hrel⟩ := exists_list_lifts p I P xs
    (fun x hx ↦ hgen.symm ▸ Ideal.subset_span hx)
  have hrel' : List.Forall₂ (fun x y ↦ ∃ u : L, IsUnit u ∧ y = u * x)
      xs (fs.map α) := List.forall₂_map_right_iff.mpr hrel
  have hreg : RingTheory.Sequence.IsRegular L (fs.map α) :=
    regular_of_unit_multiples hrel' hxs
  have hgen' : (I.map TensorProduct.includeRight.toRingHom).map
      (algebraMap F L) = (Ideal.ofList fs).map α := by
    rw [Ideal.map_ofList, ← ofList_eq_of_unit_multiples hrel']
    exact hgen
  have hJI : Ideal.ofList fs ≤ I := Ideal.span_le.mpr hfsI
  obtain ⟨t, ht, hmul⟩ := exists_multiplier_of_right_fiber_generators R A I
    (Ideal.ofList fs) hI hJI p P (by
      simpa only [Ideal.map_map] using hgen'.le)
  rw [hP] at ht
  have hIQ : I ≤ Q.asIdeal := by
    have hproper : (I.map TensorProduct.includeRight.toRingHom).map
        (algebraMap F L) ≠ ⊤ := by
      rw [hgen', Ideal.map_ofList]
      have hp : ⊤ ≠ Ideal.ofList (fs.map α) := by
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hreg.top_ne_smul
      exact hp.symm
    have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint P.asIdeal.primeCompl
      L (I.map TensorProduct.includeRight.toRingHom)).mp hproper
    intro a ha
    rw [← hP]
    by_contra hna
    apply Set.disjoint_left.mp hd _ (Ideal.mem_map_of_mem _ ha)
    change TensorProduct.includeRight a ∉ P.asIdeal
    change a ∉ (P.comap TensorProduct.includeRight.toRingHom).asIdeal
    exact hna
  obtain ⟨g, hg, hgreg⟩ := exists_isRegular_of_fiber_local R A p Q P hP fs hreg
  let B := Localization.Away g
  let C := Localization.Away (algebraMap A B t)
  let : AddCommGroup C := (inferInstance : CommRing C).toAddCommGroup
  have : IsLocalization.Away (g * t) C := inferInstance
  have hproper : I.map (algebraMap A C) ≠ ⊤ := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers (g * t))
      C I).mpr
    apply Set.disjoint_left.mpr
    intro a ha haI
    obtain ⟨n, rfl⟩ := ha
    exact (Q.asIdeal.primeCompl.mul_mem hg ht)
      (Ideal.IsPrime.mem_of_pow_mem Q.isPrime n (hIQ haI))
  have hgenC : I.map (algebraMap A C) = (Ideal.ofList fs).map (algebraMap A C) := by
    apply le_antisymm _ (Ideal.map_mono hJI)
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hu : IsUnit (algebraMap A C t) := by
      rw [IsScalarTower.algebraMap_apply A B C]
      exact IsLocalization.Away.algebraMap_isUnit _
    change algebraMap A C a ∈ (Ideal.ofList fs).map (algebraMap A C)
    apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (hmul a ha)
  have hweak : RingTheory.Sequence.IsWeaklyRegular C (fs.map (algebraMap A C)) := by
    have hw := hgreg.toIsWeaklyRegular.of_isLocalization C
      (Submonoid.powers (algebraMap A B t))
    rw [List.map_map] at hw
    have heq : (algebraMap B C) ∘ (algebraMap A B) = algebraMap A C := by
      funext a
      exact (IsScalarTower.algebraMap_apply A B C a).symm
    rw [heq] at hw
    exact hw
  have hregC : RingTheory.Sequence.IsRegular C (fs.map (algebraMap A C)) := by
    refine ⟨hweak, ?_⟩
    simpa only [← Ideal.map_ofList, ← hgenC, Ideal.smul_eq_mul,
      Ideal.mul_top] using hproper.symm
  refine ⟨g * t, Q.asIdeal.primeCompl.mul_mem hg ht, fun D _ _ _ ↦ ?_⟩
  let e := IsLocalization.algEquiv (Submonoid.powers (g * t)) C D
  refine ⟨(fs.map (algebraMap A C)).map e, ?_, ?_⟩
  · exact (e.toRingEquiv.toAddEquiv.isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
        (fun x _ y ↦ e.map_mul x y)))).mp hregC
  · change I.map (algebraMap A D) =
      Ideal.ofList ((fs.map (algebraMap A C)).map e.toRingHom)
    rw [← Ideal.map_ofList, ← Ideal.map_ofList, ← hgenC, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm

end Algebra
