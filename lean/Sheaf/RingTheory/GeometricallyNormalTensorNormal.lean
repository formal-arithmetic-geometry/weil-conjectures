/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.RingTheory.FilteredColimitNormalRing
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Sheaf.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Algebra.Field.ULift
import Sheaf.FieldTheory.SeparableSmoothColimit
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Tensor products of geometrically normal and normal algebras

Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem normal_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

private theorem normal_localization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.comap_isPrime (algebraMap R S) q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (Localization.AtPrime q)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_tensor_localization_right
    {k A B B' : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing B']
    [Algebra k A] [Algebra k B] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
    (M : Submonoid B) [IsLocalization M B']
    (h : ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (A ⊗[k] B')) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra (A ⊗[k] B) (A ⊗[k] B') :=
    (TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B B')).toAlgebra
  have : IsScalarTower A (A ⊗[k] B) (A ⊗[k] B') :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k A M B'
    (by ext; rfl)
  exact normal_localization (M.map (TensorProduct.includeRight (R := k) (A := A))) h

private theorem normal_tensor_localization_left
    {k A A' B : Type*} [CommRing k] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra k A] [Algebra k A'] [Algebra k B] [Algebra A A'] [IsScalarTower k A A']
    (M : Submonoid A) [IsLocalization M A']
    (h : ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (A' ⊗[k] B)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  have h' := normal_equiv (TensorProduct.comm k A B).toRingEquiv h
  exact normal_equiv (TensorProduct.comm k B A').toRingEquiv
    (normal_tensor_localization_right M h')

private theorem normal_atPrime_of_localization {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (p : Ideal R) [hp : p.IsPrime]
    (hdisj : Disjoint (M : Set R) (p : Set R))
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let q := p.map (algebraMap R S)
  let : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S p hp hdisj
  have hcontract : q.comap (algebraMap R S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M S hp hdisj
  obtain ⟨hd, hi⟩ := hS q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hcontract] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q)
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_tensor_of_normal_localizations_right
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (h : ∀ (q : Ideal B) [q.IsPrime],
      ∀ (r : Ideal (A ⊗[k] Localization.AtPrime q)) [r.IsPrime],
        IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
  intro r hr
  let q := r.comap (TensorProduct.includeRight (R := k) (A := A)).toRingHom
  let : q.IsPrime := Ideal.comap_isPrime _ r
  let B' := Localization.AtPrime q
  let : Algebra (A ⊗[k] B) (A ⊗[k] B') :=
    (TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B B')).toAlgebra
  have : IsScalarTower A (A ⊗[k] B) (A ⊗[k] B') :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k A q.primeCompl B'
    (by ext; rfl)
  apply normal_atPrime_of_localization
    (q.primeCompl.map (TensorProduct.includeRight (R := k) (A := A))) r _ (h q)
  rw [Set.disjoint_left]
  rintro x ⟨b, hb, rfl⟩ hx
  exact hb hx

private theorem normal_tensor_of_normal_localizations_left
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (h : ∀ (p : Ideal A) [p.IsPrime],
      ∀ (r : Ideal (Localization.AtPrime p ⊗[k] B)) [r.IsPrime],
        IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
  apply normal_equiv (TensorProduct.comm k B A).toRingEquiv
  apply normal_tensor_of_normal_localizations_right
  intro p hp
  exact normal_equiv (TensorProduct.comm k (Localization.AtPrime p) B).toRingEquiv (h p)

private theorem normal_of_geometric
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (h : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let e := (TensorProduct.congr ((AlgEquiv.refl : A ≃ₐ[k] A))
    (ULift.algEquiv : ULift.{max v w} k ≃ₐ[k] k)).trans (TensorProduct.rid k k A)
  exact normal_equiv e.toRingEquiv (h (ULift.{max v w} k))

open CategoryTheory CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem normal_tensor_of_directed_cover_left
    {k : Type u} {R B : Type (max u v)} [CommRing k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra k B]
    (P : Set (Subalgebra k R)) (hne : P.Nonempty)
    (hdir : DirectedOn (· ≤ ·) P) (hcover : ∀ x : R, ∃ A ∈ P, x ∈ A)
    (hnormal : ∀ A ∈ P, ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (R ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  let I := {A : Subalgebra k R // A ∈ P}
  have : Nonempty I := hne.to_subtype
  have : IsDirectedOrder I := ⟨fun i j ↦ by
    obtain ⟨A, hA, hi, hj⟩ := hdir i.1 i.2 j.1 j.2
    exact ⟨⟨A, hA⟩, hi, hj⟩⟩
  let inc {i j : I} (h : i ≤ j) : i.1 →ₐ[k] j.1 := Subalgebra.inclusion h
  let val (i : I) : i.1 →ₐ[k] R := i.1.val
  let F : I ⥤ CommRingCat.{max u v} :=
    { obj i := CommRingCat.of (i.1 ⊗[k] B)
      map {i j} f := CommRingCat.ofHom
        (Algebra.TensorProduct.map (inc (leOfHom f)) (AlgHom.id k B)).toRingHom
      map_id i := by ext <;> rfl
      map_comp f g := by ext <;> rfl }
  let U : Cocone F :=
    { pt := CommRingCat.of (R ⊗[k] B)
      ι :=
        { app i := CommRingCat.ofHom
            (Algebra.TensorProduct.map (val i) (AlgHom.id k B)).toRingHom
          naturality {i j} f := by ext <;> rfl } }
  have hsup : ⨆ i : I, i.1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨A, hA, hx⟩ := hcover x
    exact Algebra.mem_iSup_of_mem ⟨A, hA⟩ hx
  have hU : IsColimit U := by
    apply IsColimit.ofExistsUnique
    intro c
    let left (i : I) : i.1 →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeLeftRingHom
    let right (i : I) : B →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeRight.toRingHom
    have hleft {i j : I} (h : i ≤ j) (x : i.1) :
        left j (inc h x) = left i x := by
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (x ⊗ₜ[k] 1)
      simpa [F, left] using hh
    have hright {i j : I} (h : i ≤ j) : right i = right j := by
      ext b
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (1 ⊗ₜ[k] b)
      simpa [F, right] using hh.symm
    have hright_all (i j : I) : right i = right j := by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact (hright hik).trans (hright hjk).symm
    let i0 : I := Classical.arbitrary I
    let b : B →+* c.pt := right i0
    have hb (i : I) : b = right i := hright_all i0 i
    let : Algebra k c.pt := (b.comp (algebraMap k B)).toAlgebra
    let bAlg : B →ₐ[k] c.pt := { b with commutes' := fun _ ↦ rfl }
    let leftAlg (i : I) : i.1 →ₐ[k] c.pt :=
      { toRingHom := left i
        commutes' := by
          intro a
          change left i (algebraMap k i.1 a) = b (algebraMap k B a)
          rw [hb i]
          exact congrArg (c.ι.app i).hom
            (RingHom.congr_fun TensorProduct.includeLeftRingHom_comp_algebraMap a) }
    let rAlg : R →ₐ[k] c.pt :=
      (Subalgebra.iSupLift (fun i : I ↦ i.1) (Subtype.mono_coe _).directed_le
        leftAlg (fun i j hij ↦ AlgHom.ext (fun x ↦ (hleft hij x).symm))
        ⊤ hsup.ge).comp Subalgebra.topEquiv.symm.toAlgHom
    let r := rAlg.toRingHom
    have hr (i : I) (x : i.1) : r (x : R) = left i x := by
      have he : Subalgebra.topEquiv.symm.toAlgHom (i.1.val x) =
          Subalgebra.inclusion (le_top : i.1 ≤ ⊤) x := Subtype.ext rfl
      change (Subalgebra.iSupLift (fun i : I ↦ i.1) (Subtype.mono_coe _).directed_le
        leftAlg (fun i j hij ↦ AlgHom.ext (fun x ↦ (hleft hij x).symm)) ⊤ hsup.ge)
        (Subalgebra.topEquiv.symm.toAlgHom (i.1.val x)) = left i x
      rw [he, Subalgebra.iSupLift_inclusion]
      rfl
    let m : U.pt ⟶ c.pt := CommRingCat.ofHom
      (Algebra.TensorProduct.lift rAlg bAlg (fun _ _ ↦ Commute.all _ _)).toRingHom
    have hm (i : I) : U.ι.app i ≫ m = c.ι.app i := by
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext
      · ext x
        change r (val i x) * b 1 = (c.ι.app i).hom (x ⊗ₜ[k] 1)
        rw [map_one, mul_one]
        exact hr i x
      · ext x
        change r 1 * b x = (c.ι.app i).hom (1 ⊗ₜ[k] x)
        rw [map_one, one_mul, hb i]
        rfl
    refine ⟨m, hm, ?_⟩
    intro n hn
    apply CommRingCat.hom_ext
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      obtain ⟨A, hA, hx⟩ := hcover x
      let i : I := ⟨A, hA⟩
      have hh := ConcreteCategory.congr_hom ((hn i).trans (hm i).symm)
        ((⟨x, hx⟩ : i.1) ⊗ₜ[k] (1 : B))
      exact hh
    · ext x
      have hh := ConcreteCategory.congr_hom ((hn i0).trans (hm i0).symm)
        ((1 : i0.1) ⊗ₜ[k] x)
      exact hh
  let : HasColimit F := ⟨⟨U, hU⟩⟩
  let e := CategoryTheory.Iso.commRingCatIsoToRingEquiv
    (colimit.isoColimitCocone ⟨U, hU⟩)
  exact normal_equiv e
    (CommRingCat.isNormal_of_filtered_colimit F (fun i ↦ hnormal i.1 i.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem normal_subalgebra_extension
    {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsDomain R] [IsIntegrallyClosed R] (C : Subalgebra k R) (hC : C.FG) :
    ∃ A : Subalgebra k R, C ≤ A ∧ A.FG ∧ IsIntegrallyClosed A := by
  classical
  let K := FractionRing C
  let N := integralClosure C K
  have : Algebra.FiniteType k C := (Subalgebra.fg_iff_finiteType C).mp hC
  have : Module.Finite C N := Algebra.FiniteType.finite_integralClosure k K K
  have : Algebra.FiniteType k N :=
    Algebra.FiniteType.trans (R := k) (S := C) (A := N)
      (inferInstanceAs (Algebra.FiniteType k C))
      (inferInstanceAs (Algebra.FiniteType C N))
  have : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let L := FractionRing R
  let fC : C →ₐ[C] L := Algebra.ofId C L
  have hk : Function.Injective fC :=
    (IsFractionRing.injective R L).comp Subtype.val_injective
  let l : K →ₐ[C] L := IsFractionRing.liftAlgHom hk
  let j : N →ₐ[C] L := l.comp N.val
  let r : R →ₐ[k] L := IsScalarTower.toAlgHom k R L
  have hr : Function.Injective r := IsFractionRing.injective R L
  have hjmem : ∀ n : N, j n ∈ r.range := by
    intro n
    apply (AlgHom.mem_range r).mpr
    have hn : IsIntegral C (j n) := n.property.map l
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hn.tower_top (A := R))
  let q : N →ₐ[k] r.range := (j.restrictScalars k).codRestrict r.range hjmem
  let h : N →ₐ[k] R := (AlgEquiv.ofInjective r hr).symm.toAlgHom.comp q
  have hh : ∀ n : N, r (h n) = j n := by
    intro n
    change r ((AlgEquiv.ofInjective r hr).symm (q n)) = j n
    have he := (AlgEquiv.ofInjective r hr).apply_symm_apply (q n)
    exact congrArg Subtype.val he
  have hinj : Function.Injective h := by
    intro x y hxy
    apply Subtype.ext
    apply l.toRingHom.injective
    exact (hh x).symm.trans ((congrArg r hxy).trans (hh y))
  refine ⟨h.range, ?_, ?_, ?_⟩
  · intro x hx
    let c : C := ⟨x, hx⟩
    refine (AlgHom.mem_range h).mpr ⟨algebraMap C N c, ?_⟩
    apply hr
    rw [hh]
    rw [j.commutes]
    rfl
  · have : Algebra.FiniteType k h.range :=
      Algebra.FiniteType.of_surjective h.rangeRestrict h.rangeRestrict_surjective
    exact (Subalgebra.fg_iff_finiteType h.range).mpr inferInstance
  · exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective h hinj).toRingEquiv

private theorem normal_reduced {R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsReduced R := by
  apply isReduced_ofLocalizationMaximal
  intro p hp
  let : p.IsMaximal := hp
  let : IsDomain (Localization.AtPrime p) := (hR p).1
  infer_instance

private theorem separable_of_geometric_normal
    {k : Type u} {K : Type (max u v)} [Field k] [Field K] [Algebra k K]
    (hK : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
      ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsSeparableExtension k K := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hz
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    exact isSeparableExtension_of_forall_isReduced_tensorProduct k K (ringChar k)
      (fun E _ _ ↦ normal_reduced (hK E))
  · have : CharZero k := by
      let : CharP k 0 := hz ▸ inferInstance
      exact CharP.charP_to_charZero k
    intro F hF
    let : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
    exact ⟨(s : Set F), hs, hsep⟩

private theorem normal_tensor_of_separable_field
    {k : Type u} {K B : Type (max u v)} [Field k] [Field K] [CommRing B]
    [Algebra k K] [Algebra k B] (hsep : IsSeparableExtension k K)
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (K ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨hne, hdir, hcover, _⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
  apply normal_tensor_of_directed_cover_left
    {D : Subalgebra k K | Smooth k D ∧ D.FG}
  · obtain ⟨D⟩ := hne
    exact ⟨D.1, D.2⟩
  · intro D hD E hE
    obtain ⟨F, hDF, hEF⟩ := hdir ⟨D, hD⟩ ⟨E, hE⟩
    exact ⟨F.1, F.2, hDF, hEF⟩
  · intro x
    obtain ⟨D, hx⟩ := hcover x
    exact ⟨D.1, D.2, hx⟩
  · intro D hD
    let : Smooth k D := hD.1
    have hn := RingHom.Smooth.isNormalRing
      (RingHom.smooth_algebraMap.mpr (inferInstance : Smooth B (B ⊗[k] D))) hB
    exact normal_equiv (TensorProduct.comm k B D).toRingEquiv hn

private theorem tensor_map_injective
    {k A A' B B' : Type*} [Field k] [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra k A] [Algebra k A']
    [Algebra k B] [Algebra k B'] (f : A →ₐ[k] A') (g : B →ₐ[k] B')
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  exact _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

private theorem finite_minimalPrimes_tensor
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [FiniteType k B] :
    (minimalPrimes (A ⊗[k] B)).Finite := by
  let K := FractionRing A
  let f : A ⊗[k] B →ₐ[k] K ⊗[k] B :=
    TensorProduct.map (IsScalarTower.toAlgHom k A K) (AlgHom.id k B)
  have hf : Function.Injective f := tensor_map_injective _ _
    (IsFractionRing.injective A K) Function.injective_id
  have : IsNoetherianRing (K ⊗[k] B) := FiniteType.isNoetherianRing K _
  have hs := (minimalPrimes.finite_of_isNoetherianRing (K ⊗[k] B)).image
    (Ideal.comap f.toRingHom)
  apply hs.subset
  intro p hp
  apply Ideal.minimalPrimes_comap_subset f.toRingHom (⊥ : Ideal (K ⊗[k] B))
  rw [Ideal.comap_bot_of_injective f.toRingHom hf]
  exact hp

private theorem normal_tensor_domain_of_finiteType
    {k : Type u} {A B : Type (max u v)} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain B] [IsIntegrallyClosed B]
    (hfinite : ∀ (D : Subalgebra k B), D.FG → IsIntegrallyClosed D →
      ∀ (p : Ideal (A ⊗[k] D)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  apply normal_equiv (TensorProduct.comm k B A).toRingEquiv
  apply normal_tensor_of_directed_cover_left {D : Subalgebra k B | D.FG ∧ IsIntegrallyClosed D}
  · obtain ⟨D, hD, hfg, hn⟩ :=
      normal_subalgebra_extension (⊥ : Subalgebra k B) Subalgebra.fg_bot
    exact ⟨D, hfg, hn⟩
  · intro D hD E hE
    obtain ⟨F, hF, hfg, hn⟩ := normal_subalgebra_extension (D ⊔ E) (hD.1.sup hE.1)
    exact ⟨F, ⟨hfg, hn⟩, le_sup_left.trans hF, le_sup_right.trans hF⟩
  · intro x
    have hxfg : (Algebra.adjoin k ({x} : Set B)).FG :=
      Subalgebra.fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩
    obtain ⟨D, hD, hfg, hn⟩ := normal_subalgebra_extension (Algebra.adjoin k {x}) hxfg
    exact ⟨D, ⟨hfg, hn⟩, hD (Algebra.subset_adjoin (Set.mem_singleton x))⟩
  · intro D hD
    exact normal_equiv (TensorProduct.comm k A D).toRingEquiv (hfinite D hD.1 hD.2)

private theorem integral_mem_normal_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R)
    (hn : ∀ (p : Ideal S) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (f : S →ₐ[R] FractionRing R) (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ y : S, f y = x := by
  let : Algebra S (FractionRing R) := f.toRingHom.toAlgebra
  have : IsScalarTower R S (FractionRing R) :=
    .of_algebraMap_eq <| fun r ↦ (f.commutes r).symm
  have : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization M S (FractionRing R) hM
  have : IsIntegrallyClosed S := (isIntegrallyClosed_iff (FractionRing S)).mpr
    (fun {y} hy ↦ integral_totalFraction_mem_range_of_normal S hn y hy)
  exact (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance (hx.tower_top (A := S))

/-- Normality of the tensor product in the domain case.

Source: Stacks Project, Algebra, Tag 06DF, domain reduction and finite-type/colimit argument.
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal-domain-case)

The proof reduces to finite-type normal subalgebras of the second domain, proves the finite-type
case using separability of the fraction field and smooth normality, and descends through the
filtered tensor-product colimit. The remaining algebraic intersection and total-fraction-ring
argument is isolated here for a subsequent worker; the theorem is strictly stronger in its
hypotheses than the target because both algebras are assumed normal domains.
-/
theorem normal_domain_case
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain B] [IsIntegrallyClosed B]
    (hA : ∀ (E : Type*) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

/-- If `A` is geometrically normal over a field `k` and `B` is normal, then
`A ⊗[k] B` is normal, with normality expressed at every prime localization.
Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).

Proof (the eleven steps of the DAG node):

1. We first record two elementary consequences of the normal-ring definition, to be used below. If
   R is normal and T is multiplicative, a prime Q of T^{-1}R contracts to a prime p of R disjoint
   from T, and (T^{-1}R)_Q = R_p: the mutually inverse fraction maps send (r/t)/(u/v) to rv/(tu),
   and r/s to (r/1)/(s/1). Thus T^{-1}R is normal. Also R is reduced: for a nonzero nilpotent x
   choose a maximal ideal p containing its proper annihilator. Then x/1 is nonzero in R_p
   (otherwise some s outside p annihilates x) and nilpotent, contradicting that R_p is a domain.
   These arguments include the zero ring, which has no primes.

2. Geometric normality is preserved by localization: for each extension E/k, the tensor product of
   a localization of A with E is the localization of A tensor E at the images of the same
   denominators, by [lem-weil-pbc-localization-base-change], applied with R=A, R'=T^{-1}A and D=A
   tensor_k E. The identification (A tensor_k E) tensor_A T^{-1}A = T^{-1}A tensor_k E sends (a
   tensor e) tensor(a'/t) to (aa'/t) tensor e; its inverse sends (a/t) tensor e to (1 tensor e)
   tensor(a/t). Bilinearity and the A-balancing relation verify that these maps are well-defined
   inverse ring maps. The swap sends a tensor e to e tensor a and is inverse to itself, by the
   tensor universal property. Step 1 gives normality of this localization. In particular A is
   normal by E=k, and every A_p is geometrically normal.

3. Fix a prime r of A tensor_k B, and let p and q be its contractions to A and B. The images of A
   minus p and B minus q avoid r. Apply the maps of Step 2 with E replaced by B, then interchange
   the factors and apply them with A replaced by B and E replaced by A_p. Twice applying [lem-
   weil-pbc-localization-base-change] therefore identifies A_p tensor_k B_q with the localization
   of A tensor_k B obtained by inverting these images. Localizing once more at the prime induced
   by r gives exactly (A tensor_k B)_r, by the fraction formulas in Step 1. A_p and B_q are normal
   domains by the hypotheses and Step 2, and A_p is geometrically normal. It therefore suffices to
   prove normality of A tensor_k B when A and B are normal domains and A is geometrically normal.
   If either original algebra is zero there is no r and the conclusion is vacuous. For the
   remainder of the proof A and B denote these domains; write K=Frac(A) and L=Frac(B).

4. For any finitely generated k-subalgebra D of B, apply [lem-fin-normalization-extension-finite]
   to X=Spec D and the degree-one extension Frac(D)/Frac(D). By [def-fin-normalization-extension]
   its source is Spec N, where N is the integral closure of D in Frac(D). The finite-morphism
   definition makes N finite as a D-module. By [lem-weil-pbc-integral-closure-algebraic-extension-
   normal], N is an integrally closed domain with fraction field Frac(D). Embed Frac(D) into L
   using D subset B. Every element of N is integral over D, hence over B by the same monic
   equation, and belongs to B by [lem-weil-pbc-normal-ring-integrally-closed-total] applied to the
   domain B. Thus N is a normal k-subalgebra of B containing D; normality of all its prime
   localizations follows from [lem-weil-pbc-localization-normal-domain]. It is finite type over k:
   if d_1,...,d_h generate D as a k-algebra and n_1,...,n_m generate N as a D-module, these
   elements together generate N as a k-algebra. Consequently the collection I of all normal
   finite-type k-subalgebras of B is nonempty, covers B, and is directed: for two members take D
   generated by the union of their finite generating sets and perform this construction. I is a
   set of subalgebras, hence a small directed poset after choosing the universe of k,A,B.

5. The inclusions A tensor_k B_i into A tensor_k B, for B_i in I, exhibit the latter as their
   filtered colimit of rings. Indeed tensoring an inclusion over k is injective by [lem-weil-pbc-
   module-over-field-flat] and the injectivity definition of flatness. Every tensor is a finite
   sum of pure tensors and all its B-coordinates lie in one B_i. For a compatible family of ring
   maps out of A tensor_k B_i, define its value on an element using any stage containing that
   element; a common upper stage proves independence, addition and multiplication, and uniqueness
   follows from the union. This proves the colimit universal property [def-weil-pbc-category-
   colimit]. By [lem-weil-pbc-filtered-colimit-normal-ring], it suffices to prove the domain case
   with B finite type over k. The rest of the proof establishes precisely that case; Step 11 then
   returns to the original algebras.

6. Assume henceforth that B is finite type. By Step 2, K is geometrically normal, so K tensor_k E
   is reduced for every field extension E/k by Step 1. If k has positive characteristic, apply
   [lem-weil-pbc-geometrically-reduced-extension-separable]; if k has characteristic zero, apply
   [lem-weil-pbc-char-zero-field-extension-separable]. In either case K/k is separable in the
   sense that every finitely generated intermediate field K_i/k is separably generated. These K_i
   form a small nonempty directed poset and their union is K: the subfield generated by the union
   of two finite sets contains the corresponding two intermediate fields.

7. For each K_i, [lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra] supplies a
   smooth k-subalgebra D_i of K_i with fraction field K_i. By [lem-weil-pbc-smooth-ring-map-base-
   change-composition], B tensor_k D_i is smooth over B. It is normal by [lem-weil-pbc-smooth-
   over-normal-ring-normal], since B is normal. The explicit maps of Step 2, with A=D_i and E=B,
   and the factor swap identify B tensor_k K_i with its localization at the nonzero elements of
   D_i, so Step 1 makes B tensor_k K_i normal. Swap factors to obtain normality of K_i tensor_k B.
   Field-flatness makes each K_i tensor_k B inject into K tensor_k B. Every element is a finite
   sum of pure tensors, whose finitely many K-coordinates lie in one K_i. Given compatible ring
   maps from these stages, evaluate an element at any stage containing it. A common larger
   intermediate field proves independence of the chosen stage and preservation of addition and
   multiplication; coverage proves uniqueness. This verifies that K tensor_k B is their filtered
   colimit. Thus [lem-weil-pbc-filtered-colimit-normal-ring] proves that K tensor_k B is normal.
   Independently, A tensor_k L is normal by the original geometric-normality hypothesis, since L/k
   is a field extension.

8. Put C=A tensor_k B, C_A=K tensor_k B and C_B=A tensor_k L. The maps C to C_A and C to C_B are
   injective: tensor the inclusions A subset K and B subset L over the field k, using the flatness
   statement and definition. They are localizations by [lem-weil-pbc-localization-base-change].
   Their inverted elements are nonzerodivisors of C: multiplication by any nonzero a in A, or b in
   B, is injective before tensoring and remains injective afterward. By Step 7, C_A and C_B are
   normal, hence reduced by Step 1; therefore their subring C is reduced. C_A is finite type over
   K, generated by the same finitely many B-generators, so it is Noetherian by [lem-weil-pbc-
   finite-type-algebra-noetherian] (a field has only two ideals). It has finitely many minimal
   primes by [lem-weil-pbc-noetherian-finitely-many-minimal-primes].

9. The map A to C is flat. For an injection of A-modules M to N, the identification M tensor_A C =
   M tensor_k B (m tensor(a tensor b) maps to am tensor b, with inverse m tensor b maps to m
   tensor(1 tensor b)) identifies the induced map with tensoring the underlying injection of
   k-vector spaces by B. This is injective by field-flatness. For a minimal prime r of C, going
   down [lem-sc-flat-going-down] applied to (0) subset r intersect A yields a prime r' subset r
   contracting to (0). Minimality forces r'=r. Hence every minimal prime of C avoids A minus zero.
   Such primes extend injectively to minimal primes of C_A: extension and contraction are inverse,
   since a fraction c/s belongs to the extended prime exactly when c belongs to the original
   prime; any prime strictly below the extended prime would contract to a strictly smaller prime
   of C. Thus C has finitely many minimal primes by Step 8.

10. Both C_A and C_B embed in Q(C), since their denominators are nonzerodivisors of C. Moreover
   Q(C_A)=Q(C)=Q(C_B): localizing at a subset of the nonzerodivisors preserves nonzerodivisors,
   and if c/s is a nonzerodivisor in this localization, c is already a nonzerodivisor in C, since
   localization at nonzerodivisors is injective. Also K tensor_k L embeds in Q(C), by inverting
   both sets of denominators. Inside this ring C_A intersect C_B=C. To check the equality, split
   K=A direct-sum U and L=B direct-sum V as k-vector spaces: choose a basis of K/A and lift it to
   K to obtain U, and do the same for L/B; vector-space bases exist by [lem-weil-pbc-module-over-
   field-flat]. Bilinearity gives K tensor L=(A tensor B) direct-sum (U tensor B) direct-sum (A
   tensor V) direct-sum (U tensor V); the projections to these four summands are induced by the
   projections of the split vector spaces. C_A comprises the first two summands and C_B the first
   and third, so their intersection is the first summand. Now let x in Q(C) be integral over C.
   Its monic equation is also a monic equation over C_A and C_B. By [lem-weil-pbc-normal-ring-
   integrally-closed-total] and Step 7, x belongs to both rings, hence to C. By [lem-weil-pbc-
   reduced-normal-iff-integrally-closed-total-fractions], reducedness and finiteness of the
   minimal primes from Steps 8 and 9 imply that C is normal.

11. Step 10 proves the normal-domain case for each finite-type normal B_i of Step 4, with the same
   geometrically normal A. Step 5 and the filtered-colimit normality theorem therefore prove the
   domain case for arbitrary B. Apply this domain case to A_p and B_q in Step 3 and then use the
   prime-localization calculation there: every (A tensor_k B)_r is an integrally closed domain.
   This is exactly normality of the original tensor product. No finite-type or Noetherian
   hypothesis survives the reductions, and no domain or nonzero hypothesis is imposed on the
   original A or B.
-/
theorem isNormal_tensorProduct_of_geometricallyNormal
    (k : Type u) (A : Type v) (B : Type w)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)    := by
  apply normal_tensor_of_normal_localizations_left
  intro p hp
  let A' := Localization.AtPrime p
  let : IsDomain A' := (normal_of_geometric hA p).1
  let : IsIntegrallyClosed A' := (normal_of_geometric hA p).2
  apply normal_tensor_of_normal_localizations_right
  intro q hq
  let B' := Localization.AtPrime q
  let : IsDomain B' := (hB q).1
  let : IsIntegrallyClosed B' := (hB q).2
  apply normal_domain_case
  · intro E _ _ r hr
    exact normal_tensor_localization_left (k := k) (A := A)
      (A' := Localization.AtPrime p) (B := E) p.primeCompl (hA E) r
  · exact normal_localization q.primeCompl hB

end Algebra
