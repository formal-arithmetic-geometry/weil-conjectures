/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.RingTheory.Localization.Ideal

/-!
# Local intersections and localization of an SNC root presentation

Source: Stacks Project, Etale, Tag 0BIA; Algebra, Tags 00CO, 00CP, 00CT, 00E3,
and 00FN; ILO Expose IX, Proposition 2.1, printed p.133.
(blueprint: lem-sfb-snc-root-local-presentation)

We enumerate the finite branch set by `Fin r` and write the simultaneous root quotient
directly using `MvPolynomial`. The equivalences are pinned on coefficients and coordinates.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem root_quotient_localization
    (A : Type u) [CommRing A] (r : ℕ) (t : Fin r → A) (n : ℕ)
    (p : Ideal A) [p.IsPrime] :
    let I := Ideal.span (Set.range (fun i : Fin r ↦
      (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))
    let R := Localization.AtPrime p
    let J := Ideal.span (Set.range (fun i : Fin r ↦
      (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ n -
        MvPolynomial.C (algebraMap A R (t i))))
    ∃ e : Localization (p.primeCompl.map (algebraMap A (MvPolynomial (Fin r) A ⧸ I))) ≃+*
        (MvPolynomial (Fin r) R ⧸ J),
      (∀ a : A, e (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
        (algebraMap A (MvPolynomial (Fin r) A ⧸ I) a)) =
          algebraMap R _ (algebraMap A R a)) ∧
      (∀ i : Fin r, e (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
        (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
          Ideal.Quotient.mk _ (MvPolynomial.X i)) := by
  classical
  let := MvPolynomial.algebraMvPolynomial (σ := Fin r) (R := A) (S := Localization.AtPrime p)
  dsimp only
  let R := Localization.AtPrime p
  let P := MvPolynomial (Fin r) A
  let S := MvPolynomial (Fin r) R
  let I : Ideal P := Ideal.span (Set.range (fun i : Fin r ↦
    MvPolynomial.X i ^ n - MvPolynomial.C (t i)))
  let J : Ideal S := Ideal.span (Set.range (fun i : Fin r ↦
    MvPolynomial.X i ^ n - MvPolynomial.C (algebraMap A R (t i))))
  have hIJ : I.map (algebraMap P S) = J := by
    dsimp only [I, J, P, S]
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    change MvPolynomial.map (algebraMap A R)
      (MvPolynomial.X i ^ n - MvPolynomial.C (t i)) = _
    simp only [map_sub, map_pow, MvPolynomial.map_X, MvPolynomial.map_C]
  let C := P ⧸ I
  let B := S ⧸ J
  let f : C →+* B := Ideal.quotientMap J (algebraMap P S)
    (Ideal.map_le_iff_le_comap.mp hIJ.le)
  let : Algebra C B := f.toAlgebra
  have hloc : IsLocalization (p.primeCompl.map (algebraMap A C)) B := by
    let e : (S ⧸ I.map (algebraMap P S)) ≃ₐ[P] B :=
      Ideal.quotientEquivAlgOfEq P hIJ
    let : Algebra C (S ⧸ I.map (algebraMap P S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have : IsLocalization
        ((p.primeCompl.map (MvPolynomial.C : A →+* P)).map (Ideal.Quotient.mk I))
        (S ⧸ I.map (algebraMap P S)) :=
      IsLocalization.of_surjective (p.primeCompl.map (MvPolynomial.C : A →+* P)) S
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk (I.map (algebraMap P S))) Ideal.Quotient.mk_surjective
        rfl (by rw [Ideal.mk_ker, Ideal.mk_ker])
    let ec : (S ⧸ I.map (algebraMap P S)) ≃ₐ[C] B :=
      { e.toRingEquiv with
        commutes' := by
          intro c
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
          rfl }
    convert IsLocalization.isLocalization_of_algEquiv
      ((p.primeCompl.map (MvPolynomial.C : A →+* P)).map (Ideal.Quotient.mk I)) ec using 1
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MvPolynomial.C a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  let := hloc
  let e := (IsLocalization.algEquiv
    (p.primeCompl.map (algebraMap A C))
    (Localization (p.primeCompl.map (algebraMap A C))) B).toRingEquiv
  refine ⟨e, ?_, ?_⟩
  · intro a
    change (IsLocalization.algEquiv _ _ B) (algebraMap C _ (algebraMap A C a)) = _
    rw [AlgEquiv.commutes]
    change Ideal.quotientMap J (algebraMap P S) _ (algebraMap A C a) = _
    rw [Ideal.quotientMap_algebraMap]
    change Ideal.Quotient.mk J (MvPolynomial.map (algebraMap A R) (MvPolynomial.C a)) = _
    rw [MvPolynomial.map_C]
    rfl
  · intro i
    change (IsLocalization.algEquiv _ _ B) (algebraMap C _ _) = _
    rw [AlgEquiv.commutes]
    change Ideal.Quotient.mk J ((algebraMap P S) (MvPolynomial.X i)) = _
    rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem prime_localization_of_equiv
    (C B : Type u) [CommRing C] [CommRing B] (M : Submonoid C)
    (e : Localization M ≃+* B) (q : Ideal C) [q.IsPrime]
    (hd : Disjoint (M : Set C) (q : Set C)) :
    ∃ (Q : Ideal B) (_hQ : Q.IsPrime),
      Q = q.map (e.toRingHom.comp (algebraMap C (Localization M))) ∧
      ∃ eq : Localization.AtPrime Q ≃+* Localization.AtPrime q,
        ∀ c : C, eq (Localization.mk (e (Localization.mk c 1)) 1) =
          Localization.mk c 1 := by
  let : Algebra C B := (e.toRingHom.comp (algebraMap C (Localization M))).toAlgebra
  have : IsLocalization M B :=
    (IsLocalization.isLocalization_iff_of_ringEquiv M e).mp inferInstance
  let Q := q.map (algebraMap C B)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hd
  have hq : Q.comap (algebraMap C B) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q) Q
    simpa only [hq] using h
  let eq := (IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime Q) (Localization.AtPrime q)).toRingEquiv
  refine ⟨Q, hQ, rfl, eq, ?_⟩
  intro c
  change (IsLocalization.algEquiv q.primeCompl _ _) (algebraMap C _ c) = _
  exact AlgEquiv.commutes _ c

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem root_localization_ext
    (A : Type u) [CommRing A] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) A))
    (p : Ideal A) [p.IsPrime]
    (B : Type u) [CommRing B]
    (e f : Localization (p.primeCompl.map (algebraMap A
      (MvPolynomial (Fin r) A ⧸ I))) ≃+* B)
    (hc : ∀ a : A, e (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
      (algebraMap A (MvPolynomial (Fin r) A ⧸ I) a)) =
      f (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
        (algebraMap A (MvPolynomial (Fin r) A ⧸ I) a)))
    (hx : ∀ i : Fin r, e (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
      (Ideal.Quotient.mk I (MvPolynomial.X i))) =
      f (algebraMap (MvPolynomial (Fin r) A ⧸ I) _
        (Ideal.Quotient.mk I (MvPolynomial.X i)))) : e = f := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (p.primeCompl.map (algebraMap A (MvPolynomial (Fin r) A ⧸ I)))
  apply RingHom.ext
  intro c
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  let C := MvPolynomial (Fin r) A ⧸ I
  let D := Localization (p.primeCompl.map (algebraMap A C))
  have h : (e.toRingHom.comp (algebraMap C D)).comp (Ideal.Quotient.mk I) =
      (f.toRingHom.comp (algebraMap C D)).comp (Ideal.Quotient.mk I) := by
    apply MvPolynomial.ringHom_ext
    · exact hc
    · exact hx
  exact DFunLike.congr_fun h x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem boundary_components_reindex
    {X : Scheme.{u}} (H : X.IdealSheafData) (r k : ℕ)
    (components : Fin r ≃ {Z : Set (H.support : Set X) //
      Z ∈ irreducibleComponents (H.support : Set X)})
    (C : Fin k → X.IdealSheafData)
    (hC : ∀ j, IsIntegral (C j).subscheme)
    (hcover : H.support = ⨆ j, (C j).support) :
    ∃ φ : Fin r ↪ Fin k, ∀ i,
      ((C (φ i)).support : Set X) = Subtype.val '' (components i).val := by
  classical
  let g (j : Fin k) : Set (H.support : Set X) :=
    Subtype.val ⁻¹' ((C j).support : Set X)
  have hsub (j : Fin k) : (C j).support ≤ H.support := by
    rw [hcover]
    exact le_iSup (fun j ↦ (C j).support) j
  have hg (j : Fin k) : IsIrreducible (g j) := by
    have := hC j
    let f : (C j).subscheme → (H.support : Set X) := fun z ↦
      ⟨(C j).subschemeι z, hsub j (by
        exact (show Set.range (C j).subschemeι ⊆ ((C j).support : Set X) from
          (Scheme.IdealSheafData.range_subschemeι _).le) (Set.mem_range_self z))⟩
    have hf : Continuous f :=
      (C j).subschemeι.continuous.subtype_mk _
    have hrange : f '' Set.univ = g j := by
      ext z
      constructor
      · rintro ⟨x, _, rfl⟩
        change (C j).subschemeι x ∈ (C j).support
        exact (show Set.range (C j).subschemeι ⊆ ((C j).support : Set X) from
          (Scheme.IdealSheafData.range_subschemeι _).le) (Set.mem_range_self x)
      · intro hz
        obtain ⟨x, hx⟩ := (show z.val ∈ Set.range (C j).subschemeι by
          rw [Scheme.IdealSheafData.range_subschemeι]
          exact hz)
        exact ⟨x, Set.mem_univ _, Subtype.ext hx⟩
    rw [← hrange]
    exact (IrreducibleSpace.isIrreducible_univ _).image f hf.continuousOn
  have hclosed (j : Fin k) : IsClosed (g j) :=
    (C j).support.isClosed.preimage continuous_subtype_val
  have hchoose (i : Fin r) : ∃ j, g j = (components i).val := by
    have hcov : (components i).val ⊆ ⋃₀ (↑(Finset.univ.image g) : Set (Set _)) := by
      intro z _
      have hz : z.val ∈ (⨆ j, (C j).support : TopologicalSpace.Closeds X) := by
        rw [← hcover]
        exact z.property
      have hz' : ∃ j, z.val ∈ (C j).support := by
        change z.val ∈ ((⨆ j, (C j).support : TopologicalSpace.Closeds X) : Set X) at hz
        let F : TopologicalSpace.Closeds X :=
          ⟨⋃ j, ((C j).support : Set X), isClosed_iUnion_of_finite fun j ↦
            (C j).support.isClosed⟩
        have hle : (⨆ j, (C j).support) ≤ F :=
          iSup_le fun j x hx ↦ Set.mem_iUnion.mpr ⟨j, hx⟩
        exact Set.mem_iUnion.mp (hle hz)
      obtain ⟨j, hj⟩ := hz'
      exact Set.mem_sUnion_of_mem hj (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    obtain ⟨s, hs, hZs⟩ := isIrreducible_iff_sUnion_isClosed.mp (components i).property.1
      (Finset.univ.image g) (by
        intro s hs
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        exact hclosed j) hcov
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨j, ((components i).property.2 (hg j) hZs).antisymm hZs⟩
  choose φ hφ using hchoose
  have hinj : Function.Injective φ := by
    intro i j hij
    apply components.injective
    apply Subtype.ext
    rw [← hφ i, ← hφ j, hij]
  refine ⟨⟨φ, hinj⟩, ?_⟩
  intro i
  rw [← hφ i]
  exact (Set.image_preimage_eq_inter_range.trans
    (Set.inter_eq_left.mpr fun x hx ↦ ⟨⟨x, hsub _ hx⟩, rfl⟩)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem spec_quotient_kernel
    (A : Type u) [CommRing A] (K : Ideal A) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker =
      Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  have h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk K) ≫
        (Scheme.ΓSpecIso (.of (A ⧸ K))).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  change RingHom.ker (((Scheme.ΓSpecIso (.of (A ⧸ K))).inv.hom).comp
    ((Ideal.Quotient.mk K).comp (Scheme.ΓSpecIso (.of A)).hom.hom)) = _
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ K))).inv).1,
    ← RingHom.comap_ker, Ideal.mk_ker]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem intersection_stalk_equiv
    (A : Type u) [CommRing A] (K : Ideal A)
    (D : (Spec (.of A)).IdealSheafData)
    (hD : D = Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso (.of A)).inv.hom))
    (z : D.subscheme) :
    let p := (D.subschemeι z).asIdeal
    Nonempty ((Localization.AtPrime p ⧸ K.map (algebraMap A (Localization.AtPrime p))) ≃+*
      D.subscheme.presheaf.stalk z) := by
  let X := Spec (.of A)
  let x := D.subschemeι z
  let p := x.asIdeal
  let e := (Spec.stalkIso (.of A) x).symm.commRingCatIsoToRingEquiv
  let f := (D.subschemeι.stalkMap z).hom.comp e.toRingHom
  have hf : Function.Surjective f :=
    (D.subschemeι.stalkMap_surjective z).comp e.surjective
  have hk : RingHom.ker f = K.map (algebraMap A (Localization.AtPrime p)) := by
    rw [← RingHom.comap_ker]
    rw [Scheme.Hom.ker_stalkMap D.subschemeι ⟨⊤, isAffineOpen_top X⟩ z trivial,
      Scheme.IdealSheafData.ker_subschemeι]
    have hid := congrArg (fun E : X.IdealSheafData ↦
      E.ideal ⟨⊤, isAffineOpen_top X⟩) hD
    rw [hid]
    rw [Scheme.IdealSheafData.ideal_top_ofIdealTop]
    rw [Ideal.map_map]
    have hs (L : Ideal (X.presheaf.stalk x)) :
        L.comap e.toRingHom = L.map e.symm.toRingHom := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective
        e.symm.toRingHom e.symm.surjective]
      constructor
      · intro ha
        exact ⟨e a, ha, e.symm_apply_apply a⟩
      · rintro ⟨b, hb, hab⟩
        change e.symm b = a at hab
        rw [← hab]
        change e (e.symm b) ∈ L
        exact (e.apply_symm_apply b).symm ▸ hb
    rw [hs]
    rw [Ideal.map_map]
    have he : e.symm.toRingHom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom) =
        algebraMap A (Localization.AtPrime p) := by
      change ((Spec.stalkIso (.of A) x).hom.hom).comp
        ((X.presheaf.germ ⊤ x trivial).hom.comp
          (Scheme.ΓSpecIso (.of A)).inv.hom) = _
      have hh := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of A) (x := x)
      apply RingHom.ext
      intro a
      have ha := ConcreteCategory.congr_hom hh a
      change e.symm ((X.presheaf.germ ⊤ x trivial)
        ((Scheme.ΓSpecIso (.of A)).inv a)) = _
      change e (algebraMap A (Localization.AtPrime p) a) =
        (X.presheaf.germ ⊤ x trivial) ((Scheme.ΓSpecIso (.of A)).inv a) at ha
      exact (congrArg e.symm ha).symm.trans (e.symm_apply_apply _)
    rw [he]
  exact ⟨(Ideal.quotEquivOfEq hk.symm).trans (f.quotientKerEquivOfSurjective hf)⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem snc_local_intersections
    (A : Type u) [CommRing A] (r : ℕ) (t : Fin r → A)
    (H : (Spec (.of A)).IdealSheafData) (hH : IsStrictNormalCrossingsBoundary H)
    (components : Fin r ≃ {Z : Set (H.support : Set (Spec (.of A))) //
      Z ∈ irreducibleComponents (H.support : Set (Spec (.of A)))})
    (hbranches : ∀ i : Fin r, (Ideal.span {t i}).IsPrime ∧
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t i})))) =
        Subtype.val '' (components i).val)
    (p : Ideal A) [p.IsPrime] (J : Finset (Fin r)) (hJ : ∀ j ∈ J, t j ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p ⧸ Ideal.span
      ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r)))) ∧
    ringKrullDim (Localization.AtPrime p ⧸ Ideal.span
      ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r)))) +
      (J.card : ℕ) = ringKrullDim (Localization.AtPrime p) := by
  classical
  obtain ⟨k, C, hinj, hC, hcover, hinter⟩ := hH.2.2
  obtain ⟨φ, hφ⟩ := boundary_components_reindex H r k components C
    (fun j ↦ (hC j).1) hcover
  let X := Spec (.of A)
  have hCi (i : Fin r) : C (φ i) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t i})))).ker := by
    have := (hC (φ i)).1
    have : (Ideal.span {t i}).IsPrime := (hbranches i).1
    have : IsDomain (A ⧸ Ideal.span {t i}) := inferInstance
    rw [← Scheme.IdealSheafData.ker_subschemeι (C (φ i)),
      Scheme.Hom.ker_eq_vanishingIdeal, Scheme.Hom.ker_eq_vanishingIdeal]
    congr 1
    apply TopologicalSpace.Closeds.ext
    change closure (Set.range (C (φ i)).subschemeι) =
      closure (Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {t i})))))
    rw [Scheme.IdealSheafData.range_subschemeι, hφ i, (hbranches i).2]
  let K : Ideal A := Ideal.span (t '' (J : Set (Fin r)))
  have hK : K = ⨆ j ∈ J, Ideal.span {t j} := by
    dsimp only [K]
    simp only [← Ideal.span_iUnion]
    congr 1
    ext a
    simp [eq_comm]
  let D := ⨆ i ∈ J.map φ, C i
  have hD : D = Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
    have he : D = ⨆ j ∈ J, C (φ j) := by
      apply le_antisymm
      · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
      · exact iSup_le fun j ↦ iSup_le fun hj ↦
          le_iSup_of_le (φ j) (le_iSup_of_le
            (Finset.mem_map.mpr ⟨j, hj, rfl⟩) le_rfl)
    rw [he]
    let E := (Scheme.IdealSheafData.equivOfIsAffine (X := X)).toOrderIso
    apply E.injective
    rw [E.map_iSup]
    simp_rw [E.map_iSup]
    have hi (i : Fin r) : E (C (φ i)) =
        (Ideal.span {t i}).map (Scheme.ΓSpecIso (.of A)).inv.hom := by
      change (C (φ i)).ideal ⟨⊤, isAffineOpen_top X⟩ = _
      rw [hCi, spec_quotient_kernel, Scheme.IdealSheafData.ideal_top_ofIdealTop]
    simp only [hi]
    change _ = (Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso (.of A)).inv.hom)).ideal ⟨⊤, isAffineOpen_top X⟩
    rw [Scheme.IdealSheafData.ideal_top_ofIdealTop, hK]
    simp only [Ideal.map_iSup]
  let x : X := ⟨p, inferInstance⟩
  have hx : x ∈ (D.support : Set X) := by
    have he : D = ⨆ j ∈ J, C (φ j) := by
      apply le_antisymm
      · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
      · exact iSup_le fun j ↦ iSup_le fun hj ↦
          le_iSup_of_le (φ j) (le_iSup_of_le
            (Finset.mem_map.mpr ⟨j, hj, rfl⟩) le_rfl)
    rw [he]
    simp only [Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf,
      Set.mem_iInter]
    intro j hj
    rw [hφ j, ← (hbranches j).2]
    change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {t j})))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    change Ideal.span {t j} ≤ p
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hJ j hj))
  obtain ⟨z, hz⟩ := (show x ∈ Set.range D.subschemeι by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx)
  have hc := hinter (J.map φ) z
  have hreg := hc.1.2
  have := hreg
  obtain ⟨e⟩ := intersection_stalk_equiv A K D hD z
  have heq : (D.subschemeι z).asIdeal = p := congrArg PrimeSpectrum.asIdeal hz
  have hquot : K.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) ''
        (J : Set (Fin r))) := by
    dsimp only [K]
    rw [Ideal.map_span, Set.image_image]
  have e' : (Localization.AtPrime p ⧸ Ideal.span
      ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r)))) ≃+*
      D.subscheme.presheaf.stalk z := by
    dsimp only at e
    have ep : (Localization.AtPrime p ⧸ K.map (algebraMap A (Localization.AtPrime p)))
        ≃+* D.subscheme.presheaf.stalk z := by
      cases heq
      exact e
    exact (Ideal.quotEquivOfEq hquot.symm).trans ep
  refine ⟨IsRegularLocalRing.of_ringEquiv e'.symm, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e']
  have hdim := hc.2
  rw [hz, Finset.card_map] at hdim
  rw [← hdim]
  exact ringKrullDim_eq_of_ringEquiv
    (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- Local intersection and localization data for the full finite root quotient.
The equivalence `components` enumerates exactly the irreducible components of H.
The prime principal ideals give their reduced subscheme structures, and `hbranches`
identifies their supports with the corresponding components. No invertibility of n
or regularity of the root quotient is assumed or concluded.

Source: Stacks Tag 0BIA and ILO IX Proposition 2.1, printed p.133.
(blueprint: lem-sfb-snc-root-local-presentation)

Proof:
1. Affine local Noetherianity makes A Noetherian; finite polynomial quotients are Noetherian.
2. Reindex the irreducible components into the boundary's finite integral branch family.
   Equality of reduced supports identifies the chosen branches with their principal quotients.
   Their intersection has global ideal K = (t_j : j ∈ J). At a point over p its stalk is
   A_p/K A_p, by the surjective stalk map and its kernel. Apply the SNC intersection condition
   and transport regularity and dimension through this ring equivalence.
3. An element outside p becomes a unit in A_p, and its image in every quotient remains a unit.
4. Polynomial coefficient localization carries the root relation ideal to the localized
   relation ideal. Quotient localization therefore makes the root quotient over A_p a
   localization of the root quotient over A. The localization universal property gives e.
5. The quotient-map formulas give e on coefficients and coordinates. Polynomial and
   localization extensionality prove uniqueness from these specified values.
6. A prime q contracting to p avoids the localized denominators. Its extension Q is prime
   and contracts back to q by the prime correspondence for localizations.
7. Localizing at Q is another localization of C at q. Its canonical equivalence with C_q
   fixes the image of C. The same arguments include empty branch sets and subsets, n=1,
   and the vacuous prime-indexed assertions over the zero ring. -/
theorem snc_root_local_presentation
    (A : Type u) [CommRing A] (_hA : IsRegularScheme (Spec (.of A)))
    (r : ℕ) (t : Fin r → A)
    (H : (Spec (.of A)).IdealSheafData) (_hH : IsStrictNormalCrossingsBoundary H)
    (components : Fin r ≃ {Z : Set (H.support : Set (Spec (.of A))) //
      Z ∈ irreducibleComponents (H.support : Set (Spec (.of A)))})
    (_hbranches : ∀ i : Fin r, (Ideal.span {t i}).IsPrime ∧
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t i})))) =
        Subtype.val '' (components i).val)
    (n : ℕ) (_hn : 1 ≤ n) :
    IsNoetherianRing A ∧ IsNoetherianRing ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i :
      Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) ∧
    ∀ (p : Ideal A) [p.IsPrime],
      (∀ (J : Finset (Fin r)), (∀ j ∈ J, t j ∈ p) →
        IsRegularLocalRing
          (Localization.AtPrime p ⧸ Ideal.span
            ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r)))) ∧
        ringKrullDim
            (Localization.AtPrime p ⧸ Ideal.span
              ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r)))) +
            (J.card : ℕ) = ringKrullDim (Localization.AtPrime p) ∧
        ∀ i : Fin r, t i ∉ p →
          IsUnit (algebraMap A (Localization.AtPrime p) (t i)) ∧
          IsUnit (Ideal.Quotient.mk (Ideal.span
            ((fun j ↦ algebraMap A (Localization.AtPrime p) (t j)) '' (J : Set (Fin r))))
            (algebraMap A (Localization.AtPrime p) (t i)))) ∧
      ∃! e : Localization
          (p.primeCompl.map (algebraMap A ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i :
            Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))))) ≃+*
          (MvPolynomial (Fin r) (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i : Fin r ↦
            MvPolynomial.X i ^ n - MvPolynomial.C (algebraMap A (Localization.AtPrime p) (t i))))),
        (∀ a : A, e (algebraMap ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r ↦
          MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) _
            (algebraMap A ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r ↦
              MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) a)) =
          algebraMap (Localization.AtPrime p) _ (algebraMap A (Localization.AtPrime p) a)) ∧
        (∀ i : Fin r, e (algebraMap ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r
          ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) _
            (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
          Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
        ∀ (q : Ideal ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r ↦
          MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))) [q.IsPrime],
          q.comap (algebraMap A ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r ↦
            MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))) = p →
          ∃ (Q : Ideal ((MvPolynomial (Fin r) (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun
            i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (algebraMap A (Localization.AtPrime p)
            (t i))))))) (_hQ : Q.IsPrime),
            Q = q.map (e.toRingHom.comp (algebraMap ((MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range
              (fun i : Fin r ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) _)) ∧
            ∃ eq : Localization.AtPrime Q ≃+* Localization.AtPrime q,
              ∀ c : (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i : Fin r ↦ MvPolynomial.X
                i ^ n - MvPolynomial.C (t i)))),
                eq (Localization.mk (e (Localization.mk c 1)) 1) = Localization.mk c 1 := by
  classical
  have hnoeth : IsNoetherianRing A := isLocallyNoetherian_Spec.mp _hA.1
  have := hnoeth
  refine ⟨hnoeth, inferInstance, ?_⟩
  intro p _
  constructor
  · intro J hJ
    obtain ⟨hreg, hdim⟩ := snc_local_intersections A r t H _hH components _hbranches p J hJ
    refine ⟨hreg, hdim, ?_⟩
    intro i hi
    have hu := IsLocalization.map_units (M := p.primeCompl)
      (Localization.AtPrime p) ⟨t i, hi⟩
    exact ⟨hu, hu.map (Ideal.Quotient.mk _)⟩
  · obtain ⟨e, hec, hex⟩ := root_quotient_localization A r t n p
    refine ⟨e, ⟨hec, hex, ?_⟩, ?_⟩
    · intro q _ hqp
      apply prime_localization_of_equiv _ _ _ e q
      apply Set.disjoint_left.mpr
      rintro c ⟨a, ha, rfl⟩ hc
      have hnot : algebraMap A _ a ∉ q := by
        change a ∉ q.comap (algebraMap A _)
        rw [hqp]
        exact ha
      exact hnot hc
    · intro f hf
      apply root_localization_ext A r _ p _ f e
      · intro a
        rw [hf.1 a, hec a]
      · intro i
        rw [hf.2.1 i, hex i]

end AlgebraicGeometry
