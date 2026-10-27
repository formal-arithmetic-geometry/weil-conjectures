/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.TransversePrimeIdealParameters
import Sheaf.AlgebraicGeometry.ClosedComponentStalkCalculus
import Sheaf.AlgebraicGeometry.StalkNonzerodivisorCartierSpreading
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Local parameter criterion for strict normal crossings boundaries

Source: Stacks Project, etale.tex, Tags 0BI9 and 0BIA; divisors.tex, Tag 0AG8;
ILO VIII, Remark 4.2.2(i), printed pp. 118--119
(blueprint: lem-sfb-snc-boundary-parameter-criterion).

The closed subscheme is represented by its quasi-coherent ideal sheaf data `H`.
Extension of its ideal on an affine neighbourhood along the germ map is its stalk ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.HilbertSamuel

namespace AlgebraicGeometry

private theorem stalk_eq_affine {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    stalkIdeal I x = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  simpa only [I.ker_subschemeι] using
    (closed_component_stalk_calculus X I.subscheme I.subschemeι).1 U x hx |>.1

private theorem quotient_stalk {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (z : I.subscheme) :
    Nonempty ((X.presheaf.stalk (I.subschemeι z) ⧸ stalkIdeal I (I.subschemeι z)) ≃+*
      I.subscheme.presheaf.stalk z) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (I.subschemeι z)) isOpen_univ
  have hk : stalkIdeal I (I.subschemeι z) =
      RingHom.ker (I.subschemeι.stalkMap z).hom := by
    rw [stalk_eq_affine I ⟨U, hU⟩ _ hx, I.subschemeι.ker_stalkMap ⟨U, hU⟩ z hx,
      I.ker_subschemeι]
  exact ⟨(Ideal.quotEquivOfEq hk).trans
    ((I.subschemeι.stalkMap z).hom.quotientKerEquivOfSurjective
      (I.subschemeι.stalkMap_surjective z))⟩

private theorem list_coordinate_products {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (t : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters t) (r : ℕ) (hr : r ≤ t.length) :
    (t.take r).prod ∈ nonZeroDivisors R ∧
      Ideal.span {(t.take r).prod} =
        ⨅ i : Fin r, Ideal.span {t.get (Fin.castLE hr i)} ∧
      (Ideal.span {(t.take r).prod}).IsRadical := by
  have htake : List.ofFn (fun i : Fin r ↦ t.get (Fin.castLE hr i)) = t.take r := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left hr]
    · intro i hi hj
      simp
  have hp := RingTheory.parameter_product_ideal_properties R t.length ht.2.symm
    t.get (by simpa using ht) r hr
  have hprod : (∏ i : Fin r, t.get (Fin.castLE hr i)) = (t.take r).prod := by
    rw [← List.prod_ofFn, htake]
  rw [hprod] at hp
  exact ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2.1⟩

private theorem parameter_extension
    {R S : Type u} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) (xs : List R)
    (hker : Ideal.ofList xs = RingHom.ker f)
    (hdim : ringKrullDim R = ringKrullDim S + (xs.length : ℕ)) :
    ∃ ys : List R, IsLocalRing.IsRegularSystemOfParameters (xs ++ ys) := by
  classical
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal S))
  obtain ⟨ys, hys⟩ := hf.list_map s.toList
  have hmap : (Ideal.ofList (xs ++ ys)).map f = IsLocalRing.maximalIdeal S := by
    rw [Ideal.ofList_append, Ideal.map_sup, hker, (Ideal.map_eq_bot_iff_le_ker f).mpr le_rfl,
      bot_sup_eq,
      Ideal.map_ofList, hys]
    change Submodule.span S {r | r ∈ s.toList} = _
    simpa using hspan
  have hspan' : Ideal.ofList (xs ++ ys) = IsLocalRing.maximalIdeal R := by
    have h := congrArg (Ideal.comap f) hmap
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot] at h
    rw [sup_eq_left.mpr (by
      rw [← hker]
      exact Ideal.span_mono (by intro x hx; exact List.mem_append_left _ hx))] at h
    rw [← IsLocalRing.map_maximalIdeal_of_surjective f hf,
      Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f))] at h
    exact h
  refine ⟨ys, hspan', ?_⟩
  have hlen : ys.length = (IsLocalRing.maximalIdeal S).spanFinrank := by
    have hh := congrArg List.length hys
    simpa only [List.length_map, Finset.length_toList, hcard] using hh
  rw [List.length_append, Nat.cast_add, hlen,
    IsRegularLocalRing.spanFinrank_maximalIdeal, add_comm]
  exact hdim.symm

private theorem principal_regular_kernel
    {R S : Type u} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim R = ringKrullDim S + 1) :
    ∃ xs : List R, xs.length = 1 ∧ RingTheory.Sequence.IsRegular R xs ∧
      Ideal.ofList xs = RingHom.ker f := by
  let d := (IsLocalRing.maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have : IsRegularLocalRing (R ⧸ RingHom.ker f) :=
    IsRegularLocalRing.of_ringEquiv (f.quotientKerEquivOfSurjective hf).symm
  obtain ⟨p, c, hc, hp, hker⟩ := RingTheory.exists_parameters_regularLocalQuotient
    R d hd (RingHom.ker f) (RingHom.ker_ne_top f)
  obtain ⟨hreg, hquot, -⟩ :=
    IsRegularLocalRing.isRegular_and_quotients_of_generators R d hd p hp
  have heq := (hquot c hc).2
  rw [← hker, ringKrullDim_eq_of_ringEquiv (f.quotientKerEquivOfSurjective hf)] at heq
  have hc1 : c = 1 := by
    rw [hd, heq] at hdim
    have heq' : d = d - c + 1 := by exact_mod_cast hdim
    omega
  have hw : RingTheory.Sequence.IsWeaklyRegular R (p.take c) :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff R (p.take c) (p.drop c)).mp
      (by simpa using hreg.toIsWeaklyRegular)).1
  have hr : RingTheory.Sequence.IsRegular R (p.take c) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun x hx ↦
      hp.1 ▸ Ideal.subset_span (List.mem_of_mem_take hx))).mpr hw
  refine ⟨p.take c, ?_, hr, hker.symm⟩
  have hlen : p.length = d := by exact_mod_cast hp.2.trans hd
  rw [List.length_take, hlen, min_eq_left hc, hc1]

private theorem stalk_principal_of_regular_codimension_one
    {X : Scheme.{u}} [IsNoetherian X] [IsRegular X]
    (I : X.IdealSheafData) [IsRegular I.subscheme]
    (hdim : ∀ z, ringKrullDim (X.presheaf.stalk (I.subschemeι z)) =
      ringKrullDim (I.subscheme.presheaf.stalk z) + 1) (x : X) :
    ∃ a : X.presheaf.stalk x, stalkIdeal I x = Ideal.span {a} := by
  classical
  by_cases hx : x ∈ Set.range I.subschemeι
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨xs, hlen, _, hker⟩ := principal_regular_kernel
      (I.subschemeι.stalkMap z).hom (I.subschemeι.stalkMap_surjective z) (hdim z)
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (I.subschemeι z)) isOpen_univ
    refine ⟨a, ?_⟩
    rw [Ideal.ofList_singleton, I.subschemeι.ker_stalkMap ⟨U, hU⟩ z hxU,
      I.ker_subschemeι] at hker
    rw [stalk_eq_affine I ⟨U, hU⟩ _ hxU, ← hker]
  · refine ⟨1, ?_⟩
    have he := (closed_component_stalk_calculus X I.subscheme I.subschemeι).2.2.1 x hx
    simpa only [I.ker_subschemeι, Ideal.span_singleton_one] using he

/-- A closed subscheme of a regular Noetherian scheme is a strict normal crossings boundary
exactly when its stalk ideal at every point is generated by an initial product of a regular
system of parameters. Taking zero parameters gives the unit ideal, including off-boundary
points and the empty boundary. In the reverse direction the boundary predicate includes
radicality, the effective Cartier condition, and finite regular components with all their
scheme-theoretic intersections regular of the expected codimension.

Source: Stacks Project, Tags 0BI9 and 0BIA; Tag 0AG8; ILO VIII, Remark 4.2.2(i)
(blueprint: lem-sfb-snc-boundary-parameter-criterion).

Proof:
1. The component-stalk calculus identifies affine ideal germs with stalk ideals.
   The surjective closed-immersion stalk map identifies the subscheme stalk with
   the quotient by that ideal.
2. For a boundary component, the regular-local quotient-kernel theorem and the
   parameter-quotient dimension formula show that its ideal at a point on it is
   principal: the kernel parameter list has length one. Off the component use 1.
3. Keep the component generators in the maximal ideal. Their sum is the ideal of
   the corresponding intersection, hence is proper. The intersection is regular
   with dimension the ambient dimension minus the number of selected generators.
   Lift a minimal generating list of its quotient maximal ideal. The concatenated
   list generates the ambient maximal ideal and has the required length, so is a
   regular parameter system. The coordinate-product formula identifies its initial
   product ideal with the intersection of the component ideals. Omitted generators
   are units, and the reduced-union formula identifies this ideal with the boundary.
4. Conversely, coordinate-product algebra makes each ideal stalk radical and gives
   a nonzerodivisor generator. The quotient stalks are reduced, so the closed
   subscheme is reduced and its ideal sheaf is radical. Nonzerodivisor spreading
   proves Cartier invertibility.
5. The component-stalk calculus supplies finitely many distinct integral components
   and identifies their stalk ideals through a point with the minimal primes of the
   boundary ideal. Coordinate-product algebra identifies these primes with distinct
   parameter ideals. The ideal of any selected intersection is therefore generated
   by the corresponding parameter subset. Its quotient is regular of the expected
   dimension. Closed immersions preserve local Noetherianity, so the intersection
   is a regular scheme. This verifies all boundary clauses, including the empty
   component family, empty subset, empty boundary, and empty ambient scheme. -/
theorem isStrictNormalCrossingsBoundary_iff_parameters
    {X : Scheme.{u}} [IsNoetherian X] (_hX : IsRegularScheme X)
    (H : X.IdealSheafData) :
    IsStrictNormalCrossingsBoundary H ↔
      ∀ x : X, ∃ (t : List (X.presheaf.stalk x)) (r : ℕ),
        IsLocalRing.IsRegularSystemOfParameters t ∧ r ≤ t.length ∧
          ∃ (U : X.affineOpens) (hx : x ∈ U.1),
            (H.ideal U).map (X.presheaf.germ U.1 x hx).hom =
              Ideal.span {(t.take r).prod} := by
  classical
  have : IsRegular X := _hX.2
  constructor
  · intro hH x
    obtain ⟨n, C, hinj, hC, hcover, hinter⟩ := hH.2.2
    have hprincipal : ∀ i, ∃ a : X.presheaf.stalk x,
        stalkIdeal (C i) x = Ideal.span {a} := by
      intro i
      have : IsRegular (C i).subscheme := (hC i).2.2
      have he : (⨆ j ∈ ({i} : Finset (Fin n)), C j) = C i := by simp
      have hi := hinter {i}
      rw [he] at hi
      have hi := fun z ↦ (hi z).2
      simp only [Finset.card_singleton, Nat.cast_one] at hi
      exact stalk_principal_of_regular_codimension_one (C i) hi x
    choose g hg using hprincipal
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let U : X.affineOpens := ⟨V, hV⟩
    let L : List (Fin n) := (List.ofFn id).filter (fun i ↦
      decide (g i ∈ IsLocalRing.maximalIdeal _))
    let K : Finset (Fin n) := L.toFinset
    let J : X.IdealSheafData := ⨆ i ∈ K, C i
    have hL : L.Nodup := List.Nodup.filter _ (List.nodup_ofFn.mpr Function.injective_id)
    have hcard : K.card = L.length := List.toFinset_card_of_nodup hL
    have hgen : stalkIdeal J x = Ideal.ofList (L.map g) := by
      have he : J = ⨆ i : K, C i.val :=
        (iSup_subtype (f := fun i : K ↦ C i.val)).symm
      rw [stalk_eq_affine J U x hx, he, Scheme.IdealSheafData.ideal_iSup]
      rw [iSup_apply, Ideal.map_iSup]
      simp_rw [← stalk_eq_affine _ U x hx, hg]
      apply le_antisymm
      · refine iSup_le fun i ↦ Ideal.span_mono ?_
        rintro a rfl
        exact List.mem_map.mpr ⟨i.val, List.mem_toFinset.mp i.property, rfl⟩
      · apply Ideal.span_le.mpr
        intro a ha
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        exact (le_iSup (fun j : K ↦ Ideal.span {g j.val})
          ⟨i, List.mem_toFinset.mpr hi⟩) (Ideal.mem_span_singleton_self _)
    have hJm : (J.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤
        IsLocalRing.maximalIdeal _ := by
      rw [← stalk_eq_affine J U x hx, hgen]
      apply Ideal.span_le.mpr
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    have hxJ : x ∈ J.support := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hx, X.mem_zeroLocus_iff]
      intro z hz
      rw [X.mem_basicOpen z x hx]
      exact (IsLocalRing.mem_maximalIdeal _).mp (hJm (Ideal.mem_map_of_mem _ hz))
    obtain ⟨z, hz⟩ := (show x ∈ Set.range J.subschemeι by
      rwa [J.range_subschemeι])
    let xs := L.map g
    have hxs : ∃ ys : List (X.presheaf.stalk x),
        IsLocalRing.IsRegularSystemOfParameters (xs ++ ys) := by
      have eqv := quotient_stalk J z
      rw [hz] at eqv
      obtain ⟨eqv⟩ := eqv
      have : IsRegular J.subscheme := (hinter K z).1.2
      have : IsRegularLocalRing (X.presheaf.stalk x ⧸ stalkIdeal J x) :=
        IsRegularLocalRing.of_ringEquiv eqv.symm
      apply parameter_extension (Ideal.Quotient.mk (stalkIdeal J x))
        Ideal.Quotient.mk_surjective xs
      · rw [Ideal.mk_ker]
        exact hgen.symm
      · have hdim := (hinter K z).2
        rw [hz] at hdim
        rw [ringKrullDim_eq_of_ringEquiv eqv]
        simpa only [xs, List.length_map, hcard] using hdim
    obtain ⟨ys, hys⟩ := hxs
    refine ⟨xs ++ ys, xs.length, hys, by simp, U, hx, ?_⟩
    simp only [List.take_left]
    have hHunion : H = vanishingIdeal (⨆ i, (C i).support) := by
      rw [← hcover, vanishingIdeal_support, hH.2.1]
    have hstalk : stalkIdeal H x = ⨅ i, stalkIdeal (C i) x := by
      rw [hHunion]
      exact (closed_component_stalk_calculus X H.subscheme H.subschemeι).2.2.2.2.1
        n C (fun i ↦ by have := (hC i).1; infer_instance) x
    have hcoord := (list_coordinate_products (xs ++ ys) hys xs.length (by simp)).2.1
    have hcoord' : Ideal.span {xs.prod} =
        ⨅ i : Fin xs.length, Ideal.span {xs.get i} := by
      simpa using hcoord
    rw [← stalk_eq_affine H U x hx, hstalk, hcoord']
    apply le_antisymm
    · refine le_iInf fun j ↦ ?_
      obtain ⟨i, hi, hij⟩ := List.mem_map.mp (List.get_mem xs j)
      rw [← hij, ← hg i]
      exact iInf_le _ i
    · refine le_iInf fun i ↦ ?_
      rw [hg i]
      by_cases hi : i ∈ L
      · have hm : g i ∈ xs := List.mem_map.mpr ⟨i, hi, rfl⟩
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
        rw [← hj]
        exact iInf_le _ j
      · have hu : IsUnit (g i) := by
          apply IsLocalRing.notMem_maximalIdeal.mp
          simpa [L] using hi
        rw [Ideal.span_singleton_eq_top.mpr hu]
        exact le_top
  · intro h
    have hlocal (x : X) : ∃ (d r : ℕ) (hr : r ≤ d)
        (f : Fin d → X.presheaf.stalk x),
        IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) ∧
        stalkIdeal H x = Ideal.span {∏ i : Fin r, f (Fin.castLE hr i)} := by
      obtain ⟨t, r, ht, hr, U, hx, hI⟩ := h x
      refine ⟨t.length, r, hr, t.get, by simpa using ht, ?_⟩
      rw [stalk_eq_affine H U x hx, hI]
      congr 1
      have he : List.ofFn (fun i : Fin r ↦ t.get (Fin.castLE hr i)) = t.take r := by
        apply List.ext_getElem
        · simp [Nat.min_eq_left hr]
        · intro i hi hj
          simp
      exact congrArg (fun a ↦ ({a} : Set (X.presheaf.stalk x)))
        ((congrArg List.prod he.symm).trans List.prod_ofFn)
    choose d r hr f hf hI using hlocal
    have hd (x : X) : ringKrullDim (X.presheaf.stalk x) = (d x : WithBot ℕ∞) := by
      simpa using (hf x).2.symm
    have hp (x : X) := RingTheory.parameter_product_ideal_properties
      (X.presheaf.stalk x) (d x) (hd x) (f x) (hf x) (r x) (hr x)
    have hrad (x : X) : (stalkIdeal H x).IsRadical := by
      rw [hI]
      exact (hp x).2.2.2.2.1
    have : ∀ z : H.subscheme, _root_.IsReduced (H.subscheme.presheaf.stalk z) := by
      intro z
      obtain ⟨e⟩ := quotient_stalk H z
      have : _root_.IsReduced
          (X.presheaf.stalk (H.subschemeι z) ⧸ stalkIdeal H (H.subschemeι z)) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (hrad _)
      exact isReduced_of_injective e.symm.toRingHom e.symm.injective
    have hred : IsReduced H.subscheme := isReduced_of_isReduced_stalk _
    let : IsReduced H.subscheme := hred
    have hHrad : H.radical = H := by
      have he := H.subschemeι.ker_eq_vanishingIdeal
      rw [H.ker_subschemeι] at he
      have hclosed : (⟨closure (Set.range H.subschemeι), isClosed_closure⟩ :
          TopologicalSpace.Closeds X) = H.support := by
        apply TopologicalSpace.Closeds.ext
        change closure (Set.range H.subschemeι) = (H.support : Set X)
        rw [H.range_subschemeι, H.support.isClosed.closure_eq]
      rw [hclosed, vanishingIdeal_support] at he
      exact he.symm
    have hcart : H.IsInvertible := by
      rw [← H.ker_subschemeι]
      apply isInvertible_ker_of_stalk_nonzerodivisor H.subschemeι
      intro x
      obtain ⟨t, s, ht, hs, U, hx, hgen⟩ := h x
      refine ⟨U, hx, (t.take s).prod, ?_, ?_⟩
      · simpa only [H.ker_subschemeι] using hgen
      · exact (isRegular_iff_mem_nonZeroDivisors.mpr
          (list_coordinate_products t ht s hs).1).left
    obtain ⟨n, C, hinj, _, hC, hcover, hbij, hoff, hstalk⟩ :=
      (closed_component_stalk_calculus X H.subscheme H.subschemeι).2.2.2.2.2 hred
    let D : Fin n → X.IdealSheafData := fun i ↦ vanishingIdeal (C i)
    have hDsupport (i : Fin n) : (D i).support = C i := by
      apply TopologicalSpace.Closeds.ext
      simp [D]
    have hHcover : H.support = ⨆ i, C i := by
      rw [H.ker_subschemeι] at hcover
      rw [hcover]
      apply TopologicalSpace.Closeds.ext
      simp only [coe_support_vanishingIdeal]
    have hstrata (s : Finset (Fin n)) :
        IsRegularScheme (⨆ i ∈ s, D i).subscheme ∧
        ∀ z : (⨆ i ∈ s, D i).subscheme,
          ringKrullDim (X.presheaf.stalk ((⨆ i ∈ s, D i).subschemeι z)) =
            ringKrullDim ((⨆ i ∈ s, D i).subscheme.presheaf.stalk z) + (s.card : ℕ) := by
      let E : X.IdealSheafData := ⨆ i ∈ s, D i
      have : IsLocallyNoetherian E.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian E.subschemeι
      have hst (z : E.subscheme) :
          IsRegularLocalRing (E.subscheme.presheaf.stalk z) ∧
          ringKrullDim (X.presheaf.stalk (E.subschemeι z)) =
            ringKrullDim (E.subscheme.presheaf.stalk z) + (s.card : ℕ) := by
        let x := E.subschemeι z
        have hx (i : s) : x ∈ C i.val := by
          have hz : x ∈ E.support := by
            have hz' : x ∈ Set.range E.subschemeι := Set.mem_range_self z
            rw [E.range_subschemeι] at hz'
            exact hz' 
          have hle : D i.val ≤ E := le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl)
          exact (hDsupport i.val) ▸ (Scheme.IdealSheafData.support_antitone hle hz)
        have hmin (i : s) : stalkIdeal (D i.val) x ∈ (stalkIdeal H x).minimalPrimes := by
          simpa only [H.ker_subschemeι] using
            (hbij x).mapsTo (hx i)
        have hprime (i : s) : ∃ j : Fin (r x),
            stalkIdeal (D i.val) x = Ideal.span {f x (Fin.castLE (hr x) j)} := by
          apply ((hp x).2.2.2.2.2.1 _).mp
          simpa only [← hI x] using hmin i
        choose φ hφ using hprime
        have hφinj : Function.Injective φ := by
          intro i j hij
          apply Subtype.ext
          apply (hbij x).injOn (hx i) (hx j)
          change stalkIdeal (D i.val) x = stalkIdeal (D j.val) x
          rw [hφ i, hφ j, hij]
        let J : Finset (Fin (r x)) := Finset.univ.image φ
        have hJcard : J.card = s.card := by
          simp only [J, Finset.card_image_of_injective _ hφinj, Finset.card_univ,
            Fintype.card_coe]
        have hsum : stalkIdeal E x = Ideal.span
            ((fun j : Fin (r x) ↦ f x (Fin.castLE (hr x) j)) '' (J : Set (Fin (r x)))) := by
          obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
            X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
          have he : E = ⨆ i : s, D i.val :=
            (iSup_subtype (f := fun i : s ↦ D i.val)).symm
          rw [stalk_eq_affine E ⟨U, hU⟩ x hxU, he,
            Scheme.IdealSheafData.ideal_iSup]
          rw [iSup_apply, Ideal.map_iSup]
          simp_rw [← stalk_eq_affine _ ⟨U, hU⟩ x hxU, hφ]
          rw [← Ideal.span_iUnion]
          congr 1
          ext a
          simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_image,
            Finset.mem_coe, J, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨j, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
        obtain ⟨e⟩ := quotient_stalk E z
        have hquot := (hp x).2.2.2.2.2.2.1 J
        have e' : (X.presheaf.stalk x ⧸ Ideal.span
              ((fun j : Fin (r x) ↦ f x (Fin.castLE (hr x) j)) '' (J : Set (Fin (r x)))))
              ≃+* E.subscheme.presheaf.stalk z :=
          (Ideal.quotEquivOfEq hsum.symm).trans e
        have : IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span
            ((fun j : Fin (r x) ↦ f x (Fin.castLE (hr x) j)) '' (J : Set (Fin (r x))))) :=
          hquot.1
        refine ⟨IsRegularLocalRing.of_ringEquiv e', ?_⟩
        have hdim : ringKrullDim (E.subscheme.presheaf.stalk z) =
            ((d x - s.card : ℕ) : WithBot ℕ∞) := by
          rw [← ringKrullDim_eq_of_ringEquiv e', hquot.2, hJcard]
        have hcard : s.card ≤ d x := by
          rw [← hJcard]
          exact (Finset.card_le_card (Finset.subset_univ J)).trans
            (by simpa using hr x)
        rw [hd x, hdim, ← Nat.cast_add, Nat.sub_add_cancel hcard]
      refine ⟨⟨inferInstance, ⟨fun z ↦ (hst z).1⟩⟩, fun z ↦ (hst z).2⟩
    refine ⟨hcart, hHrad, n, D, ?_, ?_, ?_, ?_⟩
    · simpa only [hDsupport] using hinj
    · intro i
      refine ⟨hC i, ?_⟩
      simpa using (hstrata {i}).1
    · simpa only [hDsupport] using hHcover
    · intro s z
      exact ⟨(hstrata s).1, (hstrata s).2 z⟩

end AlgebraicGeometry
