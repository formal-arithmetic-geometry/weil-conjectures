/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndBijectiveOnStalks

/-!
# Maps identifying local rings with w-local target are ind-Zariski

Let `A → B` be a ring map identifying all local rings, with `Spec B` w-local. We show that
`B` is an ind-Zariski `A`-algebra (blueprint `lem-weil-pbc-local-rings-ind-zariski`).

The strategy: we construct an `A`-algebra map `WLocalization A → B` which is a w-local map.
For each finite subset `E ⊆ A`, the constructible strata `Z_i` of `E` partition `Spec A`; the
generalization hulls `U_i` of the closed points of `Spec B` lying over `Z_i` form a clopen
partition of `Spec B`, given by idempotents `eᵢ`, and the localization of `A` along `Z_i` maps
to `B ⧸ (1 - eᵢ)`. Since `B ≅ ∏ B ⧸ (1 - eᵢ)`, this defines compatible maps
`ProdStrata E → B`. The resulting map `WLocalization A → B` is a w-local map of w-local rings
identifying local rings, hence is ind-Zariski (Stacks 097F), and so is `A → B`.
-/

@[expose] public section

universe u

open PrimeSpectrum WLocalization Topology CategoryTheory Limits

section Idempotent

variable {B : Type*} [CommRing B]

lemma IsIdempotentElem.eq_zero_of_forall_mem {e : B} (he : IsIdempotentElem e)
    (h : ∀ q : PrimeSpectrum B, e ∈ q.asIdeal) : e = 0 :=
  he.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).mpr fun J hJ ↦ h ⟨J, hJ⟩)

/-- If `e, f` are idempotents with `D(e) ⊆ D(f)`, then `e * f = e`. -/
lemma IsIdempotentElem.mul_eq_left_of_basicOpen_le {e f : B} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : (basicOpen e : Set (PrimeSpectrum B)) ⊆ basicOpen f) :
    e * f = e := by
  have : e * (1 - f) = 0 := by
    refine (he.mul hf.one_sub).eq_zero_of_forall_mem fun q ↦ ?_
    by_cases heq : e ∈ q.asIdeal
    · exact q.asIdeal.mul_mem_right _ heq
    · have hfq : f ∉ q.asIdeal := h heq
      refine q.asIdeal.mul_mem_left _ ?_
      have : f * (1 - f) ∈ q.asIdeal := by rw [hf.mul_one_sub_self]; exact q.asIdeal.zero_mem
      exact (q.isPrime.mem_or_mem this).resolve_left hfq
  linear_combination -this

end Idempotent

namespace IsWLocalRing

variable {B : Type*} [CommRing B] [IsWLocalRing B]

/-- In a w-local ring, the closed points lying in a basic open form a closed subset. -/
lemma isClosed_closedPoints_inter_basicOpen (g : B) :
    IsClosed (closedPoints (PrimeSpectrum B) ∩ basicOpen g) := by
  set C := closedPoints (PrimeSpectrum B)
  have hC : IsClosed C := WLocalSpace.isClosed_closedPoints
  have hemb : IsClosedEmbedding (Subtype.val : C → PrimeSpectrum B) :=
    hC.isClosedEmbedding_subtypeVal
  have : T2Space C := inferInstance
  have hK : IsCompact ((basicOpen g : Set (PrimeSpectrum B)) ∩ C) :=
    (isCompact_basicOpen g).inter_right hC
  have hK' : IsCompact (Subtype.val ⁻¹' (basicOpen g : Set (PrimeSpectrum B)) : Set C) := by
    have := hemb.isCompact_preimage hK
    rwa [Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at this
  have := hemb.isClosedMap _ hK'.isClosed
  rwa [Subtype.image_preimage_coe] at this

end IsWLocalRing

namespace Algebra.IndZariski.OfWLocal

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]

/-- The union of the connected components of `Spec B` whose closed point lies over `Z`. -/
def componentsOver (Z : Set (PrimeSpectrum A)) : Set (PrimeSpectrum B) :=
  generalizationHull (closedPoints (PrimeSpectrum B) ∩
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' Z)

variable {A B}

omit [IsWLocalRing B] in
lemma mem_componentsOver_iff {Z : Set (PrimeSpectrum A)} {q : PrimeSpectrum B} :
    q ∈ componentsOver A B Z ↔ ∃ c : PrimeSpectrum B, IsClosed {c} ∧ q ⤳ c ∧
      PrimeSpectrum.comap (algebraMap A B) c ∈ Z := by
  simp only [componentsOver, mem_generalizationHull_iff, Set.mem_inter_iff, mem_closedPoints_iff,
    Set.mem_preimage]
  exact ⟨fun ⟨c, ⟨h1, h2⟩, h3⟩ ↦ ⟨c, h1, h3, h2⟩, fun ⟨c, h1, h3, h2⟩ ↦ ⟨c, ⟨h1, h2⟩, h3⟩⟩

omit [IsWLocalRing B] in
lemma componentsOver_mono {Z Z' : Set (PrimeSpectrum A)} (h : Z ⊆ Z') :
    componentsOver A B Z ⊆ componentsOver A B Z' := by
  intro q hq
  obtain ⟨c, hc, hqc, hcZ⟩ := mem_componentsOver_iff.mp hq
  exact mem_componentsOver_iff.mpr ⟨c, hc, hqc, h hcZ⟩

lemma disjoint_componentsOver {Z Z' : Set (PrimeSpectrum A)} (h : Disjoint Z Z') :
    Disjoint (componentsOver A B Z) (componentsOver A B Z') := by
  rw [Set.disjoint_left]
  intro q hq hq'
  obtain ⟨c, hc, hqc, hcZ⟩ := mem_componentsOver_iff.mp hq
  obtain ⟨c', hc', hqc', hcZ'⟩ := mem_componentsOver_iff.mp hq'
  obtain rfl := WLocalSpace.eq_of_specializes hc hc' hqc hqc'
  exact Set.disjoint_left.mp h hcZ hcZ'

lemma isClosed_componentsOver_locClosedSubset (f : A) (I : Ideal A) :
    IsClosed (componentsOver A B (Generalization.locClosedSubset f I)) := by
  apply isClosed_generalizationHull_of_wLocalSpace
  have : closedPoints (PrimeSpectrum B) ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' Generalization.locClosedSubset f I =
      (closedPoints (PrimeSpectrum B) ∩ basicOpen (algebraMap A B f)) ∩
        zeroLocus (I.map (algebraMap A B)) := by
    ext q
    simp only [Generalization.locClosedSubset, Set.mem_inter_iff, Set.mem_preimage,
      SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap, mem_zeroLocus,
      SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
    tauto
  rw [this]
  exact (IsWLocalRing.isClosed_closedPoints_inter_basicOpen _).inter (isClosed_zeroLocus _)

omit [IsWLocalRing B] in
variable (B) in
lemma iUnion_componentsOver_stratum (E : Finset A) :
    ⋃ i : Stratification.Index E, componentsOver A B (stratum i.left i.right) = Set.univ := by
  refine Set.eq_univ_of_forall fun q ↦ ?_
  obtain ⟨c, hc, hqc⟩ := exists_isClosed_specializes q
  have := Stratification.Index.iUnion_stratum E ▸
    Set.mem_univ (PrimeSpectrum.comap (algebraMap A B) c)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
  exact Set.mem_iUnion.mpr ⟨i, mem_componentsOver_iff.mpr ⟨c, hc, hqc, hi⟩⟩

lemma isClopen_componentsOver_stratum {E : Finset A} (i : Stratification.Index E) :
    IsClopen (componentsOver A B (stratum i.left i.right)) := by
  have hcl : ∀ j : Stratification.Index E,
      IsClosed (componentsOver A B (stratum j.left j.right)) := fun j ↦ by
    rw [← locClosedSubset_function_ideal]
    exact isClosed_componentsOver_locClosedSubset _ _
  refine ⟨hcl i, ?_⟩
  have : (componentsOver A B (stratum i.left i.right))ᶜ =
      ⋃ j ∈ {j | j ≠ i}, componentsOver A B (stratum j.left j.right) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hq
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
        (iUnion_componentsOver_stratum B E ▸ Set.mem_univ q)
      exact ⟨j, fun h ↦ hq (h ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hi
      exact Set.disjoint_left.mp (disjoint_componentsOver (stratum_disjoint_of_ne hji)) hj hi
  rw [← isClosed_compl_iff, this]
  exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ ↦ hcl j

variable (B) in
/-- The idempotent of `B` cutting out the components of `Spec B` over the stratum `i`. -/
noncomputable def idem {E : Finset A} (i : Stratification.Index E) : B :=
  (isIdempotentElemEquivClopens (R := B)).symm
    ⟨componentsOver A B (stratum i.left i.right), isClopen_componentsOver_stratum i⟩

lemma isIdempotentElem_idem {E : Finset A} (i : Stratification.Index E) :
    IsIdempotentElem (idem B i) :=
  ((isIdempotentElemEquivClopens (R := B)).symm _).2

lemma basicOpen_idem {E : Finset A} (i : Stratification.Index E) :
    (basicOpen (idem B i) : Set (PrimeSpectrum B)) =
      componentsOver A B (stratum i.left i.right) :=
  congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum B) ↦ (U : Set (PrimeSpectrum B)))
    (basicOpen_isIdempotentElemEquivClopens_symm (R := B)
      ⟨componentsOver A B (stratum i.left i.right), isClopen_componentsOver_stratum i⟩)

lemma idem_mul_idem_of_ne {E : Finset A} {i j : Stratification.Index E} (h : i ≠ j) :
    idem B i * idem B j = 0 := by
  refine ((isIdempotentElem_idem i).mul (isIdempotentElem_idem j)).eq_zero_of_forall_mem
    fun q ↦ ?_
  by_contra hq
  have hi : q ∈ (basicOpen (idem B i) : Set _) := fun h' ↦ hq (q.asIdeal.mul_mem_right _ h')
  have hj : q ∈ (basicOpen (idem B j) : Set _) := fun h' ↦ hq (q.asIdeal.mul_mem_left _ h')
  rw [basicOpen_idem] at hi hj
  exact Set.disjoint_left.mp (disjoint_componentsOver (stratum_disjoint_of_ne h)) hi hj

lemma prod_one_sub_idem (E : Finset A) [Fintype (Stratification.Index E)] :
    ∏ i : Stratification.Index E, (1 - idem B i) = 0 := by
  classical
  refine IsIdempotentElem.eq_zero_of_forall_mem ?_ fun q ↦ ?_
  · exact Finset.prod_induction _ _ (fun _ _ ha hb ↦ ha.mul hb) .one
      fun i _ ↦ (isIdempotentElem_idem i).one_sub
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (iUnion_componentsOver_stratum B E ▸ Set.mem_univ q)
    rw [← basicOpen_idem] at hi
    have hmem : 1 - idem B i ∈ q.asIdeal := by
      have : idem B i * (1 - idem B i) ∈ q.asIdeal := by
        rw [(isIdempotentElem_idem i).mul_one_sub_self]; exact q.asIdeal.zero_mem
      exact (q.isPrime.mem_or_mem this).resolve_left hi
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact q.asIdeal.mul_mem_right _ hmem

end Algebra.IndZariski.OfWLocal

namespace Algebra.IndZariski.OfWLocal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]

variable (B) in
/-- The quotient `B ⧸ (1 - eᵢ)`, i.e. the part of `B` over the stratum `i`. -/
abbrev Part {E : Finset A} (i : Stratification.Index E) : Type u :=
  B ⧸ Ideal.span {1 - idem B i}

/-- Elements of `A` invertible on the stratum `i` become units on the corresponding part
of `B`. -/
lemma isUnit_algebraMap_part {E : Finset A} (i : Stratification.Index E)
    (y : Generalization.submonoid i.function i.ideal) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - idem B i}) (algebraMap A B y)) := by
  by_contra hy
  obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hy
  set q : PrimeSpectrum B := ⟨M.comap (Ideal.Quotient.mk _), Ideal.IsPrime.comap _⟩
  have h1 : 1 - idem B i ∈ q.asIdeal := by
    change Ideal.Quotient.mk _ (1 - idem B i) ∈ M
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    exact M.zero_mem
  have h2 : q ∈ (basicOpen (idem B i) : Set (PrimeSpectrum B)) := by
    intro h
    have : (1 : B) ∈ q.asIdeal := by
      simpa using q.asIdeal.add_mem h1 h
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  rw [basicOpen_idem, mem_componentsOver_iff] at h2
  obtain ⟨c, -, hqc, hc⟩ := h2
  rw [← locClosedSubset_function_ideal] at hc
  have := (Generalization.mem_submonoid_iff _ _ _).mp y.2 _ hc
  apply this
  rw [comap_asIdeal, Ideal.mem_comap]
  exact (PrimeSpectrum.le_iff_specializes q c).mpr hqc hyM

/-- The map from the localization of `A` along the stratum `i` to the part of `B` over it. -/
noncomputable def liftPart {E : Finset A} (i : Stratification.Index E) :
    Generalization i.function i.ideal →+* Part B i :=
  IsLocalization.lift (M := Generalization.submonoid i.function i.ideal)
    (g := (Ideal.Quotient.mk _).comp (algebraMap A B)) (isUnit_algebraMap_part i)

@[simp]
lemma liftPart_algebraMap {E : Finset A} (i : Stratification.Index E) (a : A) :
    liftPart (B := B) i (algebraMap A _ a) = Ideal.Quotient.mk _ (algebraMap A B a) :=
  IsLocalization.lift_eq _ _

variable (B) in
lemma bijective_pi_part (E : Finset A) :
    Function.Bijective (RingHom.pi fun i : Stratification.Index E ↦
      Ideal.Quotient.mk (Ideal.span {1 - idem B i})) := by
  classical
  have : Fintype (Stratification.Index E) := Fintype.ofFinite _
  refine RingHom.pi_bijective_of_isIdempotentElem _ (fun i ↦ (isIdempotentElem_idem i).one_sub)
    (fun i j hij ↦ ?_) (prod_one_sub_idem E)
  simp only [sub_sub_cancel]
  exact idem_mul_idem_of_ne hij

variable (B) in
/-- The decomposition `B ≅ ∏ᵢ B ⧸ (1 - eᵢ)`. -/
noncomputable def piPartEquiv (E : Finset A) : B ≃+* ∀ i : Stratification.Index E, Part B i :=
  RingEquiv.ofBijective _ (bijective_pi_part B E)

variable (B) in
/-- The map `ProdStrata E → B`. -/
noncomputable def toB (E : Finset A) : ProdStrata E →ₐ[A] B where
  toRingHom := (piPartEquiv B E).symm.toRingHom.comp
    (RingHom.pi fun i ↦ (liftPart (B := B) i).comp (Pi.evalRingHom _ i))
  commutes' a := by
    change (piPartEquiv B E).symm _ = _
    rw [RingEquiv.symm_apply_eq]
    ext i
    change liftPart i (algebraMap A _ a) = Ideal.Quotient.mk _ (algebraMap A B a)
    exact liftPart_algebraMap i a

lemma mk_toB {E : Finset A} (x : ProdStrata E) (i : Stratification.Index E) :
    Ideal.Quotient.mk (Ideal.span {1 - idem B i}) (toB B E x) = liftPart i (x i) := by
  have h : (piPartEquiv B E) (toB B E x) = fun i ↦ liftPart i (x i) :=
    (piPartEquiv B E).apply_symm_apply _
  exact congrFun h i

lemma one_sub_idem_mem_span {E F : Finset A} (h : E ⊆ F) (j : Stratification.Index F) :
    1 - idem B (j.restrict h) ∈ Ideal.span {1 - idem B j} := by
  have hle : (basicOpen (idem B j) : Set (PrimeSpectrum B)) ⊆
      basicOpen (idem B (j.restrict h)) := by
    rw [basicOpen_idem, basicOpen_idem]
    apply componentsOver_mono
    exact stratum_anti (by simp) (by simp)
  have hmul := (isIdempotentElem_idem j).mul_eq_left_of_basicOpen_le
    (isIdempotentElem_idem (j.restrict h)) hle
  rw [Ideal.mem_span_singleton]
  refine ⟨1 - idem B (j.restrict h), ?_⟩
  linear_combination (-1 : B) * hmul

lemma toB_map {E F : Finset A} (h : E ⊆ F) (x : ProdStrata E) :
    toB B F (ProdStrata.map h x) = toB B E x := by
  apply (piPartEquiv B F).injective
  ext j
  change Ideal.Quotient.mk _ (toB B F (ProdStrata.map h x)) =
    Ideal.Quotient.mk _ (toB B E x)
  have hle : Ideal.span {1 - idem B (j.restrict h)} ≤ Ideal.span {1 - idem B j} := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact one_sub_idem_mem_span h j
  rw [mk_toB, ProdStrata.map_apply, ← Ideal.Quotient.factor_mk hle, mk_toB]
  change ((liftPart j).comp (Generalization.map _).toRingHom) (x (j.restrict h)) =
    ((Ideal.Quotient.factor hle).comp (liftPart (j.restrict h))) (x (j.restrict h))
  congr 1
  refine IsLocalization.ringHom_ext
    (Generalization.submonoid (j.restrict h).function (j.restrict h).ideal) ?_
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, liftPart_algebraMap, Ideal.Quotient.factor_mk]

variable (A B) in
/-- The cocone over the diagram defining `WLocalization A` with vertex `B`. -/
noncomputable def toBCocone : Cocone (diag A) where
  pt := CommAlgCat.of A B
  ι :=
    { app E := CommAlgCat.ofHom (toB B E)
      naturality {E F} f := by
        ext x
        change toB B F (ProdStrata.map (leOfHom f) x) = toB B E x
        exact toB_map (leOfHom f) x }

variable (A B) in
/-- The `A`-algebra map `WLocalization A → B`. -/
noncomputable def lift : WLocalization A →ₐ[A] B :=
  (colimit.desc (diag A) (toBCocone A B)).hom

lemma lift_ιRingHom (E : Finset A) (x : ProdStrata E) :
    lift A B (ιRingHom A E x) = toB B E x := by
  have := colimit.ι_desc (toBCocone A B) E
  exact congrArg (fun f ↦ f.hom x) this

lemma ideal_le_comap_toB {E : Finset A} (b : PrimeSpectrum B) (hb : IsClosed {b}) :
    ProdStrata.ideal E ≤ (b.asIdeal.comap (toB B E).toRingHom) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Stratification.Index.iUnion_stratum E ▸
    Set.mem_univ (PrimeSpectrum.comap (algebraMap A B) b))
  have hbU : b ∈ (basicOpen (idem B i) : Set (PrimeSpectrum B)) := by
    rw [basicOpen_idem]
    exact mem_componentsOver_iff.mpr ⟨b, hb, specializes_rfl, hi⟩
  have h1 : 1 - idem B i ∈ b.asIdeal := by
    have : idem B i * (1 - idem B i) ∈ b.asIdeal := by
      rw [(isIdempotentElem_idem i).mul_one_sub_self]; exact b.asIdeal.zero_mem
    exact (b.isPrime.mem_or_mem this).resolve_left hbU
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {1 - idem B i})) ≤ b.asIdeal := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact h1
  -- The prime `b̄` of the part over `i`.
  set bbar : Ideal (Part B i) := b.asIdeal.map (Ideal.Quotient.mk _)
  have hbbar : bbar.IsPrime :=
    Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk (Ideal.span {1 - idem B i}))
      Ideal.Quotient.mk_surjective hker
  have hcomap : bbar.comap (Ideal.Quotient.mk (Ideal.span {1 - idem B i})) = b.asIdeal := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
    exact sup_eq_left.mpr hker
  -- The prime of the generalization lying under `b̄`.
  set P : PrimeSpectrum (Generalization i.function i.ideal) :=
    PrimeSpectrum.comap (liftPart i) ⟨bbar, hbbar⟩
  have hP : PrimeSpectrum.comap (algebraMap A _) P = PrimeSpectrum.comap (algebraMap A B) b := by
    ext a
    simp only [P, comap_asIdeal, Ideal.mem_comap, liftPart_algebraMap]
    rw [← Ideal.mem_comap, hcomap]
  obtain ⟨P', hP'mem, hP'⟩ :=
    (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
      i.function i.ideal).surjOn (show PrimeSpectrum.comap (algebraMap A B) b ∈ _ by
      rw [locClosedSubset_function_ideal]; exact hi)
  have hPP' : P' = P :=
    PrimeSpectrum.localization_comap_injective _
      (Generalization.submonoid i.function i.ideal) (hP'.trans hP.symm)
  have hxi : x i ∈ P.asIdeal := by
    rw [← hPP']
    exact (mem_zeroLocus _ _).mp hP'mem ((ProdStrata.mem_ideal_iff x).mp hx i)
  have : Ideal.Quotient.mk _ (toB B E x) ∈ bbar := by
    rw [mk_toB]; exact hxi
  rw [Ideal.mem_comap, ← hcomap]
  exact this

lemma isWLocal_lift : (lift A B).toRingHom.IsWLocal := by
  rw [RingHom.isWLocal_iff_isMaximal_of_isMaximal]
  intro m hm
  set b : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hb : IsClosed ({b} : Set (PrimeSpectrum B)) :=
    (isClosed_singleton_iff_isMaximal _).mpr hm
  have hmem : PrimeSpectrum.comap (lift A B).toRingHom b ∈ zeroLocus (WLocalization.ideal A) := by
    rw [mem_zeroLocus_ideal_iff]
    intro E
    rw [mem_zeroLocus, SetLike.coe_subset_coe]
    intro x hx
    have := ideal_le_comap_toB (E := E) b hb hx
    rw [Ideal.mem_comap] at this
    simp only [comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [lift_ιRingHom]
    exact this
  exact (isClosed_singleton_iff_isMaximal _).mp (isClosed_singleton_of_mem_zeroLocus_ideal A hmem)

end Algebra.IndZariski.OfWLocal

open Algebra.IndZariski.OfWLocal in
/-- **Blueprint `lem-weil-pbc-local-rings-ind-zariski`**: if `A → B` identifies all local rings
and `Spec B` is w-local, then `B` is an ind-Zariski `A`-algebra. -/
theorem Algebra.IndZariski.of_bijectiveOnStalks_of_isWLocalRing (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.BijectiveOnStalks A B] [IsWLocalRing B] :
    Algebra.IndZariski A B := by
  let : Algebra (WLocalization A) B := (lift A B).toRingHom.toAlgebra
  have : IsScalarTower A (WLocalization A) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((lift A B).commutes a).symm
  have : Algebra.BijectiveOnStalks (WLocalization A) B :=
    Algebra.BijectiveOnStalks.of_comp A (WLocalization A) B
  have : Algebra.IndZariski (WLocalization A) B :=
    Algebra.BijectiveOnStalks.indZariski_of_isWLocal (WLocalization A) B isWLocal_lift
  exact Algebra.IndZariski.trans (R := A) (S := WLocalization A) (T := B)
