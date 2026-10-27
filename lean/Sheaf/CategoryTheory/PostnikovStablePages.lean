/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.PostnikovAdditiveExactCoupleData
import all Sheaf.CategoryTheory.PostnikovAdditiveExactCoupleData
import all WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import all WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import all WeilConjectures.CategoryTheory.ExactCouple
import all WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-! # Additive stabilized Postnikov pages

Source: Stacks Project, Homology, Tags 011T and 012U.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

private theorem finite_cycle_map {T : DerivedCategory A ⥤ B}
    {C : PostnikovCoupleData T} (P : PostnikovPageData C) (ρ : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) (r : ℕ) (p q : ℤ) :
    ∃ z : ((C.couple ρ L).cycleBoundaryTower.Z r p q : B) ⟶
        ((C.couple ρ M).cycleBoundaryTower.Z r p q : B),
      z ≫ ((C.couple ρ M).cycleBoundaryTower.Z r p q).arrow =
        ((C.couple ρ L).cycleBoundaryTower.Z r p q).arrow ≫ (P.map ρ 0 u).tE p q ∧
      z ≫ (C.couple ρ M).cycleBoundaryTower.projection r p q =
        (C.couple ρ L).cycleBoundaryTower.projection r p q ≫ (P.map ρ r u).tE p q := by
  let X := C.couple ρ L
  let Y := C.couple ρ M
  let TX := X.cycleBoundaryTower
  let TY := Y.cycleBoundaryTower
  induction r with
  | zero =>
    have hz : (TY.Z 0 p q).Factors
        ((TX.Z 0 p q).arrow ≫ (P.map ρ 0 u).tE p q) := by
      rw [TY.Z_zero]
      exact Subobject.top_factors _
    refine ⟨(TY.Z 0 p q).factorThru _ hz, Subobject.factorThru_arrow _ _ _, ?_⟩
    rw [TX.projection_zero, TY.projection_zero]
    exact Subobject.factorThru_arrow _ _ _
  | succ r ih =>
    obtain ⟨z, hz, hp⟩ := ih
    have hd := BigradedExactCouple.morphism_d (P.map ρ r u) p q
    have hkern : (kernelSubobject ((Y.pageCouple r).d p q)).Factors
        ((kernelSubobject ((X.pageCouple r).d p q)).arrow ≫ (P.map ρ r u).tE p q) := by
      apply kernelSubobject_factors
      rw [Category.assoc, hd, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
    have hZ := BigradedExactCouple.extendedPullback_transport (TX.Z r p q) (TY.Z r p q)
      (TX.projection r p q) (TY.projection r p q) ((P.map ρ 0 u).tE p q)
      z ((P.map ρ r u).tE p q) hz hp
      (kernelSubobject ((X.pageCouple r).d p q))
      (kernelSubobject ((Y.pageCouple r).d p q)) hkern
    rw [← TX.Z_succ, ← TY.Z_succ] at hZ
    let zn := (TY.Z (r + 1) p q).factorThru _ hZ
    have hzn : zn ≫ (TY.Z (r + 1) p q).arrow =
        (TX.Z (r + 1) p q).arrow ≫ (P.map ρ 0 u).tE p q :=
      Subobject.factorThru_arrow _ _ _
    refine ⟨zn, hzn, ?_⟩
    obtain ⟨k, hk, hkn⟩ := P.homology_square ρ r u p q
    have hc : TX.cycleLift r p q ≫ k = zn ≫ TY.cycleLift r p q := by
      apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
      rw [Category.assoc, hk, ← Category.assoc, TX.cycleLift_comm,
        Category.assoc, ← hp, ← Category.assoc,
        Category.assoc zn, TY.cycleLift_comm, ← Category.assoc]
      congr 1
      apply (cancel_mono (TY.Z r p q).arrow).mp
      rw [Category.assoc, hz, ← Category.assoc, Subobject.ofLE_arrow,
        Category.assoc, Subobject.ofLE_arrow, hzn]
    rw [TX.projection_succ, TY.projection_succ, ← Category.assoc, ← hc,
      Category.assoc, ← hkn, Category.assoc]


/-- Entries with stationary finite cycles and boundaries form additive functors.

Source: Stacks Project, Homology, Tags 011T and 012U
(blueprint: lem-per-postnikov-stable-pages).

Proof: At each object choose a cutoff witnessing stationarity of both subobjects.
Take the cokernel of the stationary boundary inclusion into the stationary cycles.
Every later page is the quotient of these same subobjects: its cycle-tower projection
is epimorphic and has exactly that kernel. The unique isomorphism of these cokernels
gives the comparison from each late page. A couple morphism preserves all finite cycles
and boundaries, so comparison at a common cutoff restricts its initial E-map to the
stationary cycles and descends to their quotient. Cancel the cycle inclusion and the
quotient projection to prove cutoff independence, identity, composition and addition.
The same cancellation proves naturality of every late-page comparison. Finally the
cycle-tower successor-projection identity and P.homology_square prove the transition
identity. All choices are finite cutoffs and quotients; arbitrary infinite limits of
subobjects are not needed. -/
theorem exists_postnikov_stable_data {T : DerivedCategory A ⥤ B}
    {C : PostnikovCoupleData T} (P : PostnikovPageData C) :
    Nonempty (PostnikovStableData P) := by
  classical
  let K (ρ p q : ℤ) := (postnikovStable C ρ p q).FullSubcategory
  let X (ρ p q : ℤ) (L : K ρ p q) := C.couple ρ L.obj
  let W (ρ p q : ℤ) (L : K ρ p q) := (X ρ p q L).cycleBoundaryTower
  have hExists (ρ p q : ℤ) (L : K ρ p q) : ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      (W ρ p q L).Z s p q = (W ρ p q L).Z r p q ∧
      (W ρ p q L).B s p q = (W ρ p q L).B r p q := L.property
  let N (ρ p q : ℤ) (L : K ρ p q) : ℕ := (hExists ρ p q L).choose
  have hN (ρ p q : ℤ) (L : K ρ p q) (r : ℕ) (h : N ρ p q L ≤ r) :=
    (hExists ρ p q L).choose_spec r h
  let Z (ρ p q : ℤ) (L : K ρ p q) := (W ρ p q L).Z (N ρ p q L) p q
  let D (ρ p q : ℤ) (L : K ρ p q) := (W ρ p q L).B (N ρ p q L) p q
  let i (ρ p q : ℤ) (L : K ρ p q) : (D ρ p q L : B) ⟶ (Z ρ p q L : B) :=
    Subobject.ofLE _ _ ((W ρ p q L).B_le_Z (N ρ p q L) p q)
  let Q (ρ p q : ℤ) (L : K ρ p q) := cokernel (i ρ p q L)
  have hfinite (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) (r : ℕ) :=
    BigradedExactCouple.exactCoupleFiniteTransport (X ρ p q L) (X ρ p q M)
      (fun a b ↦ (P.map ρ 0 u.hom).tE a b)
      (fun r a b ↦ (P.map ρ r u.hom).tE a b) (fun _ _ ↦ rfl)
      (fun r a b ↦ BigradedExactCouple.morphism_d (P.map ρ r u.hom) a b)
      (fun r a b ↦ P.homology_square ρ r u.hom a b) r p q
  have hfac (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) :
      (Z ρ p q M).Factors ((Z ρ p q L).arrow ≫ (P.map ρ 0 u.hom).tE p q) ∧
      (D ρ p q M).Factors ((D ρ p q L).arrow ≫ (P.map ρ 0 u.hom).tE p q) := by
    let r := max (N ρ p q L) (N ρ p q M)
    have hsL := hN ρ p q L r (le_max_left _ _)
    have hsM := hN ρ p q M r (le_max_right _ _)
    have hf := hfinite ρ p q u r
    change ((W ρ p q M).Z r p q).Factors
        (((W ρ p q L).Z r p q).arrow ≫ (P.map ρ 0 u.hom).tE p q) ∧
      ((W ρ p q M).B r p q).Factors
        (((W ρ p q L).B r p q).arrow ≫ (P.map ρ 0 u.hom).tE p q) at hf
    rw [hsL.1, hsL.2, hsM.1, hsM.2] at hf
    exact hf
  let z (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) :
      (Z ρ p q L : B) ⟶ (Z ρ p q M : B) :=
    (Z ρ p q M).factorThru _ (hfac ρ p q u).1
  have hz (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) :
      z ρ p q u ≫ (Z ρ p q M).arrow =
        (Z ρ p q L).arrow ≫ (P.map ρ 0 u.hom).tE p q :=
    Subobject.factorThru_arrow _ _ _
  have hw (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) :
      i ρ p q L ≫ (z ρ p q u ≫ cokernel.π (i ρ p q M)) = 0 := by
    let b := (D ρ p q M).factorThru _ (hfac ρ p q u).2
    have hb : b ≫ (D ρ p q M).arrow =
        (D ρ p q L).arrow ≫ (P.map ρ 0 u.hom).tE p q :=
      Subobject.factorThru_arrow _ _ _
    have hi : i ρ p q L ≫ z ρ p q u = b ≫ i ρ p q M := by
      apply (cancel_mono (Z ρ p q M).arrow).mp
      simp only [Category.assoc, hz, i, Subobject.ofLE_arrow_assoc,
        Subobject.ofLE_arrow, hb]
    rw [← Category.assoc, hi, Category.assoc, cokernel.condition, comp_zero]
  let m (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) : Q ρ p q L ⟶ Q ρ p q M :=
    cokernel.desc (i ρ p q L) (z ρ p q u ≫ cokernel.π (i ρ p q M)) (hw ρ p q u)
  have hm (ρ p q : ℤ) {L M : K ρ p q} (u : L ⟶ M) :
      cokernel.π (i ρ p q L) ≫ m ρ p q u =
        z ρ p q u ≫ cokernel.π (i ρ p q M) := cokernel.π_desc _ _ _
  have htid (ρ p q : ℤ) (L : K ρ p q) :
      (P.map ρ 0 (𝟙 L.obj)).tE p q = 𝟙 _ := by
    rw [P.mapE]
    exact (congrArg
      (fun f ↦ (P.eIso ρ 0 p q L.obj).inv ≫ f ≫ (P.eIso ρ 0 p q L.obj).hom)
      ((P.E ρ 0 p q).map_id L.obj)).trans
        (by simp only [Category.id_comp, Iso.inv_hom_id])
  have htcomp (ρ p q : ℤ) {L M R : K ρ p q} (u : L ⟶ M) (v : M ⟶ R) :
      (P.map ρ 0 (u.hom ≫ v.hom)).tE p q =
        (P.map ρ 0 u.hom).tE p q ≫ (P.map ρ 0 v.hom).tE p q := by
    simp only [P.mapE, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  have htadd (ρ p q : ℤ) {L M : K ρ p q} (u v : L ⟶ M) :
      (P.map ρ 0 (u.hom + v.hom)).tE p q =
        (P.map ρ 0 u.hom).tE p q + (P.map ρ 0 v.hom).tE p q := by
    have := P.additiveE ρ 0 p q
    simp only [P.mapE, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  have hzid (ρ p q : ℤ) (L : K ρ p q) : z ρ p q (𝟙 L) = 𝟙 _ := by
    apply (cancel_mono (Z ρ p q L).arrow).mp
    rw [hz]
    change (Z ρ p q L).arrow ≫ (P.map ρ 0 (𝟙 L.obj)).tE p q =
      𝟙 _ ≫ (Z ρ p q L).arrow
    rw [htid]
    change (Z ρ p q L).arrow ≫ 𝟙 ((X ρ p q L).E p q) =
      𝟙 _ ≫ (Z ρ p q L).arrow
    simp only [Category.comp_id, Category.id_comp]
  have hzcomp (ρ p q : ℤ) {L M R : K ρ p q} (u : L ⟶ M) (v : M ⟶ R) :
      z ρ p q (u ≫ v) = z ρ p q u ≫ z ρ p q v := by
    apply (cancel_mono (Z ρ p q R).arrow).mp
    rw [hz]
    change (Z ρ p q L).arrow ≫ (P.map ρ 0 (u.hom ≫ v.hom)).tE p q = _
    rw [htcomp]
    change (Z ρ p q L).arrow ≫
        ((P.map ρ 0 u.hom).tE p q ≫ (P.map ρ 0 v.hom).tE p q) = _
    rw [Category.assoc, hz]
    exact ((Category.assoc _ _ _).symm).trans
      ((congrArg (fun f ↦ f ≫ (P.map ρ 0 v.hom).tE p q)
        (hz ρ p q u).symm).trans (Category.assoc _ _ _))
  have hzadd (ρ p q : ℤ) {L M : K ρ p q} (u v : L ⟶ M) :
      z ρ p q (u + v) = z ρ p q u + z ρ p q v := by
    apply (cancel_mono (Z ρ p q M).arrow).mp
    have huv : (u + v).hom = u.hom + v.hom := rfl
    simp only [hz, huv, htadd,
      Preadditive.add_comp, Preadditive.comp_add]
  let F (ρ p q : ℤ) : K ρ p q ⥤ B :=
    { obj := Q ρ p q
      map := m ρ p q
      map_id := fun L ↦ by
        apply (cancel_epi (cokernel.π (i ρ p q L))).mp
        change cokernel.π (i ρ p q L) ≫ m ρ p q (𝟙 L) =
          cokernel.π (i ρ p q L) ≫ 𝟙 _
        rw [hm, hzid, Category.id_comp, Category.comp_id]
      map_comp := fun u v ↦ by
        apply (cancel_epi (cokernel.π (i ρ p q _))).mp
        rw [hm, hzcomp, ← Category.assoc, hm, Category.assoc _ _ (m ρ p q v), hm, Category.assoc] }
  have hF (ρ p q : ℤ) : (F ρ p q).Additive := by
    constructor
    intro L M u v
    change m ρ p q (u + v) = m ρ p q u + m ρ p q v
    apply (cancel_epi (cokernel.π (i ρ p q L))).mp
    simp only [hm, hzadd, Preadditive.comp_add, Preadditive.add_comp]
  have he (ρ p q : ℤ) (L : K ρ p q) (r : ℕ) (h : N ρ p q L ≤ r) :
      ∃ e : Q ρ p q L ≅ ((X ρ p q L).pageCouple r).E p q,
        cokernel.π (i ρ p q L) ≫ e.hom =
          Subobject.ofLE _ _ (le_of_eq (hN ρ p q L r h).1.symm) ≫
            (W ρ p q L).projection r p q := by
    have := (W ρ p q L).projection_epi r p q
    exact BigradedExactCouple.stabilized_quotient_comparison
      (D ρ p q L) (Z ρ p q L) ((W ρ p q L).B r p q) ((W ρ p q L).Z r p q)
      (hN ρ p q L r h).2.symm (hN ρ p q L r h).1.symm
      ((W ρ p q L).B_le_Z (N ρ p q L) p q)
      ((W ρ p q L).B_le_Z r p q) _ ((W ρ p q L).projection r p q)
      ((W ρ p q L).projection_kernel r p q)
  let e (ρ p q : ℤ) (L : K ρ p q) (r : ℕ) (h : N ρ p q L ≤ r) :=
    (he ρ p q L r h).choose
  have heq (ρ p q : ℤ) (L : K ρ p q) (r : ℕ) (h : N ρ p q L ≤ r) :=
    (he ρ p q L r h).choose_spec
  refine ⟨{
    E := F
    additive := hF
    cutoff := N
    iso := fun ρ p q L r h ↦ (e ρ p q L r h).symm
    naturality := ?_
    transition := ?_ }⟩
  · intro ρ p q L M u r hL hM
    apply (cancel_mono (e ρ p q M r hM).hom).mp
    apply (cancel_epi (e ρ p q L r hL).hom).mp
    apply (cancel_epi (cokernel.π (i ρ p q L))).mp
    change cokernel.π (i ρ p q L) ≫ (e ρ p q L r hL).hom ≫
        ((P.map ρ r u.hom).tE p q ≫ (e ρ p q M r hM).inv) ≫
          (e ρ p q M r hM).hom =
      cokernel.π (i ρ p q L) ≫ (e ρ p q L r hL).hom ≫
        ((e ρ p q L r hL).inv ≫ m ρ p q u) ≫ (e ρ p q M r hM).hom
    simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
    rw [← Category.assoc, heq ρ p q L r hL, ← Category.assoc, hm]
    obtain ⟨zr, hzr, hpr⟩ := finite_cycle_map P ρ u.hom r p q
    change zr ≫ ((W ρ p q M).Z r p q).arrow =
      ((W ρ p q L).Z r p q).arrow ≫ (P.map ρ 0 u.hom).tE p q at hzr
    have ha : Subobject.ofLE _ _ (le_of_eq (hN ρ p q L r hL).1.symm) ≫ zr =
        z ρ p q u ≫ Subobject.ofLE _ _ (le_of_eq (hN ρ p q M r hM).1.symm) := by
      apply (cancel_mono ((W ρ p q M).Z r p q).arrow).mp
      simp only [Category.assoc, hzr, Subobject.ofLE_arrow_assoc,
        Subobject.ofLE_arrow, hz]
      rfl
    rw [Category.assoc, ← hpr, ← Category.assoc, ha, Category.assoc,
      ← heq ρ p q M r hM, Category.assoc]
  · intro ρ p q L r h h'
    have hLift : Epi ((W ρ p q L).cycleLift r p q) := by
      have hπ := (W ρ p q L).projection_epi (r + 1) p q
      rw [(W ρ p q L).projection_succ] at hπ
      have hz : (W ρ p q L).Z (r + 1) p q = (W ρ p q L).Z r p q :=
        (hN ρ p q L (r + 1) h').1.trans (hN ρ p q L r h).1.symm
      have hi : IsIso (Subobject.ofLE _ _ ((W ρ p q L).Z_decreasing r p q)) :=
        (Subobject.isoOfEq _ _ hz).isIso_hom
      have hπr := (W ρ p q L).projection_epi r p q
      have he : Epi ((W ρ p q L).cycleLift r p q ≫
          kernel.ι (((X ρ p q L).pageCouple r).d p q)) := by
        rw [(W ρ p q L).cycleLift_comm]
        infer_instance
      have hk : IsIso (kernel.ι (((X ρ p q L).pageCouple r).d p q)) := by
        have := epi_of_epi ((W ρ p q L).cycleLift r p q)
          (kernel.ι (((X ρ p q L).pageCouple r).d p q))
        exact isIso_of_mono_of_epi _
      exact (epi_comp_iff_of_isIso _ _).mp he
    have hOf : IsIso (Subobject.ofLE _ _
        (le_of_eq (hN ρ p q L (r + 1) h').1.symm)) := by
      exact (Subobject.isoOfEq _ _ (hN ρ p q L (r + 1) h').1.symm).isIso_hom
    apply (cancel_epi ((W ρ p q L).cycleLift r p q)).mp
    rw [← Category.assoc, ← (W ρ p q L).projection_succ]
    rw [← Category.assoc, (W ρ p q L).cycleLift_comm]
    apply (cancel_epi (Subobject.ofLE _ _ (le_of_eq (hN ρ p q L (r + 1) h').1.symm))).mp
    change Subobject.ofLE _ _ (le_of_eq (hN ρ p q L (r + 1) h').1.symm) ≫
      (W ρ p q L).projection (r + 1) p q ≫ (e ρ p q L (r + 1) h').inv =
      Subobject.ofLE _ _ (le_of_eq (hN ρ p q L (r + 1) h').1.symm) ≫
        (Subobject.ofLE _ _ ((W ρ p q L).Z_decreasing r p q) ≫
          (W ρ p q L).projection r p q) ≫ (e ρ p q L r h).inv
    rw [← Category.assoc, ← heq ρ p q L (r + 1) h', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    have ha : Subobject.ofLE _ _ (le_of_eq (hN ρ p q L (r + 1) h').1.symm) ≫
        Subobject.ofLE _ _ ((W ρ p q L).Z_decreasing r p q) =
      Subobject.ofLE _ _ (le_of_eq (hN ρ p q L r h).1.symm) := by
      apply (cancel_mono ((W ρ p q L).Z r p q).arrow).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
    calc
      cokernel.π (i ρ p q L) =
          (cokernel.π (i ρ p q L) ≫ (e ρ p q L r h).hom) ≫
            (e ρ p q L r h).inv := by simp only [Category.assoc,
              Iso.hom_inv_id, Category.comp_id]
      _ = (Subobject.ofLE _ _ (le_of_eq (hN ρ p q L r h).1.symm) ≫
          (W ρ p q L).projection r p q) ≫ (e ρ p q L r h).inv := by
        rw [heq ρ p q L r h]
      _ = _ := by rw [← ha]; simp only [Category.assoc]

end DerivedCategory
