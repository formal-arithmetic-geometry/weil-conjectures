/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationData
import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationMap
import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingTotalization
import WeilConjectures.Algebra.Homology.FiniteFilteredBoundedFlatReplacement
import WeilConjectures.Algebra.Homology.FiniteFilteredPrependTwisting
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
/-! # One cone step in a filtered flat resolution

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations,
successive flat resolutions on graded pieces by mapping cylinders.
(blueprint: lem-trf-finite-filtered-twisting-augmentation-extension).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w uB vB
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
attribute [local instance] hasSheafifyEssentiallySmallSite
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}

section General
variable {B : Type uB} [Category.{vB} B] [Abelian B]

private theorem restriction_fac {K L : FilteredObject (CochainComplex B ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    FilteredObject.restrictionSteps f p ≫ (L.filtration.F p).arrow =
      (K.filtration.F p).arrow ≫ f.hom := Classical.choose_spec (f.preserves p)

private theorem restriction_next {K L : FilteredObject (CochainComplex B ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    Subobject.ofLE (K.filtration.F (p + 1)) (K.filtration.F p)
        (K.filtration.F_succ_le p) ≫ FilteredObject.restrictionSteps f p =
      FilteredObject.restrictionSteps f (p + 1) ≫
        Subobject.ofLE (L.filtration.F (p + 1)) (L.filtration.F p)
          (L.filtration.F_succ_le p) := by
  apply (cancel_mono (L.filtration.F p).arrow).1
  simp only [Category.assoc, restriction_fac, Subobject.ofLE_arrow]
  rw [← Category.assoc, Subobject.ofLE_arrow]

private theorem restriction_quasiIso_succ {K L : FilteredObject (CochainComplex B ℤ)}
    (f : K ⟶ L) (p : ℤ)
    (hs : QuasiIso (FilteredObject.restrictionSteps f (p + 1)))
    (hg : QuasiIso (FilteredObject.gradedMapSteps f p)) :
    QuasiIso (FilteredObject.restrictionSteps f p) := by
  let iK := Subobject.ofLE (K.filtration.F (p + 1)) (K.filtration.F p)
    (K.filtration.F_succ_le p)
  let iL := Subobject.ofLE (L.filtration.F (p + 1)) (L.filtration.F p)
    (L.filtration.F_succ_le p)
  let SK := ShortComplex.cokernelSequence iK
  let SL := ShortComplex.cokernelSequence iL
  have hSK : SK.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iK
      mono_f := by dsimp [SK, ShortComplex.cokernelSequence]; infer_instance }
  have hSL : SL.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iL
      mono_f := by dsimp [SL, ShortComplex.cokernelSequence]; infer_instance }
  let φ : SK ⟶ SL :=
    { τ₁ := FilteredObject.restrictionSteps f (p + 1)
      τ₂ := FilteredObject.restrictionSteps f p
      τ₃ := FilteredObject.gradedMapSteps f p
      comm₁₂ := (restriction_next f p).symm
      comm₂₃ := (Classical.choose_spec
        (FilteredObject.exists_gradedMap_steps _ _ f p)).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ φ hSK hSL hs hg

private theorem restriction_quasiIso_finite {K L : FilteredObject (CochainComplex B ℤ)}
    (f : K ⟶ L) (a b : ℤ)
    (hK : K.filtration.F (b + 1) = ⊥) (hL : L.filtration.F (b + 1) = ⊥)
    (hg : ∀ p : ℤ, a ≤ p → p ≤ b → QuasiIso (FilteredObject.gradedMapSteps f p)) :
    QuasiIso (FilteredObject.restrictionSteps f a) := by
  have hz (p : ℤ) (hp : b + 1 ≤ p) :
      QuasiIso (FilteredObject.restrictionSteps f p) := by
    have hKP : K.filtration.F p = ⊥ := le_bot_iff.mp (by
      simpa [hK] using K.filtration.antitone hp)
    have hLP : L.filtration.F p = ⊥ := le_bot_iff.mp (by
      simpa [hL] using L.filtration.antitone hp)
    have hKz : IsZero (K.filtration.F p : CochainComplex B ℤ) := by
      rw [hKP]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have hLz : IsZero (L.filtration.F p : CochainComplex B ℤ) := by
      rw [hLP]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have : IsIso (FilteredObject.restrictionSteps f p) :=
      isIso_of_source_target_iso_zero _ hKz.isoZero hLz.isoZero
    infer_instance
  have hi : ∀ k : ℕ, ∀ p : ℤ, a ≤ p → b + 1 ≤ p + k →
      QuasiIso (FilteredObject.restrictionSteps f p) := by
    intro k
    induction k with
    | zero =>
      intro p _ hp
      exact hz p (by simpa using hp)
    | succ k ih =>
      intro p hp hpb
      by_cases hbp : b < p
      · exact hz p (by omega)
      · exact restriction_quasiIso_succ f p
          (ih (p + 1) (by omega) (by omega)) (hg p hp (by omega))
  exact hi (b + 1 - a).toNat a le_rfl (by omega)

private theorem coneMap_quasiIso {X Y X' Y' : CochainComplex B ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (α : Arrow.mk f ⟶ Arrow.mk g)
    [QuasiIso α.left] [QuasiIso α.right] :
    QuasiIso (mappingCone.map f g α.left α.right α.w.symm) := by
  let := HasDerivedCategory.standard B
  let t := DerivedCategory.Q.mapTriangle.map
    (mappingCone.triangleMap f g α.left α.right α.w.symm)
  have ht : IsIso t.hom₃ := Pretriangulated.isIso₃_of_isIso₁₂ t
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (by change IsIso (DerivedCategory.Q.map α.left)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
    (by change IsIso (DerivedCategory.Q.map α.right)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).1 ht

private theorem coneQuotientMap
    {P K L : CochainComplex B ℤ} (i : K ⟶ L) [Mono i]
    (f : P ⟶ K) [QuasiIso f] :
    ∃ q : mappingCone (f ≫ i) ⟶ cokernel i, QuasiIso q ∧
      ∀ n : ℤ, q.f n = (mappingCone.snd (f ≫ i)).v n n (add_zero n) ≫
        (cokernel.π i).f n := by
  let S := ShortComplex.cokernelSequence i
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i
      mono_f := by dsimp [S, ShortComplex.cokernelSequence]; infer_instance }
  let α : Arrow.mk (f ≫ i) ⟶ Arrow.mk i := Arrow.homMk f (𝟙 _) (by simp)
  have : QuasiIso α.left := inferInstanceAs (QuasiIso f)
  have : QuasiIso α.right := inferInstanceAs (QuasiIso (𝟙 L))
  have : QuasiIso (mappingCone.map (f ≫ i) i f (𝟙 _) (by simp)) :=
    coneMap_quasiIso (f ≫ i) i α
  have : QuasiIso (mappingCone.descShortComplex S) := mappingCone.quasiIso_descShortComplex hS
  let q := mappingCone.map (f ≫ i) i f (𝟙 _) (by simp) ≫
    mappingCone.descShortComplex S
  refine ⟨q, inferInstance, ?_⟩
  intro n
  apply mappingCone.ext_from (f ≫ i) (n + 1) n rfl
  · simp [q, mappingCone.map, Category.assoc, S, ShortComplex.cokernelSequence,
      mappingCone.descShortComplex]
  · simp [q, mappingCone.map, S, ShortComplex.cokernelSequence, mappingCone.descShortComplex]

private theorem coneComponents
    {P L G : CochainComplex B ℤ} (u : P ⟶ L) (q : G ⟶ mappingCone u) :
    ∃ (g : ∀ n : ℤ, G.X n ⟶ L.X n)
      (h : ∀ n : ℤ, G.X n ⟶ P.X (n + 1)),
      (∀ n : ℤ, g n = q.f n ≫ (mappingCone.snd u).v n n (add_zero n)) ∧
      (∀ n : ℤ, h n = q.f n ≫ (mappingCone.fst u).1.v n (n + 1) rfl) ∧
      (∀ n : ℤ, h n ≫ P.d (n + 1) (n + 1 + 1) +
        G.d n (n + 1) ≫ h (n + 1) = 0) ∧
      (∀ n : ℤ, g n ≫ L.d n (n + 1) =
        G.d n (n + 1) ≫ g (n + 1) - h n ≫ u.f (n + 1)) := by
  let g (n : ℤ) := q.f n ≫ (mappingCone.snd u).v n n (add_zero n)
  let h (n : ℤ) := q.f n ≫ (mappingCone.fst u).1.v n (n + 1) rfl
  refine ⟨g, h, fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_⟩
  · intro n
    have hh := congrArg (fun k ↦ q.f n ≫ k)
      (mappingCone.d_fst_v u n (n + 1) (n + 1 + 1) rfl rfl)
    rw [q.comm_assoc] at hh
    simp only [Preadditive.comp_neg] at hh
    have e : G.d n (n + 1) ≫ h (n + 1) =
        -(h n ≫ P.d (n + 1) (n + 1 + 1)) := by
      simpa only [h, Category.assoc] using hh
    rw [e, add_neg_cancel]
  · intro n
    have hh := congrArg (fun k ↦ q.f n ≫ k) (mappingCone.d_snd_v u n (n + 1) rfl)
    rw [q.comm_assoc] at hh
    simp only [Preadditive.comp_add] at hh
    dsimp [g, h]
    apply (eq_sub_iff_add_eq).2
    simpa only [Category.assoc, add_comm] using hh.symm
end General

private theorem totalization_column
    {a b : ℤ} (D : FiniteTwistingFamily R a b) (T : FiniteTwistingTotalization D)
    (q : ↥(Finset.Icc a b)) (n : ℤ) :
    T.P.d n (n + 1) ≫ (T.coordinates (n + 1)).hom ≫
        biproduct.π (fun p ↦ (D.G p).X (n + 1)) q =
      (T.coordinates n).hom ≫ biproduct.π (fun p ↦ (D.G p).X n) q ≫
        (D.G q).d n (n + 1) +
      ∑ r : {r : ↥(Finset.Icc a b) // r.val < q.val},
        (T.coordinates n).hom ≫ biproduct.π (fun p ↦ (D.G p).X n) r.val ≫
          D.τ r.val q r.property n := by
  classical
  apply (cancel_epi (T.coordinates n).inv).1
  apply biproduct.hom_ext'
  intro p
  simp only [Preadditive.comp_add, Preadditive.comp_sum,
    Iso.inv_hom_id_assoc]
  have hd := congrArg (fun k ↦ k ≫ (T.coordinates (n + 1)).hom ≫
    biproduct.π (fun p ↦ (D.G p).X (n + 1)) q) (T.differential p n)
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc,
    Iso.inv_hom_id_assoc] at hd
  rw [hd]
  by_cases hp : p = q
  · subst p
    simp only [biproduct.ι_π_self_assoc, biproduct.ι_π_self, Category.comp_id]
    have hleft : ∀ r : {r : ↥(Finset.Icc a b) // q.val < r.val},
        D.τ q r.val r.property n ≫
          biproduct.ι (fun t ↦ (D.G t).X (n + 1)) r.val ≫
            biproduct.π (fun t ↦ (D.G t).X (n + 1)) q = 0 := by
      intro r
      rw [biproduct.ι_π_ne _ (show r.val ≠ q from fun h ↦ by
        have hv := congrArg Subtype.val h
        have := r.property
        omega), comp_zero]
    have hright : ∀ r : {r : ↥(Finset.Icc a b) // r.val < q.val},
        biproduct.ι (fun t ↦ (D.G t).X n) q ≫
          biproduct.π (fun t ↦ (D.G t).X n) r.val ≫ D.τ r.val q r.property n = 0 := by
      intro r
      rw [biproduct.ι_π_ne_assoc _ (show q ≠ r.val from fun h ↦ by
        have hv := congrArg Subtype.val h
        have := r.property
        omega), zero_comp]
    simp only [hleft, hright, Finset.sum_const_zero, add_zero]
  · simp only [biproduct.ι_π_ne_assoc _ hp, biproduct.ι_π_ne _ hp,
      comp_zero, zero_comp, zero_add]
    by_cases hlt : p.val < q.val
    · rw [Finset.sum_eq_single (⟨q, hlt⟩ : {r : ↥(Finset.Icc a b) // p.val < r.val})]
      · rw [Finset.sum_eq_single
          (⟨p, hlt⟩ : {r : ↥(Finset.Icc a b) // r.val < q.val})]
        · simp
        · intro r _ hr
          rw [biproduct.ι_π_ne_assoc _ (by intro h; apply hr; exact Subtype.ext h.symm),
            zero_comp]
        · simp
      · intro r _ hr
        rw [biproduct.ι_π_ne _ (show r.val ≠ q from fun h ↦ hr (Subtype.ext h)), comp_zero]
      · simp
    · have hleft : ∀ r : {r : ↥(Finset.Icc a b) // p.val < r.val},
          D.τ p r.val r.property n ≫
            biproduct.ι (fun t ↦ (D.G t).X (n + 1)) r.val ≫
              biproduct.π (fun t ↦ (D.G t).X (n + 1)) q = 0 := by
        intro r
        rw [biproduct.ι_π_ne _ (show r.val ≠ q from fun h ↦ by
          have hv := congrArg Subtype.val h
          have := r.property
          exact hlt (by omega)), comp_zero]
      have hright : ∀ r : {r : ↥(Finset.Icc a b) // r.val < q.val},
          biproduct.ι (fun t ↦ (D.G t).X n) p ≫
            biproduct.π (fun t ↦ (D.G t).X n) r.val ≫ D.τ r.val q r.property n = 0 := by
        intro r
        rw [biproduct.ι_π_ne_assoc _ (show p ≠ r.val from fun h ↦ by
          have hv := congrArg Subtype.val h
          have := r.property
          exact hlt (by omega)), zero_comp]
      simp only [hleft, hright, Finset.sum_const_zero]

set_option maxHeartbeats 800000 in
-- The cone and coordinate comparisons elaborate several large dependent complex types.
/-- Adjoin just the next lower weight to an already augmented flat twisting family.
This is the induction step, with the higher-weight family supplied as input.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, mapping cylinders;
step 1 of lem-trf-finite-filtered-flat-model.
Proof: realize D by its finite twisting totalization and assemble A to a filtered map.
Its restriction into F^(a+1)M is a quasi-isomorphism: descend through the finitely many
higher grades, using the short exact sequences of consecutive steps and the homology
five lemma. Form Cone(P_tail -> F^aM). Compare it with the cone of the monomorphism
F^(a+1)M -> F^aM; the resulting map onto gr^aM is a quasi-isomorphism. Both terms of the
first cone are bounded above, hence it admits a bounded flat replacement G_a. Write its
components as g:G_a -> F^aM and h:G_a -> P_tail[1], and put tau_(a,q) equal to minus the
q-th component of h in the tail coordinates. The chain-map equations give both the
Maurer--Cartan identities involving a and the augmentation equation at a. Retain the old
complexes, twisting entries, components and graded maps at all larger weights. The new grade
map is the replacement map followed by the cone-to-quotient quasi-isomorphism. Its components
are exactly g followed by the quotient projection; all bounds and flatness claims follow
from the replacement and the unchanged higher-weight data. No extension class is lifted
through a flat object, which need not be projective.
(blueprint: lem-trf-finite-filtered-twisting-augmentation-extension). -/
theorem exists_finiteFiltered_twistingAugmentationExtension
    (a b : ℤ) (hab : a < b)
    (M : FilteredObject (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (hM : CochainComplex.minus _ M.obj) (hbottom : M.filtration.F (b + 1) = ⊥)
    (D : FiniteTwistingFamily R (a + 1) b) (A : FiniteFilteredTwistingAugmentation D M)
    (hflat : ∀ (p : ↥(Finset.Icc (a + 1) b)) (n : ℤ),
      SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n))
    (hgrade : ∀ p : ↥(Finset.Icc (a + 1) b), QuasiIso (A.grade p)) :
    ∃ (D' : FiniteTwistingFamily R a b) (A' : FiniteFilteredTwistingAugmentation D' M),
      (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D'.G p).X n)) ∧
      (∀ p : ↥(Finset.Icc a b), QuasiIso (A'.grade p)) := by
  classical
  let B := ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  obtain ⟨T, _, _, _⟩ := exists_finiteFilteredTwistingTotalization R (a + 1) b
    (by omega) D
  obtain ⟨f, hf, hfg⟩ := exists_finiteFiltered_twistingAugmentationMap D M A T
  let K : FilteredObject (CochainComplex B ℤ) := ⟨T.P, T.F⟩
  have hgrades (p : ℤ) (hp : a + 1 ≤ p) (hpb : p ≤ b) :
      QuasiIso (FilteredObject.gradedMapSteps f p) := by
    let q : ↥(Finset.Icc (a + 1) b) := ⟨p, Finset.mem_Icc.mpr ⟨hp, hpb⟩⟩
    have := hgrade q
    rw [← hfg q]
    infer_instance
  have hr := restriction_quasiIso_finite f (a + 1) b T.topWeight hbottom hgrades
  have htop : IsIso (T.F.F (a + 1)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 T.bottomWeight
  let fTail : T.P ⟶ (M.filtration.F (a + 1) : CochainComplex B ℤ) :=
    inv (T.F.F (a + 1)).arrow ≫ FilteredObject.restrictionSteps f (a + 1)
  have : QuasiIso fTail := by dsimp [fTail]; infer_instance
  let i := Subobject.ofLE (M.filtration.F (a + 1)) (M.filtration.F a)
    (M.filtration.F_succ_le a)
  let u := fTail ≫ i
  have hu (n : ℤ) : u.f n = (T.coordinates n).hom ≫ biproduct.desc
      (fun p : ↥(Finset.Icc (a + 1) b) ↦ A.component p n ≫
        (Subobject.ofLE (M.filtration.F p.val) (M.filtration.F a)
          (M.filtration.antitone (by have := (Finset.mem_Icc.mp p.property).1; omega))).f n) := by
    apply (cancel_mono ((M.filtration.F a).arrow.f n)).1
    have htail : fTail ≫ (M.filtration.F (a + 1)).arrow = f.hom := by
      simp [fTail, restriction_fac]
    have huf : u ≫ (M.filtration.F a).arrow = f.hom := by
      simp [u, i, Subobject.ofLE_arrow, htail]
    rw [← HomologicalComplex.comp_f, huf]
    apply (cancel_epi (T.coordinates n).inv).1
    apply biproduct.hom_ext'
    intro p
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_desc_assoc,
      ← HomologicalComplex.comp_f, Subobject.ofLE_arrow] using hf p n
  let N : ℕ := Finset.univ.sup (fun p ↦ (Classical.choose (D.bounded p)).toNat)
  have hTP : T.P.IsStrictlyLE N := by
    rw [T.P.isStrictlyLE_iff]
    intro n hn
    have hz : IsZero (⨁ fun p : ↥(Finset.Icc (a + 1) b) ↦ (D.G p).X n) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply biproduct.hom_ext'
      intro p
      have hb := Classical.choose_spec (D.bounded p) n
      have hn' : (Classical.choose (D.bounded p)).toNat ≤ N :=
        Finset.le_sup (f := fun p ↦ (Classical.choose (D.bounded p)).toNat)
          (Finset.mem_univ p)
      exact (hb (by omega)).eq_of_src _ _
    exact hz.of_iso (T.coordinates n)
  obtain ⟨N', hN'⟩ := hM
  have := hN'
  have hz (n : ℤ) (hn : max (N : ℤ) N' < n) : IsZero ((mappingCone u).X n) := by
    rw [mappingCone.isZero_X_iff]
    exact ⟨T.P.isZero_of_isStrictlyLE N (n + 1) (by omega),
      IsZero.of_mono ((M.filtration.F a).arrow.f n)
        (M.obj.isZero_of_isStrictlyLE N' n (by omega))⟩
  obtain ⟨G, q, hflat₀, hbG, hq⟩ := exists_finiteFiltered_boundedFlatReplacement R
    (mappingCone u) (max (N : ℤ) N') hz
  obtain ⟨c, hc, hcf⟩ := coneQuotientMap i fTail
  have := hq
  have := hc
  let γ : G ⟶ M.filtration.gradedPiece a := q ≫ c
  have hγq : QuasiIso γ := by dsimp [γ]; infer_instance
  obtain ⟨g, h, hgdef, hhdef, hh, hg⟩ := coneComponents u q
  let t (p : ↥(Finset.Icc (a + 1) b)) (n : ℤ) :=
    -(h n ≫ (T.coordinates (n + 1)).hom ≫
      biproduct.π (fun p ↦ (D.G p).X (n + 1)) p)
  have ht (p : ↥(Finset.Icc (a + 1) b)) (n : ℤ) :
      t p n ≫ (D.G p).d (n + 1) (n + 1 + 1) + G.d n (n + 1) ≫ t p (n + 1) +
        ∑ r : {r : ↥(Finset.Icc (a + 1) b) // r.val < p.val},
          t r.val n ≫ D.τ r.val p r.property (n + 1) = 0 := by
    have he := congrArg (fun k ↦ k ≫ (T.coordinates (n + 1 + 1)).hom ≫
      biproduct.π (fun p ↦ (D.G p).X (n + 1 + 1)) p) (hh n)
    simp only [Preadditive.add_comp, Category.assoc, zero_comp] at he
    rw [totalization_column D T p (n + 1)] at he
    simp only [Preadditive.comp_add, Preadditive.comp_sum] at he
    simp only [t, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
      Finset.sum_neg_distrib]
    have heN := congrArg Neg.neg he
    simp only [neg_add, neg_zero] at heN
    convert heN using 1
    abel
  have hg' (n : ℤ) :
      g n ≫ (Subobject.underlying.obj (M.filtration.F a)).d n (n + 1) =
        G.d n (n + 1) ≫ g (n + 1) +
          ∑ p : ↥(Finset.Icc (a + 1) b),
            t p n ≫ A.component p (n + 1) ≫
              (Subobject.ofLE (M.filtration.F p.val) (M.filtration.F a)
                (M.filtration.antitone (by
                  have := (Finset.mem_Icc.mp p.property).1
                  omega))).f (n + 1) := by
    rw [hg n, hu (n + 1), biproduct.desc_eq]
    simp only [Preadditive.comp_sum, Category.assoc, t, Preadditive.neg_comp,
      ← Finset.sum_neg_distrib, sub_eq_add_neg]
  have hγ (n : ℤ) : γ.f n =
      g n ≫ (M.filtration.complexQuotientπ a (a + 1) (by omega)).f n := by
    simp only [γ, HomologicalComplex.comp_f, hcf, hgdef, Category.assoc]
    rfl
  exact exists_finiteFiltered_prependTwisting hab D M A G ⟨max (N : ℤ) N', hbG⟩
    t ht g hg' γ hγ hflat₀ hflat hγq hgrade
end CochainComplex
