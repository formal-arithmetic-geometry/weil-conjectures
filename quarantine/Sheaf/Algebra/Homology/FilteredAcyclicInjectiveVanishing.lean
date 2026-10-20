/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
import Sheaf.CategoryTheory.EnoughStrictFilteredInjectives
import Sheaf.Paper.FiniteFilteredGradedExactness
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction

/-! # Maps from filtered acyclic complexes to filtered injectives

Source: Stacks Project, Derived Categories, Tag 05TX
(blueprint: lem-trf-filtered-acyclic-injective-vanishing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
open HomComplex Preadditive
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
omit [HasZeroObject D] in
private theorem contraction_aux {K L : CochainComplex D ℤ}
    (extend : ∀ (n : ℤ) (u : K.X n ⟶ L.X n), K.d (n - 1) n ≫ u = 0 →
      ∃ h : K.X (n + 1) ⟶ L.X n, K.d n (n + 1) ≫ h = u)
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ h : K.X (n + 2) ⟶ L.X (n + 1),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  have hm : n + 1 + 1 = n + 2 := by omega
  have hn : n + 1 - 1 = n := by omega
  have hh := extend (n + 1) u
  rw [hn, hm] at hh
  obtain ⟨β, hβ⟩ := hh hu
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]
omit [HasZeroObject D] in
open Cochain.InductionUp in
private theorem contraction {K L : CochainComplex D ℤ} (d : ℤ) [L.IsStrictlyGE d]
    (extend : ∀ (n : ℤ) (u : K.X n ⟶ L.X n), K.d (n - 1) n ≫ u = 0 →
      ∃ h : K.X (n + 1) ⟶ L.X n, K.d n (n + 1) ≫ h = u)
    (f : K ⟶ L) : Nonempty (Homotopy f 0) := by
  let X (n : ℕ) : Set (Cochain K L (-1)) :=
    Set.ofPred (fun α ↦ (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
  let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
    IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
  let φ (n : ℕ) (α : X n) : X (n + 1) :=
    ⟨_, (contraction_aux extend f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
      (by lia) α.2).choose_spec⟩
  have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp ↦ by
    dsimp [φ]
    rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  let k₀ := (n - d + 1).toNat
  rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]
end CochainComplex


namespace CategoryTheory.FilteredObject
variable {C : Type u} [Category.{v} C] [Abelian C]
private theorem factors_image_comp {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (P : Subobject Z) (h : P.Factors (a ≫ b)) :
    P.Factors ((imageSubobject a).arrow ≫ b) := by
  obtain ⟨l, hl⟩ := (Subobject.factors_iff _ _).1 h
  have hh : imageSubobject ((imageSubobject a).arrow ≫ b) ≤ P := by
    rw [← imageSubobject_comp_eq_of_epi (factorThruImageSubobject a)
      ((imageSubobject a).arrow ≫ b), ← Category.assoc, imageSubobject_arrow_comp]
    exact imageSubobject_le _ l hl
  exact Subobject.factors_of_le _ hh
    ((Subobject.factors_iff _ _).2
      ⟨factorThruImageSubobject _, imageSubobject_arrow_comp _⟩)

private theorem image_finite {X Y : C} (F : DecreasingFiltration X) (e : X ⟶ Y)
    [Epi e] (hF : F.IsFinite) : (F.image e).IsFinite := by
  obtain ⟨a, b, ha, hb⟩ := hF
  refine ⟨a, b, ?_, ?_⟩
  · change imageSubobject ((F.F a).arrow ≫ e) = ⊤
    have : IsIso (F.F a).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ha
    rw [imageSubobject_iso_comp]
    let : Epi (image.ι e) := epi_image_of_epi e
    have : IsIso (image.ι e) := isIso_of_mono_of_epi _
    exact (Subobject.mk_eq_top_of_isIso (image.ι e))
  · change imageSubobject ((F.F b).arrow ≫ e) = ⊥
    have hz : (F.F b).arrow = 0 := by rw [hb]; simp
    rw [hz, zero_comp, imageSubobject_zero]

private theorem exact_filtered_extension {X Y Z I : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0)
    (hY : Y.filtration.IsFinite) (hZ : Z.filtration.IsFinite)
    (hI : I.filtration.IsFinite) (hv : IsStrict v)
    (hex : (ShortComplex.mk u.hom v.hom hvu).Exact)
    (hinj : ∀ p : ℤ, Injective (I.filtration.gradedPiece p))
    (r : Y ⟶ I) (hr : u.hom ≫ r.hom = 0) :
    ∃ s : Z ⟶ I, v ≫ s = r := by
  let e := factorThruImage v.hom
  let m := image.ι v.hom
  let J : FilteredObject C := ⟨image v.hom, Y.filtration.image e⟩
  have hm : e ≫ m = v.hom := image.fac v.hom
  let t := hex.isColimitImage.desc (CokernelCofork.ofπ r.hom hr)
  have ht : e ≫ t = r.hom := hex.isColimitImage.fac _ WalkingParallelPair.one
  let j : J ⟶ Z := ⟨m, fun p ↦ by
    apply (Subobject.factors_iff _ _).1
    apply factors_image_comp ((Y.filtration.step p).arrow ≫ e) m
    simpa only [Category.assoc, hm] using
      (Subobject.factors_iff _ _).2 (v.preserves p)⟩
  let q : J ⟶ I := ⟨t, fun p ↦ by
    apply (Subobject.factors_iff _ _).1
    apply factors_image_comp ((Y.filtration.step p).arrow ≫ e) t
    simpa only [Category.assoc, ht] using
      (Subobject.factors_iff _ _).2 (r.preserves p)⟩
  have hj : ∀ p : ℤ,
      imageSubobject ((J.filtration.step p).arrow ≫ j.hom) =
        imageSubobject j.hom ⊓ Z.filtration.step p := by
    intro p
    rw [← imageSubobject_comp_eq_of_epi
      (factorThruImageSubobject ((Y.filtration.step p).arrow ≫ e))
      ((J.filtration.step p).arrow ≫ j.hom), ← Category.assoc]
    change imageSubobject
      ((factorThruImageSubobject ((Y.filtration.step p).arrow ≫ e) ≫
        (imageSubobject ((Y.filtration.step p).arrow ≫ e)).arrow) ≫ m) = _
    rw [imageSubobject_arrow_comp, Category.assoc, hm]
    have hvp := hv p
    have heq : imageSubobject v.hom = imageSubobject m := by
      simpa only [hm] using imageSubobject_comp_eq_of_epi e m
    simpa only [show restrictionSteps v p ≫ (Z.filtration.step p).arrow =
      (Y.filtration.step p).arrow ≫ v.hom from Classical.choose_spec (v.preserves p),
      heq] using hvp
  obtain ⟨s, hs⟩ := enough_strict_filtered_injectives.1
    (image_finite Y.filtration e hY) hZ hI j hj hinj q
  refine ⟨s, ?_⟩
  apply (filteredHomEquiv Y I).injective
  apply Subtype.ext
  have hh := congrArg (fun f : J ⟶ I ↦ f.hom) hs
  change m ≫ s.hom = t at hh
  change v.hom ≫ s.hom = r.hom
  rw [← hm, Category.assoc, hh, ht]
end CategoryTheory.FilteredObject


namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A graded-acyclic complex has no nonzero homotopy class of maps to a bounded-below
complex of filtered injectives. Enough injectives is unnecessary for this assertion.
Source: Stacks Project, Derived Categories, Tag 05TX.

Proof: represent the homotopy-category arrow by a chain map f. Choose a lower bound
N for the target and start the homotopy with zero below N. Given the homotopy through
degree n - 1, the residual f^n - h^n d_I kills d_A^(n - 1). Graded acyclicity and finite
filtered graded exactness identify the coimage of d_A^n with its strict image.
The residual therefore factors as a filtered map from that image to I^n. Extend it
across the strict image inclusion into A^(n + 1) by filtered injectivity, obtaining
h^(n + 1). The factorization equation is precisely f^n=d_A^n h^(n + 1) + h^n d_I.
Induction produces a filtered chain homotopy from f to zero. All homotopy components
are between the original objects, so prescribed filtration bounds impose no further
condition. The argument includes the zero category when b<a.
(blueprint: lem-trf-filtered-acyclic-injective-vanishing). -/
theorem filteredAcyclic_injective_vanishing (B : Option (ℤ × ℤ))
    (A I : FiniteFilteredHomotopyPlus C B false)
    (hA : ∀ p n : ℤ, IsZero ((HomotopyCategory.homologyFunctor C (.up ℤ) n).obj
      (((filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus.obj A).obj)))
    (hI : ∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p))
    (f : A ⟶ I) : f = 0 := by
  obtain ⟨A, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective A
  obtain ⟨I, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective I
  obtain ⟨f, rfl⟩ := (HomotopyCategory.Plus.quotient
    (FiniteFilteredObjects C B false)).map_surjective f
  obtain ⟨d, hd⟩ := I.property
  let := hd
  have extend (n : ℤ) (r : A.obj.X n ⟶ I.obj.X n)
      (hr : A.obj.d (n - 1) n ≫ r = 0) :
      ∃ h : A.obj.X (n + 1) ⟶ I.obj.X n, A.obj.d n (n + 1) ≫ h = r := by
    let u := (A.obj.d (n - 1) n).hom
    let v := (A.obj.d n (n + 1)).hom
    have hvu : u.hom ≫ v.hom = 0 := by
      exact congrArg (fun f ↦ f.hom.hom) (A.obj.d_comp_d (n - 1) n (n + 1))
    have hgr (p : ℤ) :
        (ShortComplex.mk (FilteredObject.gradedMapSteps u p)
          (FilteredObject.gradedMapSteps v p)
          (FilteredObject.gradedMapSteps_comp u v hvu p)).Exact := by
      let E := filteredEvaluation C B false (some p)
      have ha : ((E.mapHomologicalComplex (.up ℤ)).obj A.obj).ExactAt n := by
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact IsZero.of_iso (hA p n)
          ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).app
            ((E.mapHomologicalComplex (.up ℤ)).obj A.obj)).symm
      exact ((((E.mapHomologicalComplex (.up ℤ)).obj A.obj).exactAt_iff'
        (n - 1) n (n + 1) (by simp) (by simp)).1 ha)
    obtain ⟨_, hv, hex, _⟩ := FilteredObject.finite_filtered_graded_exactness u v hvu
      (A.obj.X (n - 1)).property.1 (A.obj.X n).property.1
      (A.obj.X (n + 1)).property.1 hgr
    have hr' : u.hom ≫ r.hom.hom = 0 :=
      congrArg (fun f ↦ f.hom.hom) hr
    obtain ⟨h, hh⟩ := FilteredObject.exact_filtered_extension u v hvu
      (A.obj.X n).property.1 (A.obj.X (n + 1)).property.1
      (I.obj.X n).property.1 hv hex (hI n) r.hom hr'
    exact ⟨ObjectProperty.homMk h, by
      apply (ObjectProperty.ι _).map_injective
      exact hh⟩
  obtain ⟨h⟩ := CochainComplex.contraction d extend f.hom
  apply (HomotopyCategory.Plus.ι _).map_injective
  change (HomotopyCategory.quotient _ _).map f.hom = 0
  rw [HomotopyCategory.eq_of_homotopy f.hom 0 h, Functor.map_zero]

end CategoryTheory
