/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationData
/-! # Prepending one weight to a twisting family

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, mapping cylinders.
(blueprint: lem-trf-finite-filtered-prepend-twisting).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
attribute [local instance] hasSheafifyEssentiallySmallSite
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

@[reassoc (attr := simp)]
private theorem iso_hom_inv_f {X Y : CochainComplex (ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (e : X ≅ Y) (n : ℤ) : e.hom.f n ≫ e.inv.f n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

@[reassoc (attr := simp)]
private theorem iso_inv_hom_f {X Y : CochainComplex (ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (e : X ≅ Y) (n : ℤ) : e.inv.f n ≫ e.hom.f n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

set_option maxHeartbeats 1600000 in
-- Transporting the interval-indexed family repeatedly unfolds dependent complex types.
/-- Reindex the old family and adjoin one specified twisting row and augmentation component.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, mapping cylinders.
Proof: on the new smallest weight use G₀, t, g and γ; on every other weight retain the old
objects, twisting entries and augmentation components. Intermediate weights in an old
Maurer--Cartan equation are precisely the old intermediate weights. For a new equation they
are precisely the old weights below its endpoint. Reindex these finite sums; the equations
then become the supplied ones. The same reindexing proves the augmentation equations.
(blueprint: lem-trf-finite-filtered-prepend-twisting). -/
theorem exists_finiteFiltered_prependTwisting
    (_hab : a < b) (D : FiniteTwistingFamily R (a + 1) b)
    (M : FilteredObject (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (A : FiniteFilteredTwistingAugmentation D M)
    (G₀ : CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (G₀.X n))
    (t : ∀ (q : ↥(Finset.Icc (a + 1) b)) (n : ℤ), G₀.X n ⟶ (D.G q).X (n + 1))
    (ht : ∀ (q : ↥(Finset.Icc (a + 1) b)) (n : ℤ),
      t q n ≫ (D.G q).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ t q (n + 1) +
        ∑ r : {r : ↥(Finset.Icc (a + 1) b) // r.val < q.val},
          t r.val n ≫ D.τ r.val q r.property (n + 1) = 0)
    (g : ∀ n : ℤ, G₀.X n ⟶ (M.filtration.F a : CochainComplex _ ℤ).X n)
    (hg : ∀ n : ℤ,
      g n ≫ (Subobject.underlying.obj (M.filtration.F a)).d n (n + 1) =
        G₀.d n (n + 1) ≫ g (n + 1) +
          ∑ q : ↥(Finset.Icc (a + 1) b),
            t q n ≫ A.component q (n + 1) ≫
              (Subobject.ofLE (M.filtration.F q.val) (M.filtration.F a)
                (M.filtration.antitone (by
                  have := (Finset.mem_Icc.mp q.property).1
                  omega))).f (n + 1))
    (γ : G₀ ⟶ M.filtration.gradedPiece a)
    (hγ : ∀ n : ℤ, γ.f n =
      g n ≫ (M.filtration.complexQuotientπ a (a + 1) (by omega)).f n)
    (hflat₀ : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := R) (G₀.X n))
    (hflat : ∀ p n, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n))
    (hγq : QuasiIso γ) (hgrade : ∀ p, QuasiIso (A.grade p)) :
    ∃ (D' : FiniteTwistingFamily R a b) (A' : FiniteFilteredTwistingAugmentation D' M),
      (∀ p n, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D'.G p).X n)) ∧
      ∀ p, QuasiIso (A'.grade p) := by
  classical
  let old (p : ↥(Finset.Icc a b)) (hp : a + 1 ≤ p.val) : ↥(Finset.Icc (a + 1) b) :=
    ⟨p.val, Finset.mem_Icc.mpr ⟨hp, (Finset.mem_Icc.mp p.property).2⟩⟩
  have low (p : ↥(Finset.Icc a b)) (hp : ¬a + 1 ≤ p.val) : p.val = a := by
    have := (Finset.mem_Icc.mp p.property).1
    omega
  have upper (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) : a + 1 ≤ q.val := by
    have := (Finset.mem_Icc.mp p.property).1
    omega
  let G (p : ↥(Finset.Icc a b)) := if hp : a + 1 ≤ p.val then D.G (old p hp) else G₀
  let E (p : ↥(Finset.Icc a b)) (hp : a + 1 ≤ p.val) : G p ≅ D.G (old p hp) :=
    eqToIso (by simp only [G, dif_pos hp])
  let E₀ (p : ↥(Finset.Icc a b)) (hp : ¬a + 1 ≤ p.val) : G p ≅ G₀ :=
    eqToIso (by simp only [G, dif_neg hp])
  let τ (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) (n : ℤ) :
      (G p).X n ⟶ (G q).X (n + 1) :=
    if hp : a + 1 ≤ p.val then
      (E p hp).hom.f n ≫ D.τ (old p hp) (old q (upper p q hpq)) hpq n ≫
        (E q (upper p q hpq)).inv.f (n + 1)
    else (E₀ p hp).hom.f n ≫ t (old q (upper p q hpq)) n ≫
      (E q (upper p q hpq)).inv.f (n + 1)
  have hmc (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) (n : ℤ) :
      τ p q hpq n ≫ (G q).d (n + 1) (n + 1 + 1) +
        (G p).d n (n + 1) ≫ τ p q hpq (n + 1) +
        ∑ r : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val},
          τ p r.val r.property.1 n ≫ τ r.val q r.property.2 (n + 1) = 0 := by
    have hq := upper p q hpq
    by_cases hp : a + 1 ≤ p.val
    · let e : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val} ≃
          {r : ↥(Finset.Icc (a + 1) b) // p.val < r.val ∧ r.val < q.val} :=
        { toFun := fun r ↦ ⟨old r.val (upper p r.val r.property.1), r.property⟩
          invFun := fun r ↦ ⟨⟨r.val.val, Finset.mem_Icc.mpr
            ⟨by have := (Finset.mem_Icc.mp r.val.property).1; omega,
              (Finset.mem_Icc.mp r.val.property).2⟩⟩, r.property⟩
          left_inv := by intro r; rfl
          right_inv := by intro r; rfl }
      have hm (r : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val}) :
          a + 1 ≤ r.val.val := upper p r.val r.property.1
      have hs := Fintype.sum_equiv e
        (fun r ↦ D.τ (old p hp) (old r.val (hm r)) r.property.1 n ≫
          D.τ (old r.val (hm r)) (old q hq) r.property.2 (n + 1))
        (fun r ↦ D.τ (old p hp) r.val r.property.1 n ≫
          D.τ r.val (old q hq) r.property.2 (n + 1)) (fun _ ↦ rfl)
      have hh := D.maurerCartan (old p hp) (old q hq) hpq n
      rw [← hs] at hh
      apply (cancel_epi ((E p hp).inv.f n)).1
      apply (cancel_mono ((E q hq).hom.f (n + 1 + 1))).1
      simpa only [τ, dif_pos hp, dif_pos hq, hm, dite_true,
        Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sum,
        Preadditive.sum_comp, Category.assoc, HomologicalComplex.Hom.comm_assoc,
        iso_inv_hom_f_assoc, iso_inv_hom_f, iso_hom_inv_f_assoc,
        Category.comp_id, Category.id_comp, comp_zero, zero_comp] using hh
    · let e : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val} ≃
          {r : ↥(Finset.Icc (a + 1) b) // r.val < q.val} :=
        { toFun := fun r ↦ ⟨old r.val (upper p r.val r.property.1), r.property.2⟩
          invFun := fun r ↦ ⟨⟨r.val.val, Finset.mem_Icc.mpr
            ⟨by have := (Finset.mem_Icc.mp r.val.property).1; omega,
              (Finset.mem_Icc.mp r.val.property).2⟩⟩,
                ⟨by
                    change p.val < r.val.val
                    rw [low p hp]
                    have := (Finset.mem_Icc.mp r.val.property).1
                    omega,
                  r.property⟩⟩
          left_inv := by intro r; rfl
          right_inv := by intro r; rfl }
      have hm (r : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < q.val}) :
          a + 1 ≤ r.val.val := upper p r.val r.property.1
      have hs := Fintype.sum_equiv e
        (fun r ↦ t (old r.val (hm r)) n ≫
          D.τ (old r.val (hm r)) (old q hq) r.property.2 (n + 1))
        (fun r ↦ t r.val n ≫ D.τ r.val (old q hq) r.property (n + 1)) (fun _ ↦ rfl)
      have hh := ht (old q hq) n
      rw [← hs] at hh
      apply (cancel_epi ((E₀ p hp).inv.f n)).1
      apply (cancel_mono ((E q hq).hom.f (n + 1 + 1))).1
      simpa only [τ, dif_neg hp, dif_pos hq, hm, dite_true,
        Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sum,
        Preadditive.sum_comp, Category.assoc, HomologicalComplex.Hom.comm_assoc,
        iso_inv_hom_f_assoc, iso_inv_hom_f, iso_hom_inv_f_assoc,
        Category.comp_id, Category.id_comp, comp_zero, zero_comp] using hh
  let D' : FiniteTwistingFamily R a b :=
    { G := G
      bounded := fun p ↦ by
        dsimp [G]
        split
        · exact D.bounded _
        · exact hbounded
      τ := τ
      maurerCartan := hmc }
  let g' (p : ↥(Finset.Icc a b)) (n : ℤ) :
      (D'.G p).X n ⟶ (M.filtration.F p.val : CochainComplex _ ℤ).X n :=
    if hp : a + 1 ≤ p.val then (E p hp).hom.f n ≫ A.component (old p hp) n
    else (E₀ p hp).hom.f n ≫ g n ≫
      (eqToHom (congrArg (fun r ↦ Subobject.underlying.obj (M.filtration.F r))
        (low p hp).symm)).f n
  let γ' (p : ↥(Finset.Icc a b)) : D'.G p ⟶ M.filtration.gradedPiece p.val :=
    if hp : a + 1 ≤ p.val then (E p hp).hom ≫ A.grade (old p hp)
    else (E₀ p hp).hom ≫ γ ≫ eqToHom (congrArg M.filtration.gradedPiece (low p hp).symm)
  have hγ' (p : ↥(Finset.Icc a b)) (n : ℤ) : (γ' p).f n = g' p n ≫
      (M.filtration.complexQuotientπ p.val (p.val + 1) (by omega)).f n := by
    by_cases hp : a + 1 ≤ p.val
    · simp only [γ', g', dif_pos hp, HomologicalComplex.comp_f, A.grade_f, Category.assoc]
      rfl
    · rcases p with ⟨p, hp'⟩
      have hpa : p = a := low ⟨p, hp'⟩ hp
      subst p
      simp only [γ', g', dif_neg hp, HomologicalComplex.comp_f,
        HomologicalComplex.eqToHom_f, eqToHom_refl, Category.comp_id, hγ, Category.assoc]
  have hcomm (p : ↥(Finset.Icc a b)) (n : ℤ) :
      g' p n ≫ (Subobject.underlying.obj (M.filtration.F p.val)).d n (n + 1) =
        (D'.G p).d n (n + 1) ≫ g' p (n + 1) +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D'.τ p q.val q.property n ≫ g' q.val (n + 1) ≫
            (Subobject.ofLE (M.filtration.F q.val.val) (M.filtration.F p.val)
              (M.filtration.antitone (le_of_lt q.property))).f (n + 1) := by
    by_cases hp : a + 1 ≤ p.val
    · let e : {q : ↥(Finset.Icc a b) // p.val < q.val} ≃
          {q : ↥(Finset.Icc (a + 1) b) // p.val < q.val} :=
        { toFun := fun q ↦ ⟨old q.val (upper p q.val q.property), q.property⟩
          invFun := fun q ↦ ⟨⟨q.val.val, Finset.mem_Icc.mpr
            ⟨by have := (Finset.mem_Icc.mp q.val.property).1; omega,
              (Finset.mem_Icc.mp q.val.property).2⟩⟩, q.property⟩
          left_inv := by intro q; rfl
          right_inv := by intro q; rfl }
      have hm (q : {q : ↥(Finset.Icc a b) // p.val < q.val}) :
          a + 1 ≤ q.val.val := upper p q.val q.property
      have hs := Fintype.sum_equiv e
        (fun q ↦ D.τ (old p hp) (old q.val (hm q)) q.property n ≫
          A.component (old q.val (hm q)) (n + 1) ≫
            (Subobject.ofLE (M.filtration.F q.val.val) (M.filtration.F p.val)
              (M.filtration.antitone (le_of_lt q.property))).f (n + 1))
        (fun q ↦ D.τ (old p hp) q.val q.property n ≫ A.component q.val (n + 1) ≫
          (Subobject.ofLE (M.filtration.F q.val.val) (M.filtration.F p.val)
            (M.filtration.antitone (le_of_lt q.property))).f (n + 1)) (fun _ ↦ rfl)
      have hh := A.comm (old p hp) n
      rw [← hs] at hh
      apply (cancel_epi ((E p hp).inv.f n)).1
      simpa only [g', D', τ, dif_pos hp, hm, dite_true,
        Preadditive.comp_add, Preadditive.comp_sum, Category.assoc,
        HomologicalComplex.Hom.comm_assoc, iso_inv_hom_f_assoc,
        iso_hom_inv_f_assoc] using hh
    · let e : {q : ↥(Finset.Icc a b) // p.val < q.val} ≃ ↥(Finset.Icc (a + 1) b) :=
        { toFun := fun q ↦ old q.val (upper p q.val q.property)
          invFun := fun q ↦ ⟨⟨q.val, Finset.mem_Icc.mpr
            ⟨by have := (Finset.mem_Icc.mp q.property).1; omega,
              (Finset.mem_Icc.mp q.property).2⟩⟩,
                by
                  change p.val < q.val
                  rw [low p hp]
                  have := (Finset.mem_Icc.mp q.property).1
                  omega⟩
          left_inv := by intro q; rfl
          right_inv := by intro q; rfl }
      have hm (q : {q : ↥(Finset.Icc a b) // p.val < q.val}) :
          a + 1 ≤ q.val.val := upper p q.val q.property
      have hs := Fintype.sum_equiv e
        (fun q ↦ t (old q.val (hm q)) n ≫ A.component (old q.val (hm q)) (n + 1) ≫
          (Subobject.ofLE (M.filtration.F q.val.val) (M.filtration.F a)
            (M.filtration.antitone (by have := hm q; omega))).f (n + 1))
        (fun q ↦ t q n ≫ A.component q (n + 1) ≫
          (Subobject.ofLE (M.filtration.F q.val) (M.filtration.F a)
            (M.filtration.antitone (by
              have := (Finset.mem_Icc.mp q.property).1
              omega))).f (n + 1)) (fun _ ↦ rfl)
      have hh := hg n
      rw [← hs] at hh
      rcases p with ⟨p, hp'⟩
      have hpa : p = a := low ⟨p, hp'⟩ hp
      subst p
      apply (cancel_epi ((E₀ ⟨a, hp'⟩ hp).inv.f n)).1
      simpa only [g', D', τ, dif_neg hp, hm, dite_true,
        HomologicalComplex.eqToHom_f, eqToHom_refl, Category.comp_id,
        Preadditive.comp_add, Preadditive.comp_sum, Category.assoc,
        HomologicalComplex.Hom.comm_assoc, iso_inv_hom_f_assoc,
        iso_hom_inv_f_assoc] using hh
  let A' : FiniteFilteredTwistingAugmentation D' M :=
    { component := g'
      comm := hcomm
      grade := γ'
      grade_f := hγ' }
  refine ⟨D', A', ?_, ?_⟩
  · intro p n
    by_cases hp : a + 1 ≤ p.val
    · simpa only [D', G, dif_pos hp] using hflat (old p hp) n
    · simpa only [D', G, dif_neg hp] using hflat₀ n
  · intro p
    dsimp only [A', γ']
    split <;> infer_instance
end CochainComplex
