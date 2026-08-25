/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Finitely presented algebras descend along filtered colimits of rings

Let `R = colim Rᵢ` be a filtered colimit of commutative rings and let `S` be an `R`-algebra
of finite presentation. Then `S` is already defined over one of the `Rᵢ`, i.e. there is an
index `i` and an `Rᵢ`-algebra `T` of finite presentation with `S ≅ T ⊗[Rᵢ] R`.

## Main results

- `CommRingCat.exists_isPushout_quotient_span`: if `S` is the quotient of a polynomial ring
  over `R` by relations that are defined over an `R`-algebra `A`, then `S` is the base change
  of the corresponding quotient over `A`.
- `CommRingCat.exists_isPushout_of_finitePresentation`: the descent statement above.

## References

- [Stacks: Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
- [EGA IV, 8.8.2]
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits

namespace CommRingCat

/-- Let `π : A[x₁, …, xₙ] ⊗_A R = R[x₁, …, xₙ] → S` be a surjection whose kernel is generated
by polynomials `r x` with coefficients in `A`. Then `S` is the base change along `A ⟶ R` of
the quotient of `A[x₁, …, xₙ]` by the `r x`. -/
lemma exists_isPushout_quotient_span {A R S : CommRingCat.{u}} (φ : A ⟶ R) {n : ℕ}
    {γ : Type*} (r : γ → MvPolynomial (Fin n) A) (π : of (MvPolynomial (Fin n) R) ⟶ S)
    (hπ : Function.Surjective π)
    (hr : RingHom.ker π.hom = Ideal.span (Set.range fun x ↦ MvPolynomial.map φ.hom (r x))) :
    ∃ h : of (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range r)) ⟶ S,
      IsPushout φ (ofHom MvPolynomial.C ≫ ofHom (Ideal.Quotient.mk (Ideal.span (Set.range r))))
        (ofHom MvPolynomial.C ≫ π) h := by
  set K : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range r) with hK
  set q : of (MvPolynomial (Fin n) A) ⟶ of (MvPolynomial (Fin n) A ⧸ K) :=
    ofHom (Ideal.Quotient.mk K) with hq
  set ψ : of (MvPolynomial (Fin n) A) ⟶ of (MvPolynomial (Fin n) R) :=
    ofHom (MvPolynomial.map φ.hom) with hψ
  have hKle : K ≤ RingHom.ker (ψ ≫ π).hom := by
    rw [hK, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    change MvPolynomial.map φ.hom (r x) ∈ RingHom.ker π.hom
    rw [hr]
    exact Ideal.subset_span ⟨x, rfl⟩
  refine ⟨ofHom (Ideal.Quotient.lift K (ψ ≫ π).hom fun a ha ↦ RingHom.mem_ker.mp (hKle ha)), ?_⟩
  set h : of (MvPolynomial (Fin n) A ⧸ K) ⟶ S :=
    ofHom (Ideal.Quotient.lift K (ψ ≫ π).hom fun a ha ↦ RingHom.mem_ker.mp (hKle ha)) with hh
  -- The three facts about `q` and `h` that are used below.
  have hcomp : ∀ p : MvPolynomial (Fin n) A,
      h.hom (q.hom p) = π.hom (MvPolynomial.map φ.hom p) := by
    intro p
    rw [hh, hq]
    simp [hψ]
  have hqzero : ∀ x, q.hom (r x) = 0 := by
    intro x
    rw [hq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hK ▸ Ideal.subset_span ⟨x, rfl⟩)
  -- Evaluating a polynomial with coefficients in `A` at a cocone can be done over `A`.
  have key : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → ∀ p : MvPolynomial (Fin n) A,
        MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k)))
          (MvPolynomial.map φ.hom p) = v.hom (q.hom p) := by
    intro W u v huv p
    rw [MvPolynomial.eval₂_map]
    have h1 : u.hom.comp φ.hom = v.hom.comp (q.hom.comp MvPolynomial.C) := by
      have := congrArg CommRingCat.Hom.hom huv
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] using this
    have h2 : MvPolynomial.eval₂Hom (q.hom.comp MvPolynomial.C)
        (fun k ↦ q.hom (MvPolynomial.X k)) = q.hom :=
      MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun k ↦ by simp)
    have h4 : MvPolynomial.eval₂Hom (v.hom.comp (q.hom.comp MvPolynomial.C))
        (fun k ↦ v.hom (q.hom (MvPolynomial.X k))) = v.hom.comp q.hom := by
      rw [← MvPolynomial.comp_eval₂Hom, h2]
    rw [h1]
    simpa using DFunLike.congr_fun h4 p
  -- The descent map out of `S` attached to a cocone, and its defining property.
  have hker : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → RingHom.ker π.hom ≤
        RingHom.ker (MvPolynomial.eval₂Hom u.hom fun k ↦ v.hom (q.hom (MvPolynomial.X k))) := by
    intro W u v huv
    rw [hr, Ideal.span_le, Set.range_subset_iff]
    intro x
    change MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k)))
      (MvPolynomial.map φ.hom (r x)) = 0
    rw [key _ u v huv, hqzero, map_zero]
  set desc : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W),
      φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v → (S ⟶ W) :=
    fun W u v huv ↦ ofHom (RingHom.liftOfSurjective π.hom hπ ⟨_, hker W u v huv⟩) with hdescdef
  have hdesc : ∀ (W : CommRingCat.{u}) (u : R ⟶ W) (v : of (MvPolynomial (Fin n) A ⧸ K) ⟶ W)
      (huv : φ ≫ u = (ofHom MvPolynomial.C ≫ q) ≫ v) (p : MvPolynomial (Fin n) R),
      (desc W u v huv).hom (π.hom p) =
        MvPolynomial.eval₂ u.hom (fun k ↦ v.hom (q.hom (MvPolynomial.X k))) p := by
    intro W u v huv p
    rw [hdescdef]
    exact RingHom.liftOfSurjective_comp_apply π.hom hπ ⟨_, hker W u v huv⟩ p
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk _ (fun t ↦ desc _ t.inl t.inr t.condition)
    ?_ ?_ ?_⟩⟩
  · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change π.hom (MvPolynomial.C (φ.hom a)) = h.hom (q.hom (MvPolynomial.C a))
    rw [hcomp, MvPolynomial.map_C]
  · intro t
    refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
    change (desc _ t.inl t.inr t.condition).hom (π.hom (MvPolynomial.C a)) = t.inl.hom a
    rw [hdesc _ t.inl t.inr t.condition, MvPolynomial.eval₂_C]
  · intro t
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (desc _ t.inl t.inr t.condition).hom (h.hom (q.hom p)) = t.inr.hom (q.hom p)
    rw [hcomp, hdesc _ t.inl t.inr t.condition]
    exact key _ t.inl t.inr t.condition p
  · intro t m hm₁ hm₂
    have hmφ : m.hom.comp π.hom =
        MvPolynomial.eval₂Hom t.inl.hom (fun k ↦ t.inr.hom (q.hom (MvPolynomial.X k))) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun k ↦ ?_)
      · rw [MvPolynomial.eval₂Hom_C]
        exact congrArg (fun φ ↦ CommRingCat.Hom.hom φ a) hm₁
      · rw [MvPolynomial.eval₂Hom_X']
        change m.hom (π.hom (MvPolynomial.X k)) = t.inr.hom (q.hom (MvPolynomial.X k))
        rw [show π.hom (MvPolynomial.X k) = h.hom (q.hom (MvPolynomial.X k)) by
          rw [hcomp, MvPolynomial.map_X]]
        exact congrArg (fun φ ↦ CommRingCat.Hom.hom φ (q.hom (MvPolynomial.X k))) hm₂
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := hπ x
    change m.hom (π.hom y) = (desc _ t.inl t.inr t.condition).hom (π.hom y)
    rw [hdesc _ t.inl t.inr t.condition]
    exact DFunLike.congr_fun hmφ y

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ CommRingCat.{u})
  (c : Cocone F) [PreservesColimit F (forget CommRingCat)] {σ : Type*}

omit [IsFiltered J] [PreservesColimit F (forget CommRingCat)] in
/-- The polynomials over `F.obj j` that are visible in the colimit only grow along the
transition maps. -/
lemma range_map_ι_app_subset {j k : J} (α : j ⟶ k) :
    Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) ⊆
      Set.range (MvPolynomial.map (σ := σ) (c.ι.app k).hom) := by
  have h : (c.ι.app k).hom.comp (F.map α).hom = (c.ι.app j).hom :=
    congrArg CommRingCat.Hom.hom (c.w α)
  rintro _ ⟨p, rfl⟩
  exact ⟨MvPolynomial.map (F.map α).hom p, by rw [MvPolynomial.map_map, h]; rfl⟩

variable (hc : IsColimit c)

include hc in
/-- Every polynomial over a filtered colimit of rings is defined over a finite stage. -/
lemma exists_mem_range_map_ι_app (p : MvPolynomial σ c.pt) :
    ∃ j, p ∈ Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨j, y, hy⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) hc)
        (show ((forget CommRingCat).mapCocone c).pt from a)
    exact ⟨j, MvPolynomial.C y, by rw [MvPolynomial.map_C]; exact congrArg MvPolynomial.C hy⟩
  | add p q hp hq =>
    obtain ⟨j, p, rfl⟩ := hp
    obtain ⟨k, q, rfl⟩ := hq
    obtain ⟨p', hp'⟩ := range_map_ι_app_subset F c (IsFiltered.leftToMax j k) ⟨p, rfl⟩
    obtain ⟨q', hq'⟩ := range_map_ι_app_subset F c (IsFiltered.rightToMax j k) ⟨q, rfl⟩
    exact ⟨IsFiltered.max j k, p' + q', by rw [map_add]; exact congrArg₂ (· + ·) hp' hq'⟩
  | mul_X p n hp =>
    obtain ⟨j, p, rfl⟩ := hp
    exact ⟨j, p * MvPolynomial.X n, by
      rw [map_mul]
      exact congrArg (MvPolynomial.map (c.ι.app j).hom p * ·) (MvPolynomial.map_X _ _)⟩

include hc in
/-- Finitely many polynomials over a filtered colimit of rings are all defined over a common
finite stage. -/
lemma exists_forall_mem_range_map_ι_app (s : Finset (MvPolynomial σ c.pt)) :
    ∃ j, ∀ p ∈ s, p ∈ Set.range (MvPolynomial.map (σ := σ) (c.ι.app j).hom) := by
  classical
  choose j hj using fun p : s ↦ exists_mem_range_map_ι_app F c hc (p : MvPolynomial σ c.pt)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  refine ⟨k, fun p hp ↦ ?_⟩
  obtain ⟨α⟩ := hk (Finset.mem_image_of_mem j (Finset.mem_univ (⟨p, hp⟩ : s)))
  exact range_map_ι_app_subset F c α (hj ⟨p, hp⟩)

include hc in
/-- **Finitely presented algebras descend along filtered colimits of rings.**

If `S` is an algebra of finite presentation over the colimit `c.pt` of a filtered diagram `F`
of commutative rings, then `S` is the base change of an algebra `T` of finite presentation
over one of the `F.obj j`. -/
@[stacks 00R4]
theorem exists_isPushout_of_finitePresentation {S : CommRingCat.{u}} (f : c.pt ⟶ S)
    (hf : f.hom.FinitePresentation) :
    ∃ (j : J) (T : CommRingCat.{u}) (g : F.obj j ⟶ T) (_ : g.hom.FinitePresentation)
      (h : T ⟶ S), IsPushout (c.ι.app j) g f h := by
  classical
  letI := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  -- Present `S` as a quotient of a polynomial ring over `c.pt` by a finitely generated ideal.
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      ∃ π : CommRingCat.of (MvPolynomial (Fin n) c.pt) ⟶ S,
        ofHom MvPolynomial.C ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  -- All of the finitely many relations are already defined over some stage `i`.
  obtain ⟨i, hi⟩ := exists_forall_mem_range_map_ι_app F c hc s
  choose lift hlift using fun p : s ↦ hi p p.2
  have hrange : (↑s : Set (MvPolynomial (Fin n) c.pt)) =
      Set.range fun x ↦ MvPolynomial.map (c.ι.app i).hom (lift x) := by
    refine Set.ext fun p ↦ ⟨fun hp ↦ ⟨⟨p, hp⟩, hlift ⟨p, hp⟩⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact Set.mem_of_eq_of_mem (hx.symm.trans (hlift x)) (Finset.mem_coe.mpr x.2)
  obtain ⟨h, hpush⟩ := exists_isPushout_quotient_span (R := c.pt) (c.ι.app i) lift π hπ
    (by rw [← hs, hrange]; rfl)
  refine ⟨i, _, _, ?_, h, hpush⟩
  change ((Ideal.Quotient.mk (Ideal.span (Set.range lift))).comp MvPolynomial.C).FinitePresentation
  refine RingHom.FinitePresentation.comp
    (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_) ?_
  · rw [Ideal.mk_ker]
    exact ⟨Finset.univ.image lift, by simp⟩
  · have := RingHom.finitePresentation_algebraMap
      (A := (F.obj i : Type u)) (B := MvPolynomial (Fin n) (F.obj i))
    rw [MvPolynomial.algebraMap_eq] at this
    exact this.mpr inferInstance

end CommRingCat
