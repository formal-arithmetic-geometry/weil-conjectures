/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Defs
import WeilConjectures.AlgebraicGeometry.AffineGroupoidInvariantRankStrata
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Invariant rank pieces and gluing monic equations

Source: Stacks Project, Groupoid Schemes, Tags 03BI and 03BJ,
`lemma-finite-locally-free-disjoint-free` and the first paragraph of
`lemma-integral-over-invariants`; Schemes, Tag 01I5, `lemma-disjoint-union-affines`
(blueprint: lem-a1-affine-groupoid-rankwise-monic-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem groupoid_to_old
    {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
    {c : pullback s t ⟶ R} (h : Scheme.IsGroupoid s t e i c) :
    IsGroupoidScheme s t e i c where
  identity_source := h.source_id
  identity_target := h.target_id
  inverse_source := h.source_inv
  inverse_target := h.target_inv
  composition_source := h.source_comp
  composition_target := h.target_comp
  identity_comp H a hab := h.id_comp H a _ (by simp) (by simp)
  comp_identity H a hab := h.comp_id H a _ (by simp) (by simp)
  inverse_comp H a hab := h.inv_comp H a _ (by simp) (by simp)
  comp_inverse H a hab := h.comp_inv H a _ (by simp) (by simp)
  associative H a b d hab hbd hl hr :=
    h.assoc H (pullback.lift a b hab) (pullback.lift b d hbd) _ _
      (by simp) (by simp) (by simp) (by simp) (by simp)

private theorem groupoid_from_old
    {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
    {c : pullback s t ⟶ R} (h : IsGroupoidScheme s t e i c) :
    Scheme.IsGroupoid s t e i c := by
  have hp {H : Scheme.{u}} (p : H ⟶ pullback s t) :
      p = pullback.lift (p ≫ pullback.fst s t) (p ≫ pullback.snd s t)
        (by simp [Category.assoc, pullback.condition]) :=
    pullback.hom_ext (by simp) (by simp)
  refine ⟨h.identity_source, h.identity_target, h.inverse_source, h.inverse_target,
    h.composition_source, h.composition_target, ?_, ?_, ?_, ?_, ?_⟩
  · intro H a p h₁ h₂
    have heq : p = pullback.lift (a ≫ t ≫ e) a
        (by simp [Category.assoc, h.identity_source]) :=
      pullback.hom_ext (by simpa using h₁) (by simpa using h₂)
    rw [heq]
    exact h.identity_comp H a _
  · intro H a p h₁ h₂
    have heq : p = pullback.lift a (a ≫ s ≫ e)
        (by simp [Category.assoc, h.identity_target]) :=
      pullback.hom_ext (by simpa using h₁) (by simpa using h₂)
    rw [heq]
    exact h.comp_identity H a _
  · intro H a p h₁ h₂
    have heq : p = pullback.lift (a ≫ i) a
        (by simp [Category.assoc, h.inverse_source]) :=
      pullback.hom_ext (by simpa using h₁) (by simpa using h₂)
    rw [heq]
    exact h.inverse_comp H a _
  · intro H a p h₁ h₂
    have heq : p = pullback.lift a (a ≫ i)
        (by simp [Category.assoc, h.inverse_target]) :=
      pullback.hom_ext (by simpa using h₁) (by simpa using h₂)
    rw [heq]
    exact h.comp_inverse H a _
  · intro H p q r z hpq hr₁ hr₂ hz₁ hz₂
    have hab := congrArg (p ≫ ·) (pullback.condition (f := s) (g := t))
    have hbd := congrArg (q ≫ ·) (pullback.condition (f := s) (g := t))
    simp only [← Category.assoc] at hab hbd
    rw [← hpq] at hbd
    have hpeq : pullback.lift (p ≫ pullback.fst s t) (p ≫ pullback.snd s t) hab = p :=
      (hp p).symm
    have hqeq : pullback.lift (p ≫ pullback.snd s t) (q ≫ pullback.snd s t) hbd = q :=
      pullback.hom_ext (by simpa using hpq) (by simp)
    have hl : (p ≫ c) ≫ s = (q ≫ pullback.snd s t) ≫ t := by
      rw [Category.assoc, h.composition_source, ← Category.assoc, hpq]
      exact congrArg (q ≫ ·) (pullback.condition (f := s) (g := t))
    have hr : (p ≫ pullback.fst s t) ≫ s = (q ≫ c) ≫ t := by
      simpa only [Category.assoc, h.composition_target] using
        hab.trans (congrArg (· ≫ t) hpq)
    have hreq : pullback.lift (p ≫ c) (q ≫ pullback.snd s t) hl = r :=
      pullback.hom_ext (by simpa using hr₁.symm) (by simpa using hr₂.symm)
    have hzeq : pullback.lift (p ≫ pullback.fst s t) (q ≫ c) hr = z :=
      pullback.hom_ext (by simpa using hz₁.symm) (by simpa using hz₂.symm)
    have hassoc := h.associative H (p ≫ pullback.fst s t) (p ≫ pullback.snd s t)
      (q ≫ pullback.snd s t) hab hbd
    simp only [hpeq, hqeq] at hassoc
    simpa only [hreq, hzeq] using hassoc hl hr

private theorem sections_product
    (X : Scheme.{u}) {ι : Type*} (U : ι → X.Opens)
    (hd : Pairwise (fun r r' ↦ Disjoint (U r) (U r'))) (hc : iSup U = ⊤) :
    ∃ ρ : Γ(X, ⊤) ≃+* ∀ r, Γ((U r).toScheme, ⊤),
      ∀ a r, ρ a r = (U r).ι.appTop a := by
  classical
  let res (r : ι) : Γ(X, ⊤) →+* Γ(X, U r) :=
    (X.presheaf.map (homOfLE le_top : U r ⟶ ⊤).op).hom
  let R := RingHom.pi res
  have hinj : Function.Injective R := by
    intro a b hab
    exact X.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hc.ge a b
      (fun r ↦ congrFun hab r)
  have hsurj : Function.Surjective R := by
    intro a
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U a := by
      intro r r'
      by_cases heq : r = r'
      · subst r'
        rfl
      · apply TopCat.Presheaf.section_ext X.sheaf _ _ _
        intro x hx
        rw [(hd heq).eq_bot] at hx
        exact hx.elim
    obtain ⟨a, ha, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
      (fun _ ↦ homOfLE le_top) hc.ge a hcompat
    exact ⟨a, funext ha⟩
  let E := (RingEquiv.ofBijective R ⟨hinj, hsurj⟩).trans
    (RingEquiv.piCongrRight fun r ↦ (U r).topIso.symm.commRingCatIsoToRingEquiv)
  refine ⟨E, ?_⟩
  intro a r
  apply (ConcreteCategory.bijective_of_isIso (U r).topIso.hom).injective
  change (U r).topIso.hom ((U r).topIso.inv (res r a)) =
    (U r).topIso.hom ((U r).ι.appTop a)
  rw [Iso.inv_hom_id_apply]
  change res r a = ((U r).ι.appTop ≫ (U r).topIso.hom) a
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  rfl

/-- An affine finite locally free groupoid admits invariant rank pieces; restriction
identifies its coordinate and invariant rings with the corresponding finite products.
Monic equations of degree `r` on the pieces glue after multiplication by `X^(d-r)`.
The conditional assertion does not supply those equations.

Source: Stacks Project, Tags 03BI, 03BJ (first proof paragraph), and 01I5
(blueprint: lem-a1-affine-groupoid-rankwise-monic-gluing).

Proof, following the node's six steps:
1. Apply `lem-a1-affine-groupoid-invariant-rank-strata` to obtain finitely many positive
   ranks, nonempty affine clopen pieces, invariant arrow pieces, and the restricted
   groupoids of degree `r`. The groupoid laws are exactly
   `def-a1-scheme-groupoid-laws` (the two recorded groupoid predicates express the same laws).
2. For a nonempty set of pieces, induct on its cardinality and apply
   `lem-weil-pbc-sheaf-disjoint-union-product` to the structure sheaf. Together with
   `def-weil-affine-spectrum`, this identifies `A` and `B` with their section-ring
   products by restriction. Functoriality gives the source and target component formulas.
3. Those formulas and injectivity of the product map on `B` show that an element is
   invariant exactly when all its components are. Restrict the product isomorphism
   on `A` and its inverse to obtain the product isomorphism on the equalizer subrings.
4. For supplied monic degree-`r` polynomials, let `d` be the largest rank. The coefficients
   of `X^(d-r) * P r` below degree `d` give tuples in the invariant rings. Apply the
   inverse product isomorphism to each tuple and form `X^d` plus these lower terms.
   Its leading coefficient is one, and its restriction is precisely `X^(d-r) * P r`.
5. Evaluate the finite sum and use the restriction formulas. Its component is
   `a_r^(d-r) * P_r(a_r) = 0`; injectivity of the product isomorphism gives vanishing
   in `A`. These two steps use only `def-weil-polynomial-ring` and ring identities.
6. If there are no pieces, the cover forces the object scheme empty and hence the
   arrow scheme empty. Sections of the empty open are the zero ring (also obtained
   from the disjoint-union product with both opens empty). The spectrum section
   isomorphism makes `A`, `B`, and its invariant subring zero rings. The three
   restriction isomorphisms are the unique maps to empty products; `X` is monic
   since its leading coefficient is `0 = 1`, and annihilates the unique element.

`C` and `Cᵣ` are explicitly required to be Mathlib's equalizer subrings. The formulas
for `ρA` and `ρB` specify restriction using `Scheme.ΓSpecIso` and the open inclusions;
`ρC` is specified as their restriction. Monicity and natural degree `r` encode
`P_r = X^r + ∑_{j<r} p_{r,j} X^j` on each nonempty piece. The displayed formula for
`Q` uses exactly the coefficients of the padded polynomials and `ρC.symm`.
-/
theorem affineGroupoid_rankwise_monic_gluing
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] :
    ∃ (I : Finset ℕ) (U : I → (Spec A).Opens) (V : I → (Spec B).Opens)
      (s' t' : ∀ r : I, (V r).toScheme ⟶ (U r).toScheme)
      (e' : ∀ r : I, (U r).toScheme ⟶ (V r).toScheme)
      (i' : ∀ r : I, (V r).toScheme ⟶ (V r).toScheme)
      (c' : ∀ r : I, pullback (s' r) (t' r) ⟶ (V r).toScheme)
      (k : ∀ r : I, pullback (s' r) (t' r) ⟶ pullback s t)
      (C : Subring A) (Cᵣ : ∀ r : I, Subring Γ((U r).toScheme, ⊤))
      (ρA : A ≃+* ∀ r : I, Γ((U r).toScheme, ⊤))
      (ρB : B ≃+* ∀ r : I, Γ((V r).toScheme, ⊤))
      (ρC : C ≃+* ∀ r : I, Cᵣ r),
      (∀ r : I, 0 < r.1) ∧
      (∀ r : I, Nonempty (U r).toScheme ∧ IsClosed (U r : Set (Spec A)) ∧
        IsAffine (U r).toScheme) ∧
      Pairwise (fun r r' : I ↦ Disjoint (U r) (U r')) ∧
      (⨆ r : I, U r) = ⊤ ∧
      (∀ r : I, V r = s ⁻¹ᵁ U r ∧ V r = t ⁻¹ᵁ U r ∧ IsAffine (V r).toScheme ∧
        Scheme.IsGroupoid (s' r) (t' r) (e' r) (i' r) (c' r) ∧
        (s' r).IsFiniteLocallyFreeOfDegree r.1 ∧ (t' r).IsFiniteLocallyFreeOfDegree r.1 ∧
        s' r ≫ (U r).ι = (V r).ι ≫ s ∧ t' r ≫ (U r).ι = (V r).ι ≫ t ∧
        e' r ≫ (V r).ι = (U r).ι ≫ e ∧ i' r ≫ (V r).ι = (V r).ι ≫ i ∧
        k r ≫ pullback.fst s t = pullback.fst (s' r) (t' r) ≫ (V r).ι ∧
        k r ≫ pullback.snd s t = pullback.snd (s' r) (t' r) ≫ (V r).ι ∧
        c' r ≫ (V r).ι = k r ≫ c) ∧
      C = (Spec.preimage s).hom.eqLocus (Spec.preimage t).hom ∧
      (∀ r : I, Cᵣ r = (s' r).appTop.hom.eqLocus (t' r).appTop.hom) ∧
      (∀ (a : A) (r : I), ρA a r = (U r).ι.appTop ((Scheme.ΓSpecIso A).inv a)) ∧
      (∀ (b : B) (r : I), ρB b r = (V r).ι.appTop ((Scheme.ΓSpecIso B).inv b)) ∧
      (∀ (a : A) (r : I),
        ρB ((Spec.preimage s).hom a) r = (s' r).appTop (ρA a r) ∧
        ρB ((Spec.preimage t).hom a) r = (t' r).appTop (ρA a r)) ∧
      (∀ (a : C) (r : I), (ρC a r : Γ((U r).toScheme, ⊤)) = ρA (a : A) r) ∧
      (∀ (a : A) (P : ∀ r : I, Polynomial (Cᵣ r)), I.Nonempty →
        (∀ r : I, (P r).Monic ∧ (P r).natDegree = r.1 ∧
          (P r).eval₂ (Cᵣ r).subtype (ρA a r) = 0) →
        ∃ (d : ℕ) (Q : Polynomial C), d = I.sup id ∧
          Q = Polynomial.X ^ d + ∑ j ∈ Finset.range d,
            Polynomial.C (ρC.symm (fun r : I ↦
              ((Polynomial.X ^ (d - r.1)) * P r).coeff j)) * Polynomial.X ^ j ∧
          Q.Monic ∧
          (∀ r : I,
            Q.map ((Pi.evalRingHom (fun r : I ↦ Cᵣ r) r).comp ρC.toRingHom) =
              Polynomial.X ^ (d - r.1) * P r) ∧
          (∀ r : I, ρA (Q.eval₂ C.subtype a) r =
            (ρA a r) ^ (d - r.1) * (P r).eval₂ (Cᵣ r).subtype (ρA a r) ∧
            (ρA a r) ^ (d - r.1) * (P r).eval₂ (Cᵣ r).subtype (ρA a r) = 0) ∧
          Q.eval₂ C.subtype a = 0) ∧
      (IsEmpty (Spec A) → I = ∅ ∧ Subsingleton A ∧
        (Polynomial.X : Polynomial C).Monic ∧
        ∀ a : A, (Polynomial.X : Polynomial C).eval₂ C.subtype a = 0) := by
  classical
  obtain ⟨I, U, V, hpos, hU, hd, hc, hempty, hV⟩ :=
    affineGroupoid_exists_invariant_rank_strata s t e i c (groupoid_to_old hG)
  have hmaps := fun r ↦ (hV r).2.2.2
  choose s' t' e' i' c' k hmaps using hmaps
  obtain ⟨α, hα⟩ := sections_product (Spec A) U hd hc
  have hVeq : V = fun r ↦ s ⁻¹ᵁ U r := funext fun r ↦ (hV r).1
  have hdc : Pairwise (fun r r' ↦ Disjoint (V r) (V r')) := by
    intro r r' hne
    rw [hVeq]
    apply disjoint_iff.mpr
    rw [← Scheme.Hom.preimage_inf, (hd hne).eq_bot]
    rfl
  have hcc : iSup V = ⊤ := by
    rw [hVeq, ← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  obtain ⟨β, hβ⟩ := sections_product (Spec B) V hdc hcc
  let ρA := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.trans α
  let ρB := (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.trans β
  have hρA (a : A) (r : I) :
      ρA a r = (U r).ι.appTop ((Scheme.ΓSpecIso A).inv a) := hα _ r
  have hρB (b : B) (r : I) :
      ρB b r = (V r).ι.appTop ((Scheme.ΓSpecIso B).inv b) := hβ _ r
  have hcomp (f : Spec B ⟶ Spec A)
      (f' : ∀ r : I, (V r).toScheme ⟶ (U r).toScheme)
      (hf : ∀ r, f' r ≫ (U r).ι = (V r).ι ≫ f) (a : A) (r : I) :
      ρB ((Spec.preimage f).hom a) r = (f' r).appTop (ρA a r) := by
    rw [hρA, hρB]
    have hnat := Scheme.ΓSpecIso_inv_naturality (Spec.preimage f)
    simp only [Spec.map_preimage] at hnat
    have hr := congrArg Scheme.Hom.appTop (hf r)
    simp only [Scheme.Hom.comp_appTop] at hr
    change (((Spec.preimage f) ≫ (Scheme.ΓSpecIso B).inv) ≫ (V r).ι.appTop) a =
      (((Scheme.ΓSpecIso A).inv ≫ (U r).ι.appTop) ≫ (f' r).appTop) a
    rw [hnat, Category.assoc, ← hr, ← Category.assoc]
  have hs := hcomp s s' (fun r ↦ (hmaps r).2.2.2.1)
  have ht := hcomp t t' (fun r ↦ (hmaps r).2.2.2.2.1)
  let C := (Spec.preimage s).hom.eqLocus (Spec.preimage t).hom
  let Cᵣ := fun r ↦ (s' r).appTop.hom.eqLocus (t' r).appTop.hom
  let f : C →+* ∀ r : I, Cᵣ r := RingHom.pi fun r ↦
    { toFun := fun a ↦ ⟨ρA (a : A) r, by
        change (s' r).appTop (ρA (a : A) r) = (t' r).appTop (ρA (a : A) r)
        rw [← hs, ← ht, a.property]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply ρA.injective
    funext r
    exact congrArg Subtype.val (congrFun hab r)
  have hfsurj : Function.Surjective f := by
    intro b
    let a := ρA.symm (fun r ↦ (b r : Γ((U r).toScheme, ⊤)))
    have ha : a ∈ C := by
      apply ρB.injective
      funext r
      rw [hs, ht]
      simp only [a, RingEquiv.apply_symm_apply]
      exact (b r).property
    refine ⟨⟨a, ha⟩, ?_⟩
    funext r
    apply Subtype.ext
    exact congrFun (ρA.apply_symm_apply _) r
  let ρC := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hρC (a : C) (r : I) : (ρC a r : Γ((U r).toScheme, ⊤)) = ρA (a : A) r := rfl
  refine ⟨I, U, V, s', t', e', i', c', k, C, Cᵣ, ρA, ρB, ρC,
    hpos, hU, hd, hc, ?_, rfl, (fun _ ↦ rfl), hρA, hρB,
    (fun a r ↦ ⟨hs a r, ht a r⟩), hρC, ?_, ?_⟩
  · intro r
    exact ⟨(hV r).1, (hV r).2.1, (hV r).2.2.1,
      groupoid_from_old (hmaps r).1, (hmaps r).2⟩
  · intro a P _hI hP
    let d := I.sup id
    have hrle (r : I) : r.1 ≤ d := Finset.le_sup (f := id) r.property
    let q (r : I) := Polynomial.X ^ (d - r.1) * P r
    have hqm (r : I) : (q r).Monic := (Polynomial.monic_X_pow _).mul (hP r).1
    have hqd (r : I) : (q r).natDegree = d := by
      have hne : P r ≠ 0 := by
        intro hz
        have := (hP r).2.1
        rw [hz, Polynomial.natDegree_zero] at this
        have := hpos r
        omega
      have : Nontrivial (Cᵣ r) := by
        rcases subsingleton_or_nontrivial (Cᵣ r) with hsub | hnt
        · exact (hne (Subsingleton.elim _ _)).elim
        · exact hnt
      dsimp [q]
      rw [Polynomial.natDegree_X_pow_mul (d - r.1) hne, (hP r).2.1]
      have := hrle r
      omega
    let b (j : ℕ) := ρC.symm (fun r ↦ (q r).coeff j)
    let Q := Polynomial.X ^ d + ∑ j ∈ Finset.range d,
      Polynomial.C (b j) * Polynomial.X ^ j
    have hQm : Q.Monic := by
      apply Polynomial.monic_X_pow_add
      rw [← Fin.sum_univ_eq_sum_range]
      exact Polynomial.degree_sum_fin_lt _
    let ev (r : I) := (Pi.evalRingHom (fun r : I ↦ Cᵣ r) r).comp ρC.toRingHom
    have hQmap (r : I) : Q.map (ev r) = q r := by
      dsimp [Q]
      simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
      have hb (j : ℕ) : ev r (b j) = (q r).coeff j := by
        exact congrFun (ρC.apply_symm_apply _) r
      simp only [hb]
      exact ((hqm r).as_sum.trans (by rw [hqd])).symm
    have heval (r : I) : ρA (Q.eval₂ C.subtype a) r =
        (ρA a r) ^ (d - r.1) * (P r).eval₂ (Cᵣ r).subtype (ρA a r) := by
      let g := (Pi.evalRingHom (fun r : I ↦ Γ((U r).toScheme, ⊤)) r).comp ρA.toRingHom
      have hcoeff : g.comp C.subtype = (Cᵣ r).subtype.comp (ev r) := by
        ext x
        exact (hρC x r).symm
      change g (Q.eval₂ C.subtype a) = _
      rw [Polynomial.hom_eval₂, hcoeff, ← Polynomial.eval₂_map, hQmap]
      simp [q, g, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
    have hz (r : I) :
        (ρA a r) ^ (d - r.1) * (P r).eval₂ (Cᵣ r).subtype (ρA a r) = 0 := by
      rw [(hP r).2.2, mul_zero]
    refine ⟨d, Q, rfl, rfl, hQm, hQmap, (fun r ↦ ⟨heval r, hz r⟩), ?_⟩
    apply ρA.injective
    funext r
    simpa only [map_zero, Pi.zero_apply] using (heval r).trans (hz r)
  · intro hE
    have hsub : Subsingleton A := PrimeSpectrum.isEmpty_iff_subsingleton.mp hE
    exact ⟨hempty hE, hsub, Polynomial.monic_X, fun _ ↦ hsub.elim _ _⟩

end AlgebraicGeometry
