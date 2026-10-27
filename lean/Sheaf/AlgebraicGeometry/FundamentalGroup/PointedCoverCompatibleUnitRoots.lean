/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.CategoryTheory.CofilteredSystem
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Compatible unit roots on the pointed universal finite étale cover

Source: Stacks 03PL, proof of lemma-kummer-sequence; algebra 00UB and 00UC;
Bhatt–Scholze §7.4; ILO IX Proposition 2.1, p.133.
(blueprint: lem-sfb-pointed-cover-compatible-unit-roots).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Polynomial
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The coordinate ring of the actual pointed limit cover of an affine scheme.
Source: Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-cover-compatible-unit-roots). -/
abbrev pointedCoverRing {E Ω : Type u} [CommRing E] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E)) :=
  Γ(cover s, ⊤)

/-- The structural map into the coordinate ring of the pointed cover.
Source: Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-cover-compatible-unit-roots). -/
def pointedCoverBase {E Ω : Type u} [CommRing E] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E)) :
    E →+* pointedCoverRing s :=
  (proj s).appTop.hom.comp (Scheme.ΓSpecIso (.of E)).inv.hom

/-- Evaluation at the marked geometric point of the cover.
Source: Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-cover-compatible-unit-roots). -/
def pointedCoverEval {E Ω : Type u} [CommRing E] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E)) :
    pointedCoverRing s →+* Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp (pt s).appTop.hom

private theorem root_cover_finite_etale
    {E : Type u} [CommRing E] (a : Eˣ) (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : E)) :
    IsFinite (Spec.map (CommRingCat.ofHom (AdjoinRoot.of
      ((Polynomial.X : Polynomial E) ^ n - Polynomial.C (a : E))))) ∧
    Etale (Spec.map (CommRingCat.ofHom (AdjoinRoot.of
      ((Polynomial.X : Polynomial E) ^ n - Polynomial.C (a : E))))) := by
  have := (Polynomial.monic_X_pow_sub_C (a : E) hn).finite_adjoinRoot
  have := AdjoinRoot.etale_X_pow_sub_C hn hu a.isUnit
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance

private def affinePull {T : Scheme.{u}} {R : Type u} [CommRing R]
    (f : T ⟶ Spec (.of R)) : R →+* Γ(T, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

private lemma affinePull_comp {T U : Scheme.{u}} {R : Type u} [CommRing R]
    (f : T ⟶ U) (g : U ⟶ Spec (.of R)) :
    affinePull (f ≫ g) = f.appTop.hom.comp (affinePull g) := by
  simp [affinePull, RingHom.comp_assoc]

private lemma affinePull_spec {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    affinePull (Spec.map (CommRingCat.ofHom f)) =
      (Scheme.ΓSpecIso (.of S)).inv.hom.comp f := by
  apply RingHom.ext
  intro r
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  exact congrArg (fun k ↦ k r) h.symm

private lemma affinePull_spec_comp {T : Scheme.{u}} {R S : Type u}
    [CommRing R] [CommRing S] (f : T ⟶ Spec (.of S)) (g : R →+* S) :
    affinePull (f ≫ Spec.map (CommRingCat.ofHom g)) = (affinePull f).comp g := by
  rw [affinePull_comp, affinePull_spec]
  rfl

private lemma exists_affine_pointed_lift
    {E Ω A : Type u} [CommRing E] [CommRing A] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E))
    (i : E →+* A) (hi : IsFinite (Spec.map (CommRingCat.ofHom i)))
    (he : Etale (Spec.map (CommRingCat.ofHom i)))
    (c : A →+* Ω) (hc : c.comp i = (Spec.homEquiv s).hom) :
    ∃ f : A →+* pointedCoverRing s,
      f.comp i = pointedCoverBase s ∧ (pointedCoverEval s).comp f = c := by
  let Y : (Spec (.of E)).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom i)) he, hi⟩
  let y : (FiniteEtale.fiber s).obj Y :=
    FiniteEtale.fiberMk s Y (Spec.map (CommRingCat.ofHom c)) (by
      change Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom i) = s
      rw [← Spec.map_comp]
      exact (congrArg Spec.map (CommRingCat.hom_ext hc)).trans (Spec.map_preimage s))
  refine ⟨affinePull (toObj s Y y), ?_, ?_⟩
  · have h := congrArg affinePull (toObj_hom s Y y)
    change affinePull (toObj s Y y ≫ Spec.map (CommRingCat.ofHom i)) = _ at h
    rw [affinePull_spec_comp] at h
    exact h
  · have h := congrArg (fun f ↦ affinePull f) (pt_toObj s Y y)
    change affinePull (pt s ≫ toObj s Y y) =
      affinePull (Spec.map (CommRingCat.ofHom c)) at h
    rw [affinePull_comp, affinePull_spec] at h
    apply RingHom.ext
    intro a
    have h' := congrArg (fun f : A →+* Γ(Spec (.of Ω), ⊤) ↦
      (Scheme.ΓSpecIso (.of Ω)).hom.hom (f a)) h
    simpa [pointedCoverEval] using h'

private lemma simple_roots_eq_or_isUnit_sub {R : Type u} [CommRing R]
    (hid : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : Polynomial R) (x y : R) (hx : f.IsRoot x) (hy : f.IsRoot y)
    (hu : IsUnit (f.derivative.eval x)) : x = y ∨ IsUnit (y - x) := by
  classical
  let q := f /ₘ (Polynomial.X - Polynomial.C x)
  have hq : q.eval x = f.derivative.eval x := by
    have h := congrArg (Polynomial.eval x)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f x)
    simpa [q] using h
  have hmul : (y - x) * q.eval y = 0 := by
    have h := congrArg (Polynomial.eval y) (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hx)
    simpa [q, hy.eq_zero] using h
  obtain ⟨v, hv⟩ := hq.symm ▸ hu
  obtain ⟨z, hz⟩ := Polynomial.sub_dvd_eval_sub y x q
  have heq : q.eval y = (v : R) + (y - x) * z := by rw [hv]; linear_combination hz
  let e : R := (↑v⁻¹ : R) * q.eval y
  have hed : e * (y - x) = 0 := by dsimp [e]; linear_combination (↑v⁻¹ : R) * hmul
  have he : IsIdempotentElem e := by
    change e * e = e
    have he' : e = 1 + (↑v⁻¹ : R) * (y - x) * z := by
      dsimp [e]
      rw [heq, mul_add, Units.inv_mul]
      ring
    calc
      e * e = e * (1 + (↑v⁻¹ : R) * (y - x) * z) := congrArg (e * ·) he'
      _ = e + (↑v⁻¹ : R) * z * (e * (y - x)) := by ring
      _ = e := by rw [hed]; ring
  rcases hid e he with h0 | h1
  · right
    have hqy : q.eval y = 0 := by
      have h := congrArg (fun a : R ↦ (v : R) * a) h0
      simpa [e] using h
    have hzunit : (y - x) * (-(↑v⁻¹ : R) * z) = 1 := by
      have h := congrArg (fun a : R ↦ -(↑v⁻¹ : R) * a) heq
      rw [hqy, mul_zero, mul_add, neg_mul, Units.inv_mul, neg_mul] at h
      linear_combination -h
    exact isUnit_iff_exists_inv.mpr ⟨_, hzunit⟩
  · left
    rw [h1, one_mul] at hed
    exact (sub_eq_zero.mp hed).symm

private lemma quotient_chain {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) :
    c / b * (b / a) = c / a := by
  by_cases ha : a = 0
  · simp [ha]
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha)
  rw [mul_assoc, Nat.div_mul_cancel hab, Nat.div_mul_cancel hbc,
    Nat.div_mul_cancel (dvd_trans hab hbc)]

private structure RootIndex (p : ℕ) where
  order : TameRootOrder p

private instance rootIndexPreorder (p : ℕ) : Preorder (RootIndex p) where
  le n m := n.order.val ∣ m.order.val
  le_refl n := dvd_refl n.order.val
  le_trans _ _ _ := dvd_trans

private instance rootIndexDirected (p : ℕ) : IsDirectedOrder (RootIndex p) :=
  ⟨fun n m ↦ ⟨⟨⟨n.order.val * m.order.val,
    Nat.mul_pos n.order.property.1 m.order.property.1,
    n.order.property.2.mul_left m.order.property.2⟩⟩,
    dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

private lemma exists_compatible_primitive_labels
    (p : ℕ) {E Ω : Type u} [CommRing E] [CharP E p] [Field Ω] [IsAlgClosed Ω]
    (s : E →+* Ω) :
    ∃ ζ : TameRootOrder p → Ω,
      (∀ n, IsPrimitiveRoot (ζ n) n.val) ∧
      ∀ n m, n.val ∣ m.val → ζ m ^ (m.val / n.val) = ζ n := by
  classical
  let F : (RootIndex p)ᵒᵖ ⥤ Type u :=
    { obj := fun n ↦ {z : Ω // IsPrimitiveRoot z n.unop.order.val}
      map := fun {m n} h ↦ ↾fun z ↦ ⟨z.val ^ (m.unop.order.val / n.unop.order.val),
        z.property.pow m.unop.order.property.1
          (Nat.div_mul_cancel (leOfHom h.unop)).symm⟩
      map_id := fun n ↦ by
        ext z
        change z.val ^ (n.unop.order.val / n.unop.order.val) = z.val
        rw [Nat.div_self n.unop.order.property.1, pow_one]
      map_comp := fun {l m n} f g ↦ by
        ext z
        change z.val ^ (l.unop.order.val / n.unop.order.val) =
          (z.val ^ (l.unop.order.val / m.unop.order.val)) ^
            (m.unop.order.val / n.unop.order.val)
        rw [← pow_mul, quotient_chain (leOfHom g.unop) (leOfHom f.unop)] }
  have hfinite (n : (RootIndex p)ᵒᵖ) : Finite (F.obj n) := by
    apply Finite.of_injective (fun z ↦
      (⟨z.val, (mem_primitiveRoots n.unop.order.property.1).mpr z.property⟩ :
        ↥(primitiveRoots n.unop.order.val Ω)))
    intro x y h
    exact Subtype.ext (congrArg (fun t : ↥(_ : Finset Ω) ↦ t.val) h)
  have hnonempty (n : (RootIndex p)ᵒᵖ) : Nonempty (F.obj n) := by
    let : Invertible (n.unop.order.val : E) := invertibleOfCoprime n.unop.order.property.2
    have : NeZero (n.unop.order.val : Ω) :=
      ⟨by simpa using ((isUnit_of_invertible (n.unop.order.val : E)).map s).ne_zero⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n.unop.order.val
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨z, hz⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n ↦ (z (Opposite.op ⟨n⟩)).val, fun n ↦ (z (Opposite.op ⟨n⟩)).property, ?_⟩
  intro n m h
  exact congrArg Subtype.val (hz (homOfLE (show (⟨n⟩ : RootIndex p) ≤ ⟨m⟩ from h)).op)

private lemma exists_compatible_scalar_labels
    (p : ℕ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (a : Ω) :
    ∃ b : TameRootOrder p → Ω,
      (∀ n, b n ^ n.val = a) ∧
      ∀ n m, n.val ∣ m.val → b m ^ (m.val / n.val) = b n := by
  classical
  let F : (RootIndex p)ᵒᵖ ⥤ Type u :=
    { obj := fun n ↦ {z : Ω // z ^ n.unop.order.val = a}
      map := fun {m n} h ↦ ↾fun z ↦ ⟨z.val ^ (m.unop.order.val / n.unop.order.val), by
        rw [← pow_mul, Nat.div_mul_cancel (leOfHom h.unop), z.property]⟩
      map_id := fun n ↦ by
        ext z
        change z.val ^ (n.unop.order.val / n.unop.order.val) = z.val
        rw [Nat.div_self n.unop.order.property.1, pow_one]
      map_comp := fun {l m n} f g ↦ by
        ext z
        change z.val ^ (l.unop.order.val / n.unop.order.val) =
          (z.val ^ (l.unop.order.val / m.unop.order.val)) ^
            (m.unop.order.val / n.unop.order.val)
        rw [← pow_mul, quotient_chain (leOfHom g.unop) (leOfHom f.unop)] }
  have hfinite (n : (RootIndex p)ᵒᵖ) : Finite (F.obj n) := by
    apply Finite.of_injective (fun z ↦
      (⟨z.val, (Polynomial.mem_nthRootsFinset n.unop.order.property.1 a).mpr z.property⟩ :
        ↥(Polynomial.nthRootsFinset n.unop.order.val a)))
    intro x y h
    exact Subtype.ext (congrArg (fun t : ↥(_ : Finset Ω) ↦ t.val) h)
  have hnonempty (n : (RootIndex p)ᵒᵖ) : Nonempty (F.obj n) :=
    let ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a n.unop.order.property.1
    ⟨⟨z, hz⟩⟩
  obtain ⟨z, hz⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n ↦ (z (Opposite.op ⟨n⟩)).val, fun n ↦ (z (Opposite.op ⟨n⟩)).property, ?_⟩
  intro n m h
  exact congrArg Subtype.val (hz (homOfLE (show (⟨n⟩ : RootIndex p) ≤ ⟨m⟩ from h)).op)

private lemma unit_roots_eq_or_isUnit_sub {R : Type u} [CommRing R]
    (hid : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (n : ℕ) (hn : IsUnit (n : R)) (a x y : R) (hx : x ^ n = a) (hy : y ^ n = a)
    (hu : IsUnit x) : x = y ∨ IsUnit (y - x) := by
  apply simple_roots_eq_or_isUnit_sub hid (X ^ n - C a) x y
  · simp [Polynomial.IsRoot, hx]
  · simp [Polynomial.IsRoot, hy]
  · simpa only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      eval_mul, eval_C, eval_pow, eval_X] using hn.mul (hu.pow (n - 1))

private lemma unit_roots_unique {R Ω : Type u} [CommRing R] [Field Ω]
    (hid : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (ev : R →+* Ω) (n : ℕ) (hn : IsUnit (n : R))
    (a x y : R) (hx : x ^ n = a) (hy : y ^ n = a)
    (hu : IsUnit x) (he : ev x = ev y) : x = y := by
  rcases unit_roots_eq_or_isUnit_sub hid n hn a x y hx hy hu with h | h
  · exact h
  · have := (h.map ev).ne_zero
    exact False.elim (this (by simp [he]))

private lemma exists_normalized_root
    (p : ℕ) {E Ω : Type u} [CommRing E] [CharP E p] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E))
    (a : Eˣ) (n : TameRootOrder p)
    (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)}) :
    ∃ b : pointedCoverRing s,
      b ^ n.val = pointedCoverBase s (a : E) ∧ pointedCoverEval s b = c.val := by
  let : Invertible (n.val : E) := invertibleOfCoprime n.property.2
  obtain ⟨hi, he⟩ := root_cover_finite_etale a n.val n.property.1.ne'
    (isUnit_of_invertible _)
  let f : Polynomial E := X ^ n.val - C (a : E)
  let g : AdjoinRoot f →+* Ω := AdjoinRoot.lift (Spec.homEquiv s).hom c.val (by
    simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C, c.property, sub_self])
  obtain ⟨h, hb, hv⟩ := exists_affine_pointed_lift s (AdjoinRoot.of f) hi he g
    (AdjoinRoot.lift_comp_of _)
  refine ⟨h (AdjoinRoot.root f), ?_, ?_⟩
  swap
  · exact (RingHom.congr_fun hv (AdjoinRoot.root f)).trans (AdjoinRoot.lift_root _)
  have hr : AdjoinRoot.root f ^ n.val = AdjoinRoot.of f (a : E) := by
    simpa only [f, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] using AdjoinRoot.eval₂_root f
  rw [← map_pow, hr]
  exact RingHom.congr_fun hb _

private lemma normalized_root_unique
    (p : ℕ) {E Ω : Type u} [CommRing E] [CharP E p] [Field Ω] [IsAlgClosed Ω]
    [ConnectedSpace (Spec (.of E))] (s : Spec (.of Ω) ⟶ Spec (.of E))
    (a : Eˣ) (n : TameRootOrder p) (x y : pointedCoverRing s)
    (hx : x ^ n.val = pointedCoverBase s (a : E))
    (hy : y ^ n.val = pointedCoverBase s (a : E))
    (he : pointedCoverEval s x = pointedCoverEval s y) : x = y := by
  let : Invertible (n.val : E) := invertibleOfCoprime n.property.2
  have hid := (Scheme.connectedSpace_iff_isIdempotentElem (cover s)).mp
    (inferInstanceAs (ConnectedSpace (cover s)))
  exact unit_roots_unique hid (pointedCoverEval s) n.val
    (by simpa using (isUnit_of_invertible (n.val : E)).map (pointedCoverBase s))
    _ x y hx hy
    ((isUnit_pow_iff n.property.1.ne').mp (hx.symm ▸ a.isUnit.map (pointedCoverBase s))) he

/-- Compatible primitive labels and all normalized unit-root sections, including pointed
naturality with transported labels. Sections of the root scheme are encoded by the
contravariant affine correspondence as homomorphisms out of `AdjoinRoot (X^n-a)`.
Their restrictions to E are the structural map, and their marked values are the prescribed
geometric labels. Uniqueness is uniqueness of the entire homomorphism and of its root value.

Source: Stacks 03PL, proof of lemma-kummer-sequence; 00UB, 00UC;
Bhatt–Scholze §7.4; ILO IX Proposition 2.1, p.133.
(blueprint: lem-sfb-pointed-cover-compatible-unit-roots).

Proof: (1) In the geometric field the primitive-root theorem identifies each group of
n-th roots with a cyclic group of order n. (2) Reduction of residue-unit groups is
surjective, so power transitions on primitive roots are surjective. (3) The orders
prime to p form a directed system under divisibility; the finite inverse-limit theorem
gives compatible primitive labels. (4) For each unit the nonempty finite root torsors
also have surjective power transitions, giving compatible labels, including an empty
family. (5) The monic quotient is finite free; Bezout makes n invertible, and the root
is invertible, so the derivative criterion makes the root cover étale.
(6) Split each finite cover on the existing pointed limit. A section of the resulting
finite disjoint union has one label since the limit is connected and nonempty. Its
marked point fixes that label uniquely. Evaluation gives the asserted root, whose
inverse is a^(-1) times its (n-1)-st power. The quotient universal property gives the
unique homomorphism. (7) Substitution X ↦ X^(m/n), and more generally X ↦ X^k, respects
geometric labels; uniqueness proves the power identities. (8) For distinct powers of
a primitive root, lift the split idempotent with values 1 and 0 to a polynomial P.
The identity P(v)-P(w)=(v-w)Q(v,w) proves that v-w is a unit; distinct geometric
values alone would not suffice. (9) Under a pointed pullback, including an embedding
of geometric fields, the pulled-back section has the transported label. The same
uniqueness proves naturality simultaneously with power maps. The initial compatible
geometric labels are chosen, not canonical. -/
theorem pointedCover_compatible_unit_roots
    (p : ℕ) (hp : p.Prime) {E Ω : Type u} [CommRing E] [CharP E p]
    [ConnectedSpace (Spec (.of E))] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of E)) :
    (∃ ζ : TameRootOrder p → Ω,
      (∀ n, IsPrimitiveRoot (ζ n) n.val) ∧
      ∀ n m, n.val ∣ m.val → ζ m ^ (m.val / n.val) = ζ n) ∧
    (∀ (a : Eˣ) (n : TameRootOrder p),
      IsFinite (Spec.map (CommRingCat.ofHom (AdjoinRoot.of
        ((Polynomial.X : Polynomial E) ^ n.val - Polynomial.C (a : E))))) ∧
      Etale (Spec.map (CommRingCat.ofHom (AdjoinRoot.of
        ((Polynomial.X : Polynomial E) ^ n.val - Polynomial.C (a : E)))))) ∧
    ∃ root : (a : Eˣ) → (n : TameRootOrder p) →
        {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)} → pointedCoverRing s,
      (∀ (a : Eˣ) (n : TameRootOrder p)
          (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)}),
        root a n c ^ n.val = pointedCoverBase s (a : E) ∧
        pointedCoverEval s (root a n c) = c.val ∧ IsUnit (root a n c) ∧
        (∀ b : pointedCoverRing s, b ^ n.val = pointedCoverBase s (a : E) →
          pointedCoverEval s b = c.val → b = root a n c) ∧
        ∃! f : AdjoinRoot ((Polynomial.X : Polynomial E) ^ n.val -
            Polynomial.C (a : E)) →+* pointedCoverRing s,
          (∀ e : E, f (AdjoinRoot.of _ e) = pointedCoverBase s e) ∧
          pointedCoverEval s (f (AdjoinRoot.root _)) = c.val) ∧
      (∀ (a : Eˣ) (n m : TameRootOrder p) (_h : n.val ∣ m.val)
          (c : {c : Ω // c ^ m.val = (Spec.homEquiv s).hom (a : E)})
          (d : {d : Ω // d ^ n.val = (Spec.homEquiv s).hom (a : E)}),
        c.val ^ (m.val / n.val) = d.val →
          root a m c ^ (m.val / n.val) = root a n d) ∧
      (∀ (a : Eˣ) (n : TameRootOrder p) (k : ℕ)
          (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)})
          (d : {d : Ω // d ^ n.val = (Spec.homEquiv s).hom ((a ^ k : Eˣ) : E)}),
        c.val ^ k = d.val → root a n c ^ k = root (a ^ k) n d) ∧
      (∀ (n : TameRootOrder p)
          (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom ((1 : Eˣ) : E)}),
        IsPrimitiveRoot c.val n.val → ∀ a b : ℕ, a % n.val ≠ b % n.val →
          IsUnit (root 1 n c ^ a - root 1 n c ^ b)) ∧
      (∀ (r : ℕ) (a : Fin r → Eˣ),
        ∃ b : Fin r → TameRootOrder p → Ω,
          (∀ j n, b j n ^ n.val = (Spec.homEquiv s).hom (a j : E)) ∧
          ∀ j n m, n.val ∣ m.val → b j m ^ (m.val / n.val) = b j n) ∧
      (∀ {E' Ω' : Type u} [CommRing E'] [CharP E' p]
          [ConnectedSpace (Spec (.of E'))] [Field Ω'] [IsAlgClosed Ω']
          (s' : Spec (.of Ω') ⟶ Spec (.of E')) (f : E →+* E') (ι : Ω →+* Ω')
          (g : pointedCoverRing s →+* pointedCoverRing s')
          (_hbase : g.comp (pointedCoverBase s) = (pointedCoverBase s').comp f)
          (_hpoint : (pointedCoverEval s').comp g = ι.comp (pointedCoverEval s))
          (a : Eˣ) (n : TameRootOrder p)
          (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)})
          (b : pointedCoverRing s'),
        b ^ n.val = pointedCoverBase s' (f (a : E)) →
        pointedCoverEval s' b = ι c.val → g (root a n c) = b) := by
  classical
  have _hp := hp.pos
  have hn (n : TameRootOrder p) : IsUnit (n.val : E) := by
    let : Invertible (n.val : E) := invertibleOfCoprime n.property.2
    exact isUnit_of_invertible _
  refine ⟨exists_compatible_primitive_labels p (Spec.homEquiv s).hom,
    fun a n ↦ root_cover_finite_etale a n.val n.property.1.ne' (hn n), ?_⟩
  choose root hpow heval using exists_normalized_root p s
  have hunit (a : Eˣ) (n : TameRootOrder p)
      (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)}) :
      IsUnit (root a n c) :=
    (isUnit_pow_iff n.property.1.ne').mp
      ((hpow a n c).symm ▸ a.isUnit.map (pointedCoverBase s))
  have huniq (a : Eˣ) (n : TameRootOrder p)
      (c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)})
      (b : pointedCoverRing s) (hb : b ^ n.val = pointedCoverBase s (a : E))
      (hc : pointedCoverEval s b = c.val) : b = root a n c :=
    normalized_root_unique p s a n b (root a n c) hb (hpow a n c)
      (hc.trans (heval a n c).symm)
  refine ⟨root, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a n c
    refine ⟨hpow a n c, heval a n c, hunit a n c, huniq a n c, ?_⟩
    let f : Polynomial E := X ^ n.val - C (a : E)
    let k : AdjoinRoot f →+* pointedCoverRing s :=
      AdjoinRoot.lift (pointedCoverBase s) (root a n c) (by simp [f, hpow])
    refine ⟨k, ⟨fun e ↦ AdjoinRoot.lift_of _ , ?_⟩, ?_⟩
    · change pointedCoverEval s (k (AdjoinRoot.root f)) = c.val
      rw [show k (AdjoinRoot.root f) = root a n c from AdjoinRoot.lift_root _]
      exact heval a n c
    · intro g hg
      have hgpow : g (AdjoinRoot.root f) ^ n.val = pointedCoverBase s (a : E) := by
        have hr : AdjoinRoot.root f ^ n.val = AdjoinRoot.of f (a : E) := by
          simpa [f, sub_eq_zero] using AdjoinRoot.eval₂_root f
        rw [← map_pow, hr, hg.1]
      exact AdjoinRoot.ringHom_ext (by
        ext e
        change g (AdjoinRoot.of f e) = k (AdjoinRoot.of f e)
        rw [hg.1, show k (AdjoinRoot.of f e) = pointedCoverBase s e from
          AdjoinRoot.lift_of _])
        ((huniq a n c _ hgpow hg.2).trans (AdjoinRoot.lift_root _).symm)
  · intro a n m h c d hc
    apply huniq a n d
    · rw [← pow_mul, Nat.div_mul_cancel h, hpow]
    · rw [map_pow, heval, hc]
  · intro a n k c d hc
    apply huniq (a ^ k) n d
    · rw [← pow_mul, mul_comm k n.val, pow_mul, hpow, ← map_pow]
      rfl
    · rw [map_pow, heval, hc]
  · intro n c hc a b hab
    have hr : root 1 n c ^ n.val = 1 := by simpa using hpow 1 n c
    have hid := (Scheme.connectedSpace_iff_isIdempotentElem (cover s)).mp
      (inferInstanceAs (ConnectedSpace (cover s)))
    have he : root 1 n c ^ b ≠ root 1 n c ^ a := by
      intro h
      have hv := congrArg (pointedCoverEval s) h
      simp only [map_pow, heval] at hv
      exact hab ((hc.pow_inj (Nat.mod_lt _ n.property.1) (Nat.mod_lt _ n.property.1)
        (by rw [← pow_eq_pow_mod a hc.pow_eq_one, ← pow_eq_pow_mod b hc.pow_eq_one];
            exact hv.symm)))
    exact (unit_roots_eq_or_isUnit_sub hid n.val
      (by simpa using (hn n).map (pointedCoverBase s)) 1
      (root 1 n c ^ b) (root 1 n c ^ a)
      (by rw [← pow_mul, mul_comm b n.val, pow_mul, hr, one_pow])
      (by rw [← pow_mul, mul_comm a n.val, pow_mul, hr, one_pow])
      ((hunit 1 n c).pow b)).resolve_left he
  · intro r a
    choose b hb hc using fun j ↦
      exists_compatible_scalar_labels p ((Spec.homEquiv s).hom (a j : E))
    exact ⟨b, hb, hc⟩
  · intro E' Ω' _ _ _ _ _ s' f ι g hbase hpoint a n c b hb hc
    apply normalized_root_unique p s' (Units.map f a) n (g (root a n c)) b
    · rw [← map_pow, hpow]
      exact RingHom.congr_fun hbase (a : E)
    · exact hb
    · have h := RingHom.congr_fun hpoint (root a n c)
      simpa only [RingHom.comp_apply, heval, hc] using h

end AlgebraicGeometry.Scheme.UniversalCover
