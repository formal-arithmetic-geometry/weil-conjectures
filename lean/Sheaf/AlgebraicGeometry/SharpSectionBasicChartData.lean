/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup

/-!
# Sharp basic-chart maps from global sections

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.1.8(i)--(ii), printed p.99,
and 3.1.1--3.1.4, printed p.98 (blueprint: lem-trf-sharp-section-basic-chart-data).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.FineFan

private theorem germ_local_eq (T : SheafedSpace CommMonCat.{u})
    (U : Opens T) (x : T) (hx : x ∈ U) (s t : T.presheaf.obj (op U))
    (h : germ T.presheaf U x hx s = germ T.presheaf U x hx t) :
    ∃ (W : Opens T) (i : W ⟶ U), x ∈ W ∧
      T.presheaf.map i.op s = T.presheaf.map i.op t := by
  obtain ⟨W, i, j, hij⟩ := CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq
    (stalkDiagram T.presheaf x) (i := op ⟨U, hx⟩) (j := op ⟨U, hx⟩) s t h
  have he : j = i := Subsingleton.elim _ _
  rw [he] at hij
  let k : W.unop.1 ⟶ U := (OpenNhds.inclusion x).map i.unop
  change T.presheaf.map k.op s = T.presheaf.map k.op t at hij
  exact ⟨W.unop.1, k, W.unop.2, hij⟩

private theorem section_eq_of_germs (T : SheafedSpace CommMonCat.{u})
    (U : Opens T) (s t : T.presheaf.obj (op U))
    (h : ∀ (x : T) (hx : x ∈ U),
      germ T.presheaf U x hx s = germ T.presheaf U x hx t) : s = t := by
  apply T.IsSheaf.section_ext
  intro x hx
  obtain ⟨W, i, hxW, e⟩ := germ_local_eq T U x hx s t (h x hx)
  exact ⟨W, i.le, hxW, e⟩

private theorem germ_restrict (T : SheafedSpace CommMonCat.{u})
    {U V : Opens T} (i : U ⟶ V) (x : T) (hx : x ∈ U)
    (s : T.presheaf.obj (op V)) :
    germ T.presheaf U x hx (T.presheaf.map i.op s) =
      germ T.presheaf V x (i.le hx) s := by
  let j : (⟨U, hx⟩ : OpenNhds x) ⟶ ⟨V, i.le hx⟩ := i
  exact ConcreteCategory.congr_hom
    (CategoryTheory.Limits.colimit.w (stalkDiagram T.presheaf x) j.op) s

private theorem sections_sharp (T : SheafedSpace CommMonCat.{u})
    (hT : ∀ x : T, IsSharp (stalk T.presheaf x))
    (U : Opens T) : IsSharp (T.presheaf.obj (op U)) := by
  intro s hs
  apply section_eq_of_germs T U s 1
  intro x hx
  rw [map_one]
  exact hT x _ (hs.map (germ T.presheaf U x hx).hom)

private theorem unit_locus_open (T : SheafedSpace CommMonCat.{u})
    (s : T.presheaf.obj (op ⊤)) :
    IsOpen {x : T | germ T.presheaf ⊤ x (by trivial) s = 1} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨W, i, hxW, e⟩ := germ_local_eq T ⊤ x (by trivial) s 1
    (hx.trans (map_one (germ T.presheaf ⊤ x (by trivial)).hom).symm)
  refine ⟨W, ?_, W.isOpen, hxW⟩
  intro y hy
  have he := congrArg (germ T.presheaf W y hy) e
  rw [germ_restrict, map_one, map_one] at he
  exact he

private theorem prime_mul_open {P : Type u} [CommMonoid P] (a b : P) :
    basicOpen (a * b) = basicOpen a ⊓ basicOpen b := by
  ext x
  change a * b ∉ x.carrier ↔ a ∉ x.carrier ∧ b ∉ x.carrier
  constructor
  · intro h
    exact ⟨fun ha ↦ h (by simpa [mul_comm] using x.smul_mem' b ha),
      fun hb ↦ h (x.smul_mem' a hb)⟩
  · rintro ⟨ha, hb⟩
    exact x.complement_mul a b ha hb

private theorem fraction_exists {P : Type u} [CommMonoid P] (a : P)
    (q : Algebra.faceLocalization P (Submonoid.powers a)) :
    ∃ (p : P) (n : ℕ),
      q.val = Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a ^ n)⁻¹ := by
  obtain ⟨p, f, hf⟩ := q.property
  obtain ⟨n, hn⟩ := f.property
  exact ⟨p, n, by simpa only [← hn, map_pow] using hf⟩

private theorem fraction_images {P M : Type u} [CommMonoid P] [CommMonoid M]
    (hinj : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (a : P) (g : P →* M) (ha : g a = 1) (p r : P) (n m : ℕ)
    (h : Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a ^ n)⁻¹ =
      Algebra.GrothendieckGroup.of r * (Algebra.GrothendieckGroup.of a ^ m)⁻¹) :
    g p = g r := by
  have e : p * a ^ m = r * a ^ n := by
    apply hinj
    simpa only [map_mul, map_pow] using (mul_inv_eq_mul_inv_iff_mul_eq_mul.mp h)
  have eg := congrArg g e
  simpa only [map_mul, map_pow, ha, one_pow, mul_one] using eg

private theorem localization_lift {P M : Type u} [CommMonoid P] [CommMonoid M]
    (hinj : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (a : P) (g : P →* M) (ha : g a = 1) :
    ∃ l : Algebra.faceLocalization P (Submonoid.powers a) →* M,
      (∀ (p : P) (n : ℕ) (q : Algebra.faceLocalization P (Submonoid.powers a)),
        q.val = Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a ^ n)⁻¹ →
        l q = g p) ∧
      (∀ μ : Algebra.faceLocalization P (Submonoid.powers a) →* M,
        (∀ (p : P) (q : Algebra.faceLocalization P (Submonoid.powers a)),
          q.val = Algebra.GrothendieckGroup.of p → μ q = g p) → μ = l) := by
  classical
  let num := fun q : Algebra.faceLocalization P (Submonoid.powers a) ↦
    (fraction_exists a q).choose
  let den := fun q : Algebra.faceLocalization P (Submonoid.powers a) ↦
    (fraction_exists a q).choose_spec.choose
  have rep (q : Algebra.faceLocalization P (Submonoid.powers a)) :
      q.val = Algebra.GrothendieckGroup.of (num q) *
        (Algebra.GrothendieckGroup.of a ^ den q)⁻¹ :=
    (fraction_exists a q).choose_spec.choose_spec
  let f := fun q : Algebra.faceLocalization P (Submonoid.powers a) ↦ g (num q)
  have formula (p : P) (n : ℕ) (q : Algebra.faceLocalization P (Submonoid.powers a))
      (hq : q.val = Algebra.GrothendieckGroup.of p *
        (Algebra.GrothendieckGroup.of a ^ n)⁻¹) : f q = g p :=
    fraction_images hinj a g ha _ _ _ _ ((rep q).symm.trans hq)
  let l : Algebra.faceLocalization P (Submonoid.powers a) →* M :=
    { toFun := f
      map_one' := by
        simpa only [map_one] using formula 1 0 1 (by simp)
      map_mul' := by
        intro q r
        rw [formula (num q * num r) (den q + den r) (q * r) (by
          change q.val * r.val = _
          rw [rep q, rep r, map_mul, pow_add]
          simp only [mul_inv_rev]
          ac_rfl)]
        exact g.map_mul _ _ }
  refine ⟨l, formula, ?_⟩
  intro μ hμ
  ext q
  obtain ⟨p, n, hq⟩ := fraction_exists a q
  let qp : Algebra.faceLocalization P (Submonoid.powers a) :=
    ⟨Algebra.GrothendieckGroup.of p, p, 1, by simp⟩
  let qd : Algebra.faceLocalization P (Submonoid.powers a) :=
    ⟨Algebra.GrothendieckGroup.of (a ^ n), a ^ n, 1, by simp⟩
  have he : q * qd = qp := by
    apply Subtype.ext
    change q.val * Algebra.GrothendieckGroup.of (a ^ n) = Algebra.GrothendieckGroup.of p
    rw [hq, map_pow, inv_mul_cancel_right]
  have hd : μ qd = 1 := by
    rw [hμ (a ^ n) qd rfl, map_pow, ha, one_pow]
  have hp := congrArg μ he
  rw [map_mul, hd, mul_one, hμ p qp rfl] at hp
  exact hp.trans (formula p n q hq).symm

private theorem sharpening_lift {L M : Type u} [CommMonoid L] [CommMonoid M]
    (hM : IsSharp M) (l : L →* M) :
    ∃ θ : Associates L →* M, ∀ q : L, θ (Associates.mk q) = l q := by
  let f : Associates L → M := Quotient.lift l (by
    rintro p q ⟨v, hv⟩
    rw [← hv, map_mul, hM _ (v.isUnit.map l), mul_one])
  refine ⟨{ toFun := f, map_one' := l.map_one, map_mul' := ?_ }, fun _ ↦ rfl⟩
  intro x y
  exact Quotient.inductionOn₂ x y (fun p q ↦ l.map_mul p q)

private theorem restrict_global (T : SheafedSpace CommMonCat.{u})
    {U V : Opens T} (i : U ⟶ V) (p : T.presheaf.obj (op ⊤)) :
    T.presheaf.map i.op (T.presheaf.map (homOfLE le_top).op p) =
      T.presheaf.map (homOfLE le_top).op p := by
  have e : (homOfLE (le_top : V ≤ ⊤)).op ≫ i.op =
      (homOfLE (le_top : U ≤ ⊤)).op := Subsingleton.elim _ _
  exact (ConcreteCategory.congr_hom (T.presheaf.map_comp _ _) p).symm.trans
    (congrArg (fun f ↦ T.presheaf.map f p) e)

private theorem cross_fraction_images {P M : Type u} [CommMonoid P] [CommMonoid M]
    (hinj : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (a b : P) (g : P →* M) (ha : g a = 1) (hb : g b = 1)
    (p r : P) (n m : ℕ)
    (h : Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a ^ n)⁻¹ =
      Algebra.GrothendieckGroup.of r * (Algebra.GrothendieckGroup.of b ^ m)⁻¹) :
    g p = g r := by
  have e : p * b ^ m = r * a ^ n := by
    apply hinj
    simpa only [map_mul, map_pow] using (mul_inv_eq_mul_inv_iff_mul_eq_mul.mp h)
  have eg := congrArg g e
  simpa only [map_mul, map_pow, ha, hb, one_pow, mul_one] using eg

/-- Global sections give a continuous prime map and compatible sharpened chart maps.
Multiplicative notation translates additive zero to `1` and `p - n*a` to
`of p * (of a ^ n)⁻¹`. The open `V a` is both the unit-germ locus and the inverse
image of `D(a)`. The formula on ambient fractions specifies the localization lift;
its uniqueness is tested on extensions of the numerator map. `Associates` is the
quotient by units. For an inclusion of basic opens, equal ambient fractions encode
exactly the localization-induced restriction in `affineFan_localization_sections`.
The final clause records both restriction maps on the overlap `D(a*b)`.

Source: ILO VIII, Lemma 3.1.8(i)--(ii), p.99; 3.1.1--3.1.4, p.98
(blueprint: lem-trf-sharp-section-basic-chart-data).

Proof:
1. If two sections multiply to `1`, their germs do also. Sharp stalks make the
   first germ `1`. Local equality of germs and sheaf separation give equality of
   sections. The empty cover proves the same assertion on the empty open.
2. For each point, take the elements whose image germ is not `1`. The complement
   is multiplicatively closed. Sharpness shows that a product involving an element
   of the ideal cannot have germ `1`, so this is a proper prime, possibly empty.
3. The locus where a germ is `1` is open by the definition of germs; sheaf separation
   makes the restricted section `1`. These loci are the inverse images of the basic
   opens and prove continuity using `def-trf-fine-fan-blowup`.
4. On `V a`, send a fraction `p/a^n` to the restriction of `φ p`. Injectivity into
   the completion and the fact that `φ a` restricts to `1` prove well-definedness.
   Products of representatives prove multiplicativity. Every extension sends
   `a⁻¹` to `1`, proving uniqueness.
5. Sharpness of sections makes the lift kill every unit, so it descends uniquely
   through `Associates.mk` to the sharpening.
6. For `D(b) ⊆ D(a)`, the localization restriction of
   `lem-trf-affine-fan-localization-sections` preserves the ambient fraction.
   Numerators restrict to the same `φ p`, and inverse denominators map to `1`;
   hence the restriction square commutes.
7. The prime property gives `D(a) ∩ D(b) = D(a*b)` and thus the same identity for
   the inverse images. Apply the preceding restriction squares to the two
   inclusions of `D(a*b)`: both maps become `θ (a*b)` on the overlap.
-/
theorem sharp_section_basic_chart_data
    (T : SheafedSpace CommMonCat.{u}) (hT : ∀ x : T, IsSharp (stalk T.presheaf x))
    (P : Type u) [CommMonoid P] (hP : IsFine P) (sP : IsSharp P)
    (φ : P →* T.presheaf.obj (op ⊤)) :
    (∀ U : Opens T, IsSharp (T.presheaf.obj (op U))) ∧
    ∃ (h : T.carrier ⟶ TopCat.of (MonoidPrime P)) (V : P → Opens T),
      (∀ x : T, (h x).carrier = {p : P | germ T.presheaf ⊤ x (by trivial) (φ p) ≠ 1}) ∧
      (∀ a : P, (V a : Set T) = {x : T | germ T.presheaf ⊤ x (by trivial) (φ a) = 1}) ∧
      (∀ a : P, V a = (Opens.map h).obj (basicOpen a)) ∧
      (∀ a : P, T.presheaf.map (homOfLE le_top).op (φ a) = (1 : T.presheaf.obj (op (V a)))) ∧
      ∃ (lam : ∀ a : P, Algebra.faceLocalization P (Submonoid.powers a) →*
          T.presheaf.obj (op (V a)))
        (θ : ∀ a : P, Associates (Algebra.faceLocalization P (Submonoid.powers a)) →*
          T.presheaf.obj (op (V a))),
        (∀ (a p : P) (n : ℕ) (q : Algebra.faceLocalization P (Submonoid.powers a)),
          q.val = Algebra.GrothendieckGroup.of p * (Algebra.GrothendieckGroup.of a ^ n)⁻¹ →
          lam a q = T.presheaf.map (homOfLE le_top).op (φ p)) ∧
        (∀ (a : P) (μ : Algebra.faceLocalization P (Submonoid.powers a) →*
            T.presheaf.obj (op (V a))),
          (∀ (p : P) (q : Algebra.faceLocalization P (Submonoid.powers a)),
            q.val = Algebra.GrothendieckGroup.of p →
            μ q = T.presheaf.map (homOfLE le_top).op (φ p)) → μ = lam a) ∧
        (∀ (a : P) (q : Algebra.faceLocalization P (Submonoid.powers a)),
          IsUnit q → lam a q = 1) ∧
        (∀ (a : P) (q : Algebra.faceLocalization P (Submonoid.powers a)),
          θ a (Associates.mk q) = lam a q) ∧
        (∀ (a b : P), basicOpen b ≤ basicOpen a →
          ∃ i : V b ⟶ V a,
            ∀ (q : Algebra.faceLocalization P (Submonoid.powers a))
              (r : Algebra.faceLocalization P (Submonoid.powers b)),
              r.val = q.val →
              T.presheaf.map i.op (θ a (Associates.mk q)) = θ b (Associates.mk r)) ∧
        (∀ a b : P,
          basicOpen (a * b) = basicOpen a ⊓ basicOpen b ∧ V (a * b) = V a ⊓ V b ∧
          ∃ (i : V (a * b) ⟶ V a) (j : V (a * b) ⟶ V b),
            ∀ (q : Algebra.faceLocalization P (Submonoid.powers a))
              (r : Algebra.faceLocalization P (Submonoid.powers b))
              (s : Algebra.faceLocalization P (Submonoid.powers (a * b))),
              (s.val = q.val →
                T.presheaf.map i.op (θ a (Associates.mk q)) = θ (a * b) (Associates.mk s)) ∧
              (s.val = r.val →
                T.presheaf.map j.op (θ b (Associates.mk r)) = θ (a * b) (Associates.mk s))) := by
  classical
  have hs := sections_sharp T hT
  let f (x : T) : P →* stalk T.presheaf x :=
    (germ T.presheaf ⊤ x (by trivial)).hom.comp φ
  let prime (x : T) : MonoidPrime P :=
    { carrier := {p | f x p ≠ 1}
      smul_mem' := by
        intro a b hb hab
        apply hb
        change f x (a * b) = 1 at hab
        have hu : IsUnit (f x a * f x b) := by
          rw [← map_mul, hab]
          exact isUnit_one
        exact hT x _ (isUnit_of_mul_isUnit_right hu)
      proper := by
        intro e
        have he : (1 : P) ∈ ({p | f x p ≠ 1} : Set P) := by rw [e]; trivial
        have hunit (p : P) (hp : IsUnit p) : f x p = 1 := by
          rw [sP p hp, map_one]
        exact he (hunit 1 isUnit_one)
      complement_mul := by
        intro a b ha hb
        change ¬f x (a * b) ≠ 1
        simp only [Set.mem_ofPred_eq, not_not] at ha hb ⊢
        rw [map_mul, ha, hb, mul_one] }
  have hc : Continuous prime := by
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨a, rfl⟩
    convert unit_locus_open T (φ a) using 1
    ext x
    change (¬f x a ≠ 1) ↔ _
    simp only [not_not]
    rfl
  let h : T.carrier ⟶ TopCat.of (MonoidPrime P) := TopCat.ofHom ⟨prime, hc⟩
  let V (a : P) : Opens T := (Opens.map h).obj (basicOpen a)
  have hV (a : P) :
      (V a : Set T) = {x : T | germ T.presheaf ⊤ x (by trivial) (φ a) = 1} := by
    ext x
    change (¬f x a ≠ 1) ↔ _
    simp only [not_not]
    rfl
  have hv (a : P) : T.presheaf.map (homOfLE le_top).op (φ a) =
      (1 : T.presheaf.obj (op (V a))) := by
    apply section_eq_of_germs T (V a)
    intro x hx
    rw [germ_restrict, map_one]
    exact (Set.ext_iff.mp (hV a) x).mp hx
  let g (a : P) : P →* T.presheaf.obj (op (V a)) :=
    (T.presheaf.map (homOfLE le_top).op).hom.comp φ
  have ga (a : P) : g a a = 1 := hv a
  choose lam hformula hunique using fun a ↦ localization_lift hP.2 a (g a) (ga a)
  choose θ hθ using fun a ↦ sharpening_lift (hs (V a)) (lam a)
  have compat (a b : P) (hab : basicOpen b ≤ basicOpen a) :
      ∃ i : V b ⟶ V a,
        ∀ (q : Algebra.faceLocalization P (Submonoid.powers a))
          (r : Algebra.faceLocalization P (Submonoid.powers b)),
          r.val = q.val →
          T.presheaf.map i.op (θ a (Associates.mk q)) = θ b (Associates.mk r) := by
    let i : V b ⟶ V a := homOfLE (fun _ hx ↦ hab hx)
    refine ⟨i, ?_⟩
    intro q r hrq
    obtain ⟨p, n, hp⟩ := fraction_exists a q
    obtain ⟨t, m, ht⟩ := fraction_exists b r
    rw [hθ, hθ, hformula a p n q hp, hformula b t m r ht]
    change T.presheaf.map i.op (T.presheaf.map (homOfLE le_top).op (φ p)) = g b t
    rw [restrict_global]
    have ha : g b a = 1 := by
      have e := congrArg (T.presheaf.map i.op) (hv a)
      rw [restrict_global, map_one] at e
      exact e
    exact cross_fraction_images hP.2 a b (g b) ha (ga b) p t n m
      (hp.symm.trans (hrq.symm.trans ht))
  refine ⟨hs, h, V, fun _ ↦ rfl, hV, fun _ ↦ rfl, hv, lam, θ,
    hformula, hunique, ?_, hθ, compat, ?_⟩
  · intro a q hq
    exact hs (V a) _ (hq.map (lam a))
  · intro a b
    have he := prime_mul_open a b
    have hve : V (a * b) = V a ⊓ V b := by
      ext x
      change h x ∈ basicOpen (a * b) ↔ h x ∈ basicOpen a ⊓ basicOpen b
      rw [he]
    have ha : basicOpen (a * b) ≤ basicOpen a := he.le.trans inf_le_left
    have hb : basicOpen (a * b) ≤ basicOpen b := he.le.trans inf_le_right
    obtain ⟨i, hi⟩ := compat a (a * b) ha
    obtain ⟨j, hj⟩ := compat b (a * b) hb
    exact ⟨he, hve, i, j, fun q r s ↦ ⟨hi q s, hj r s⟩⟩

end AlgebraicGeometry.FineFan
