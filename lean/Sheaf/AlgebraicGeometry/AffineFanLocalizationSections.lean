/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.CategoryTheory.LargeSetSheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.AlgebraicGeometry.MonoidPrincipalOpenFace
import Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood

/-!
# Sections and stalks of a sharp affine monoid spectrum

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.4, printed pp. 98--99
(blueprint: lem-trf-affine-fan-localization-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.FineFan

open CategoryTheory.Limits

private theorem unit_bijective_minimal
    {X : Type u} [TopologicalSpace X]
    (M : (Opens X)ᵒᵖ ⥤ CommMonCat.{u}) (U : Opens X) (x : X) (hx : x ∈ U)
    (hmin : ∀ V : Opens X, x ∈ V → U ≤ V) :
    Function.Bijective ((toSheafify (Opens.grothendieckTopology X) M).app (op U)) := by
  let J := Opens.grothendieckTopology X
  let η := toSheafify J M
  let := largeSetSheafification_locallyBijective.{u, u, 0} J
  have hw := J.W_of_preservesSheafification (forget CommMonCat) η (J.W_toSheafify M)
  have := (Presheaf.isLocallyInjective_forget_iff J η).mp hw.isLocallyInjective
  have := (Presheaf.isLocallySurjective_iff_whisker_forget J η).mpr hw.isLocallySurjective
  constructor
  · intro a b hab
    obtain ⟨V, f, hf, hxV⟩ :=
      (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) η a b hab) x hx
    have hVU : V = U := le_antisymm f.le (hmin V hxV)
    subst V
    have hf' : f = 𝟙 U := Subsingleton.elim _ _
    simpa [hf'] using hf
  · intro s
    obtain ⟨V, f, hf, hxV⟩ :=
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) η s) x hx
    have hVU : V = U := le_antisymm f.le (hmin V hxV)
    subst V
    obtain ⟨t, ht⟩ := hf
    refine ⟨t, ?_⟩
    have hf' : f = 𝟙 U := Subsingleton.elim _ _
    simpa [hf'] using ht

private theorem localization_mono {P : Type u} [CommMonoid P]
    {F G : Submonoid P} (h : F ≤ G) :
    Algebra.faceLocalization P F ≤ Algebra.faceLocalization P G := by
  rintro z ⟨p, f, rfl⟩
  exact ⟨p, ⟨f.val, h f.property⟩, rfl⟩

private theorem powers_complement {P : Type u} [CommMonoid P]
    (a : P) (x : MonoidPrime P) (hx : x ∈ basicOpen a) :
    Submonoid.powers a ≤ Submonoid.closure {p : P | p ∉ x.carrier} := by
  exact Submonoid.powers_le.mpr (Submonoid.subset_closure hx)

private theorem basic_localization_at_max
    (P : Type u) [CommMonoid P] (hP : IsFine P) (a : P)
    (m : MonoidPrime P) (hm : m.carrier = (principalFace a)ᶜ)
    (hma : m ∈ basicOpen a)
    (hmin : ∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U) :
    Algebra.faceLocalization P (Submonoid.closure {p : P | p ∉ m.carrier}) =
      Algebra.faceLocalization P (Submonoid.powers a) := by
  apply le_antisymm
  · rintro z ⟨p, f, rfl⟩
    have hf : f.val ∈ principalFace a := by
      have hc : Submonoid.closure {p : P | p ∉ m.carrier} ≤
          { carrier := principalFace a
            one_mem' := (monoid_principalOpen_face P hP).1 a |>.1
            mul_mem' := fun hx hy ↦ (monoid_principalOpen_face P hP).1 a |>.2.2.1 _ _ hx hy } := by
        apply Submonoid.closure_le.mpr
        intro p hp
        simpa [hm] using hp
      exact hc f.property
    have hDa : basicOpen a ≤ basicOpen f.val := hmin _ (by
      change f.val ∉ m.carrier
      intro hfm
      exact ((congrArg (fun S : Set P ↦ f.val ∈ S) hm).mp hfm) hf)
    obtain ⟨h, _, _⟩ := (monoid_principalOpen_face P hP).2.2.2 f.val a |>.2.2 hDa
    apply h
    exact ⟨p, ⟨f.val, Submonoid.mem_powers _⟩, rfl⟩
  · exact localization_mono (powers_complement a m hma)

private noncomputable def raw_basic_equiv
    (P : Type u) [CommMonoid P] (hP : IsFine P) (a : P)
    (m : MonoidPrime P) (hm : m.carrier = (principalFace a)ᶜ)
    (hma : m ∈ basicOpen a)
    (hmin : ∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U) :
    spectrumSections (basicOpen a) ≃* Algebra.faceLocalization P (Submonoid.powers a) where
  toFun s := ⟨s.val ⟨m, hma⟩, by
    rw [← basic_localization_at_max P hP a m hm hma hmin]
    exact s.property.1 ⟨m, hma⟩⟩
  invFun q := ⟨fun _ ↦ q.val,
    ⟨fun x ↦ localization_mono (powers_complement a x.val x.property) q.property,
      fun _ _ ↦ rfl⟩⟩
  left_inv s := by
    apply Subtype.ext
    funext x
    exact s.property.2 _ _
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def sharp_equiv {M N : Type u} [CommMonoid M] [CommMonoid N]
    (e : M ≃* N) : Associates M ≃* Associates N where
  toFun := sharpenMap e.toMonoidHom
  invFun := sharpenMap e.symm.toMonoidHom
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro m
    change Associates.mk (e.symm (e m)) = Associates.mk m
    rw [e.symm_apply_apply]
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro n
    change Associates.mk (e (e.symm n)) = Associates.mk n
    rw [e.apply_symm_apply]
  map_mul' := (sharpenMap e.toMonoidHom).map_mul

private noncomputable def sharp_unit (P : Type u) [CommMonoid P] :
    sharpPresheaf (X := TopCat.of (MonoidPrime P)) (spectrumPresheaf P) ⟶ (affine P).presheaf where
  app U := CommMonCat.ofHom
    (((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
      (sharpPresheaf (spectrumSheaf P).obj)).app U).hom.comp
      (sharpenMap (((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (spectrumPresheaf P)).app U).hom)))
  naturality U V f := by
    ext z
    refine Quotient.inductionOn z ?_
    intro q
    have h₁ := NatTrans.naturality_apply
      (toSheafify (Opens.grothendieckTopology (MonoidPrime P)) (spectrumPresheaf P)) f q
    have h₂ := NatTrans.naturality_apply
      (toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (sharpPresheaf (spectrumSheaf P).obj)) f
      (Associates.mk (((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (spectrumPresheaf P)).app U) q))
    change ((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (sharpPresheaf (spectrumSheaf P).obj)).app V)
      (Associates.mk (((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (spectrumPresheaf P)).app V) ((spectrumPresheaf P).map f q))) = _
    exact (congrArg ((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
        (sharpPresheaf (spectrumSheaf P).obj)).app V)
        (congrArg Associates.mk h₁)).trans h₂

private theorem sharp_unit_bijective
    (P : Type u) [CommMonoid P] (U : Opens (MonoidPrime P))
    (m : MonoidPrime P) (hm : m ∈ U)
    (hmin : ∀ V : Opens (MonoidPrime P), m ∈ V → U ≤ V) :
    Function.Bijective ((sharp_unit P).app (op U)) := by
  let e := MulEquiv.ofBijective
    (((toSheafify (Opens.grothendieckTopology (MonoidPrime P))
      (spectrumPresheaf P)).app (op U)).hom)
    (unit_bijective_minimal _ U m hm hmin)
  exact (unit_bijective_minimal (sharpPresheaf (spectrumSheaf P).obj) U m hm hmin).comp
    (sharp_equiv e).bijective

private noncomputable def basic_forward
    (P : Type u) [CommMonoid P] (hP : IsFine P) (a : P)
    (m : MonoidPrime P) (hm : m.carrier = (principalFace a)ᶜ)
    (hma : m ∈ basicOpen a)
    (hmin : ∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U) :
    Associates (Algebra.faceLocalization P (Submonoid.powers a)) ≃*
      (affine P).presheaf.obj (op (basicOpen a)) :=
  (sharp_equiv (raw_basic_equiv P hP a m hm hma hmin).symm).trans
    (MulEquiv.ofBijective ((sharp_unit P).app (op (basicOpen a))).hom
      (sharp_unit_bijective P _ m hma hmin))

private def constant_fraction {P : Type u} [CommMonoid P] (a : P)
    (q : Algebra.faceLocalization P (Submonoid.powers a)) : spectrumSections (basicOpen a) :=
  ⟨fun _ ↦ q.val,
    ⟨fun x ↦ localization_mono (powers_complement a x.val x.property) q.property,
      fun _ _ ↦ rfl⟩⟩

private theorem basic_models (P : Type u) [CommMonoid P] (hP : IsFine P) :
    ∀ a : P, ∃ E : Associates (Algebra.faceLocalization P (Submonoid.powers a)) ≃*
        (affine P).presheaf.obj (op (basicOpen a)),
      ∀ q, E (Associates.mk q) =
        (sharp_unit P).app (op (basicOpen a)) (Associates.mk (constant_fraction a q)) := by
  intro a
  obtain ⟨m, hm, hma, _, hmin⟩ := (monoid_principalOpen_face P hP).1 a |>.2.2.2.2.1
  exact ⟨basic_forward P hP a m hm hma hmin, fun _ ↦ rfl⟩

private theorem germ_restrict
    {X : TopCat.{u}} (M : TopCat.Presheaf CommMonCat.{u} X)
    {U V : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : M.obj (op U)) :
    germ M V x hx (M.map (homOfLE h).op s) = germ M U x (h hx) s := by
  exact congrArg (fun f : M.obj (op U) ⟶ stalk M x ↦ f s)
    (colimit.w (stalkDiagram M x)
      (homOfLE (show (⟨V, hx⟩ : OpenNhds x) ≤ ⟨U, h hx⟩ from h)).op)

private noncomputable def minimal_stalk_equiv
    {X : TopCat.{u}} (M : TopCat.Presheaf CommMonCat.{u} X)
    (x : X) (U : Opens X) (hx : x ∈ U)
    (hmin : ∀ V : Opens X, x ∈ V → U ≤ V) : stalk M x ≃* M.obj (op U) := by
  have hT : IsTerminal (op (⟨U, hx⟩ : OpenNhds x)) :=
    IsTerminal.ofUniqueHom
      (fun V ↦ (homOfLE (show (⟨U, hx⟩ : OpenNhds x) ≤ V.unop from
        hmin V.unop.val V.unop.property)).op)
      (fun _ _ ↦ Subsingleton.elim _ _)
  have : IsIso (germ M U x hx) :=
    IsColimit.isIso_ι_app_of_isTerminal (colimit.isColimit (stalkDiagram M x)) _ hT
  exact (CategoryTheory.Iso.commMonCatIsoToMulEquiv (asIso (germ M U x hx))).symm

private theorem minimal_stalk_equiv_germ
    {X : TopCat.{u}} (M : TopCat.Presheaf CommMonCat.{u} X)
    (x : X) (U : Opens X) (hx : x ∈ U)
    (hmin : ∀ V : Opens X, x ∈ V → U ≤ V)
    (V : Opens X) (hxV : x ∈ V) (s : M.obj (op V)) :
    minimal_stalk_equiv M x U hx hmin (germ M V x hxV s) =
      M.map (homOfLE (hmin V hxV)).op s := by
  have hw := colimit.w (stalkDiagram M x)
    (homOfLE (show (⟨U, hx⟩ : OpenNhds x) ≤ ⟨V, hxV⟩ from hmin V hxV)).op
  have hw' : germ M V x hxV s =
      germ M U x hx (M.map (homOfLE (hmin V hxV)).op s) := by
    exact (congrArg (fun f ↦ f s) hw).symm
  rw [hw']
  exact (minimal_stalk_equiv M x U hx hmin).apply_symm_apply _

private def submonoid_equiv {G : Type u} [Monoid G] {S T : Submonoid G}
    (h : S = T) : S ≃* T where
  toFun := Submonoid.inclusion h.le
  invFun := Submonoid.inclusion h.ge
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem prime_neighborhood_data
    (P : Type u) [CommMonoid P] (hP : IsFine P) (x : MonoidPrime P) :
    ∃ b : P, x ∈ basicOpen b ∧
      (∀ U : Opens (MonoidPrime P), x ∈ U → basicOpen b ≤ U) ∧
      Algebra.faceLocalization P (Submonoid.powers b) =
        Algebra.faceLocalization P (Submonoid.closure {p : P | p ∉ x.carrier}) ∧
      (∀ p : P,
        (∃ v : Algebra.faceLocalization P (Submonoid.closure {a : P | a ∉ x.carrier}),
          Algebra.GrothendieckGroup.of p * v.val = 1) ↔ p ∉ x.carrier) := by
  classical
  obtain ⟨S, hS⟩ := hP.1.fg_top
  let e : Fin (Fintype.card S) → P := fun i ↦ ((Fintype.equivFin S).symm i).val
  have hrange : Set.range e = (S : Set P) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin S).symm i).property
    · intro hp
      refine ⟨Fintype.equivFin S ⟨p, hp⟩, ?_⟩
      simp [e]
  have he : Submonoid.closure (Set.range e) = ⊤ := by rw [hrange]; exact hS
  let b := (Finset.univ.filter (fun i ↦ e i ∉ x.carrier)).prod e
  have hd := monoidPrime_minimal_neighborhood P hP _ e he x b rfl
  rcases hd with ⟨_, _, _, _, _, _, hxb, hmin, hloc, _, hunit⟩
  exact ⟨b, hxb, hmin, hloc, fun p ↦ (hunit p).1.trans (hunit p).2⟩

/-- The sections on `D(a)` and the stalk at a prime are the corresponding localizations
modulo units. We use multiplicative notation: the additive zero is `1`, and sharpening
is `Associates`. The first equation fixes the canonical numerator sections. The next
clauses say that restrictions and germs send a fraction to the same ambient completion
element in the new localization, then pass to its class modulo units. Thus the
isomorphisms are canonical, rather than arbitrary isomorphisms of abstract monoids.
Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.4, printed pp. 98--99
(blueprint: lem-trf-affine-fan-localization-sections).

Proof:
1. For `a`, take the face of elements dividing some power of `a`. Its complement is
   a prime in `D(a)` containing every prime of `D(a)`.
2. Every neighborhood of this prime contains `D(a)`, so every open cover of `D(a)`
   contains `D(a)` itself. This includes `a = 1`.
3. Form the sectionwise quotient by units using `def-trf-fine-fan-blowup`.
   By `lem-trf-commutative-monoid-sheafification` its monoid sheafification has the
   underlying set sheafification, with the same unit.
4. The sheafification unit is locally bijective by
   `lem-weil-pbc-large-set-sheafification`: sheafification fixes sheaves by the
   universal property in `def-weil-pbc-sheafification`, so it inverts its own unit.
5. The trivial-cover property makes that unit bijective on `D(a)`. The unsharpened
   sections are the localization at `a`, giving the first isomorphisms.
6. The complement of a prime is a face generated by those members of a finite set
   of monoid generators that avoid the prime. Their product `b` has `D(b)` as the
   smallest neighborhood of the prime. Its localization is localization at the
   whole complement, so the first isomorphism computes the stalk.
7. Both sheafification units commute with restrictions. For `D(b)` inside `D(a)`,
   `a` divides a power of `b`, so localization sends each fraction to the identical
   completion element. The same holds for germs by the smallest-neighborhood calculation.
8. The canonical germ is zero precisely when its numerator is a unit in the prime
   localization. Elements outside the prime become units. Conversely an inverse
   gives an equality `p*q = f` with `f` outside the prime; integrality and the face
   property force `p` outside the prime.
-/
theorem affineFan_localization_sections
    (P : Type u) [CommMonoid P] (hP : IsFine P) :
    ∃ (sections : ∀ a : P, (affine P).presheaf.obj (op (basicOpen a)) ≃*
        Associates (Algebra.faceLocalization P (Submonoid.powers a)))
      (stalks : ∀ x : MonoidPrime P, stalk (affine P).presheaf x ≃*
        Associates (Algebra.faceLocalization P
          (Submonoid.closure {a : P | a ∉ x.carrier}))),
      (∀ a p : P,
        ∃ q : Algebra.faceLocalization P (Submonoid.powers a),
          q.val = Algebra.GrothendieckGroup.of p ∧
          sections a ((affine P).presheaf.map (homOfLE le_top).op (affineSection P p)) =
            Associates.mk q) ∧
      (∀ (a b : P) (h : basicOpen b ≤ basicOpen a)
          (q : Algebra.faceLocalization P (Submonoid.powers a)),
        ∃ r : Algebra.faceLocalization P (Submonoid.powers b),
          r.val = q.val ∧
          sections b ((affine P).presheaf.map (homOfLE h).op
            ((sections a).symm (Associates.mk q))) = Associates.mk r) ∧
      (∀ (a : P) (x : MonoidPrime P) (hx : x ∈ basicOpen a)
          (q : Algebra.faceLocalization P (Submonoid.powers a)),
        ∃ r : Algebra.faceLocalization P
            (Submonoid.closure {p : P | p ∉ x.carrier}),
          r.val = q.val ∧
          stalks x (germ (affine P).presheaf (basicOpen a) x hx
            ((sections a).symm (Associates.mk q))) = Associates.mk r) ∧
      (∀ (x : MonoidPrime P) (p : P), affineGerm x p = 1 ↔ p ∉ x.carrier) := by
  classical
  choose E hE using basic_models P hP
  let sections := fun a ↦ (E a).symm
  have hnum : ∀ a p : P,
      ∃ q : Algebra.faceLocalization P (Submonoid.powers a),
        q.val = Algebra.GrothendieckGroup.of p ∧
        sections a ((affine P).presheaf.map (homOfLE le_top).op (affineSection P p)) =
          Associates.mk q := by
    intro a p
    let q : Algebra.faceLocalization P (Submonoid.powers a) :=
      ⟨Algebra.GrothendieckGroup.of p, p, ⟨1, Submonoid.one_mem _⟩, by simp⟩
    refine ⟨q, rfl, ?_⟩
    apply (E a).injective
    rw [MulEquiv.apply_symm_apply, hE]
    change (affine P).presheaf.map (homOfLE le_top).op
        ((sharp_unit P).app (op ⊤) (Associates.mk (numerator P p))) = _
    rw [← NatTrans.naturality_apply]
    rfl
  have hres : ∀ (a b : P) (h : basicOpen b ≤ basicOpen a)
      (q : Algebra.faceLocalization P (Submonoid.powers a)),
      ∃ r : Algebra.faceLocalization P (Submonoid.powers b), r.val = q.val ∧
        sections b ((affine P).presheaf.map (homOfLE h).op
          ((sections a).symm (Associates.mk q))) = Associates.mk r := by
    intro a b h q
    obtain ⟨hi, _, _⟩ := (monoid_principalOpen_face P hP).2.2.2 a b |>.2.2 h
    let r := Submonoid.inclusion hi q
    refine ⟨r, rfl, ?_⟩
    apply (E b).injective
    rw [MulEquiv.apply_symm_apply]
    change (affine P).presheaf.map (homOfLE h).op (E a (Associates.mk q)) = _
    rw [hE, hE, ← NatTrans.naturality_apply]
    rfl
  choose b hb hmin hloc hunit using prime_neighborhood_data P hP
  let K := fun x ↦ sharp_equiv (submonoid_equiv (hloc x))
  let stalks := fun x ↦
    (minimal_stalk_equiv (affine P).presheaf x (basicOpen (b x)) (hb x) (hmin x)).trans
      ((sections (b x)).trans (K x))
  have hgerm : ∀ (a : P) (x : MonoidPrime P) (hx : x ∈ basicOpen a)
      (q : Algebra.faceLocalization P (Submonoid.powers a)),
      ∃ r : Algebra.faceLocalization P (Submonoid.closure {p : P | p ∉ x.carrier}),
        r.val = q.val ∧
        stalks x (germ (affine P).presheaf (basicOpen a) x hx
          ((sections a).symm (Associates.mk q))) = Associates.mk r := by
    intro a x hx q
    obtain ⟨r, hr, heq⟩ := hres a (b x) (hmin x _ hx) q
    refine ⟨submonoid_equiv (hloc x) r, hr, ?_⟩
    change K x (sections (b x)
      (minimal_stalk_equiv (affine P).presheaf x (basicOpen (b x)) (hb x) (hmin x)
        (germ (affine P).presheaf (basicOpen a) x hx
          ((sections a).symm (Associates.mk q))))) = _
    rw [minimal_stalk_equiv_germ, heq]
    rfl
  refine ⟨sections, stalks, hnum, hres, hgerm, ?_⟩
  intro x p
  obtain ⟨q, hq, hqE⟩ := hnum (1 : P) p
  have hx1 : x ∈ basicOpen (1 : P) := by
    rw [(monoid_principalOpen_face P hP).2.2.1]
    trivial
  obtain ⟨r, hr, hrE⟩ := hgerm 1 x hx1 q
  have hg : stalks x (affineGerm x p) = Associates.mk r := by
    rw [← hrE]
    apply congrArg (stalks x)
    change germ (affine P).presheaf ⊤ x _ (affineSection P p) = _
    rw [← hqE, MulEquiv.symm_apply_apply]
    exact (germ_restrict (affine P).presheaf (U := ⊤) (V := basicOpen 1)
      le_top x hx1 (affineSection P p)).symm
  rw [← (stalks x).map_eq_one_iff, hg, Associates.mk_eq_one]
  rw [isUnit_iff_exists_inv]
  constructor
  · rintro ⟨v, hv⟩
    apply (hunit x p).mp
    refine ⟨v, ?_⟩
    have hv' := congrArg Subtype.val hv
    change r.val * v.val = 1 at hv'
    simpa [hr, hq] using hv'
  · intro hp
    obtain ⟨v, hv⟩ := (hunit x p).mpr hp
    refine ⟨v, Subtype.ext ?_⟩
    change r.val * v.val = 1
    simpa [hr, hq] using hv

end AlgebraicGeometry.FineFan
