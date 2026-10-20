/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.EventuallyAffine
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Eventually finite stages in an inverse system

Source: Stacks Project, Limits, Lemma 09ZN, `lemma-eventually-finite`
(blueprint: lem-weil-pbc-eventually-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem finite_of_integral_image_generators
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (g : A →ₐ[R] B) (hg : g.Finite)
    (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hi : ∀ x ∈ s, _root_.IsIntegral R (g x)) : Module.Finite R B := by
  have heq : Algebra.adjoin R (g '' (s : Set A)) = g.range := by
    rw [Algebra.adjoin_image, hs, Algebra.map_top]
  have hfin : Module.Finite R g.range := by
    rw [← heq]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hi x hx)
  have hsub : g.range.val.toRingHom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := g.rangeRestrict.toRingHom)
    exact hg
  have : Module.Finite g.range B := hsub
  exact Module.Finite.trans g.range B

private theorem exists_finite_stage_of_affine
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (S : Scheme.{u}) [IsAffine S] (D : J ⥤ Scheme.{u})
    [∀ j, IsAffine (D.obj j)]
    [∀ {i j : J} (g : i ⟶ j), IsFinite (D.map g)]
    (h : D ⟶ (Functor.const J).obj S)
    [∀ j, LocallyOfFiniteType (h.app j)]
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ j, c.π.app j ≫ h.app j = f) [IsIntegralHom f] (a : J) :
    ∃ (k : J) (_ : k ⟶ a), IsFinite (h.app k) := by
  classical
  have (j : J) : IsAffine (((Functor.const J).obj S).obj j) := ‹IsAffine S›
  let R := Γ(S, ⊤)
  let q (j : J) : R →+* Γ(D.obj j, ⊤) := (h.app j).appTop.hom
  let (j : J) : Algebra R Γ(D.obj j, ⊤) := (q j).toAlgebra
  have hq {i j : J} (g : i ⟶ j) :
      (D.map g).appTop.hom.comp (q j) = q i := by
    have H : D.map g ≫ h.app j = h.app i := by
      exact h.naturality g
    exact congrArg (fun t ↦ t.appTop.hom) H
  have hp (j : J) : (c.π.app j).appTop.hom.comp (q j) = f.appTop.hom := by
    simpa [q, Scheme.Hom.comp_appTop] using
      congrArg (fun t ↦ t.appTop.hom) (hf j)
  have hft : (q a).FiniteType := by
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
      inferInstance
  have : Algebra.FiniteType R Γ(D.obj a, ⊤) := hft
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := Γ(D.obj a, ⊤))
  have H (x : s) : ∃ (k : J) (g : k ⟶ a),
      (q k).IsIntegralElem ((D.map g).appTop x.val) := by
    obtain ⟨P, hP, hx⟩ := f.isIntegral_app ⊤ (isAffineOpen_top S)
      ((c.π.app a).appTop x.val)
    have heval : (c.π.app a).appTop (P.eval₂ (q a) x.val) = 0 := by
      rw [Polynomial.hom_eval₂, hp a]
      exact hx
    obtain ⟨k, g, hg⟩ := exists_appTop_map_eq_zero_of_isAffine_of_isLimit
      D c hc a (P.eval₂ (q a) x.val) heval
    refine ⟨k, g, P, hP, ?_⟩
    rw [Polynomial.hom_eval₂, hq g] at hg
    exact hg
  choose k g hg using H
  obtain ⟨b, gba, gb, hgb⟩ := IsCofiltered.wideCospan g
  let v : Γ(D.obj a, ⊤) →ₐ[R] Γ(D.obj b, ⊤) :=
    { __ := (D.map gba).appTop.hom
      commutes' := fun r ↦ congrFun (congrArg DFunLike.coe (hq gba)) r }
  have hv : v.Finite := (D.map gba).finite_appTop
  have hi (x) (hx : x ∈ s) : _root_.IsIntegral R (v x) := by
    have H := (hg ⟨x, hx⟩).map (D.map (gb ⟨x, hx⟩)).appTop.hom
    rw [hq] at H
    have heq : v x = (D.map (gb ⟨x, hx⟩)).appTop
        ((D.map (g ⟨x, hx⟩)).appTop x) := by
      change (D.map gba).appTop x = _
      rw [← hgb ⟨x, hx⟩, D.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [heq]
    exact H
  have hfinite : Module.Finite R Γ(D.obj b, ⊤) :=
    finite_of_integral_image_generators v hv s hs hi
  refine ⟨b, gba, ?_⟩
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  exact ⟨inferInstance, hfinite⟩

private theorem property_resLE_iff_of_eq
    (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (heq : V = f ⁻¹ᵁ U) :
    P (f.resLE U V e) ↔ P (f ∣_ U) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]

/-- The algebraic part of Stacks Tag 09ZN, assuming the structure maps are already
affine on a tail.  The proof descends finitely many monic equations through the
filtered colimit of sections and then uses finite module transitivity.

Source: Stacks Project, Limits, Lemma 09ZN, affine reduction in its proof.
(blueprint: lem-weil-pbc-eventually-finite-affine-tail) -/
private theorem eventually_finite_of_eventually_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsFinite (D.map g)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj S)
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsIntegralHom f]
    (ha : ∃ a : I, ∀ i : I, a ≤ i → IsAffineHom (h.app (op i))) :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsFinite (h.app (op i)) := by
  classical
  obtain ⟨a, ha⟩ := ha
  let b := op a
  have : IsAffineHom (h.app b) := ha a le_rfl
  let 𝒰 := S.affineCover.finiteSubcover
  have (v : 𝒰.I₀) : IsAffine (𝒰.X v) := inferInstanceAs (IsAffine (Spec _))
  let V (v : 𝒰.I₀) : S.affineOpens := ⟨(𝒰.f v).opensRange,
    isAffineOpen_opensRange (𝒰.f v)⟩
  have H (v : 𝒰.I₀) : ∃ k : Over b, IsFinite (h.app k.left ∣_ (V v).1) := by
    let U := h.app b ⁻¹ᵁ (V v).1
    have hU : IsAffineOpen U := (V v).2.preimage (h.app b)
    let E := opensDiagram D b U
    let d := opensCone D c b U
    have (k : Over b) : IsAffine (E.obj k) := hU.preimage (D.map k.hom)
    have {j k : Over b} (g : j ⟶ k) : IsFinite (E.map g) := by
      change IsFinite ((D.map g.left).resLE _ _ _)
      apply (property_resLE_iff_of_eq @IsFinite _ _ _ _ ?_).mpr
      · infer_instance
      · simp only [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]
    let t : E ⟶ (Functor.const (Over b)).obj (V v).1.toScheme :=
      { app k := (h.app k.left).resLE (V v).1 (D.map k.hom ⁻¹ᵁ U) (by
          simp [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom])
        naturality {j k} g := by
          apply (cancel_mono (V v).1.ι).mp
          dsimp [E, opensDiagram]
          simp [Scheme.Hom.resLE_comp_ι, Category.assoc, h.naturality] }
    have (k : Over b) : LocallyOfFiniteType (t.app k) := by
      dsimp [t]
      infer_instance
    let fV := f.resLE (V v).1 (c.π.app b ⁻¹ᵁ U) (by
      simp [U, ← Scheme.Hom.comp_preimage, _hf b])
    have hfVeq : c.π.app b ⁻¹ᵁ U = f ⁻¹ᵁ (V v).1 := by
      simp [U, ← Scheme.Hom.comp_preimage, _hf b]
    have : IsIntegralHom fV := by
      apply (property_resLE_iff_of_eq @IsIntegralHom _ _ _ _ hfVeq).mpr
      infer_instance
    have hcompat (k : Over b) : d.π.app k ≫ t.app k = fV := by
      apply (cancel_mono (V v).1.ι).mp
      dsimp [d, opensCone, t, fV]
      simp [Scheme.Hom.resLE_comp_ι, Category.assoc, _hf]
    let : IsAffine (V v).1.toScheme := (V v).2
    obtain ⟨k, _, hk⟩ := exists_finite_stage_of_affine (V v).1.toScheme E t d
      (isLimitOpensCone D c _hc b U) fV hcompat (Over.mk (𝟙 b))
    refine ⟨k, ?_⟩
    change IsFinite ((h.app k.left).resLE _ _ _) at hk
    exact (property_resLE_iff_of_eq @IsFinite _ _ _ _ (by
      simp [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom])).mp hk
  choose k hk using H
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image (fun v ↦ (k v).left))
  have gi (v : 𝒰.I₀) : i ⟶ (k v).left := (hi (by simp)).some
  refine ⟨i.unop, fun j hij ↦ ?_⟩
  let g : op j ⟶ i := (homOfLE hij).op
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun v ↦ (V v).1) 𝒰.iSup_opensRange
  intro v
  have : IsFinite (h.app (k v).left ∣_ (V v).1) := hk v
  have : IsFinite ((D.map (g ≫ gi v) ≫ h.app (k v).left) ∣_ (V v).1) := by
    rw [morphismRestrict_comp]
    infer_instance
  have heq : D.map (g ≫ gi v) ≫ h.app (k v).left = h.app (op j) := by
    exact h.naturality (g ≫ gi v)
  rw [← heq]
  exact this


/-- An inverse system of qcqs schemes over a qcqs base, with finite transitions and
locally finite type structure maps, has eventually finite structure maps if its limit
structure map is integral.

Source: Stacks Project, Limits, Lemma 09ZN, `lemma-eventually-finite`.
(blueprint: lem-weil-pbc-eventually-finite)

Proof plan:
1. Integral morphisms and finite transitions are affine
   (def-weil-finite-integral-morphism). Apply `eventually_affine`
   (lem-weil-pbc-eventually-affine). Restrict to the resulting cofinal upper tail,
   which has the same limit by directedness.
2. Choose a finite affine open cover of the base (def-pc-scheme). On that tail all
   inverse images are affine (pqf-def-affine-morphism). The open-restriction and
   affine comparison clauses of `exists_limit_affine_transition`
   (lem-weil-pbc-limit-affine-transition) identify their limit with the spectrum of
   the filtered colimit of their rings. The stage algebras are finite type
   (lem-weil-pbc-lft-affine-pairs); transitions are finite and the colimit is integral
   over the base ring (def-weil-finite-integral-morphism).
3. Choose finitely many algebra generators at one stage. Their images in the
   colimit satisfy monic equations by integrality.
4. Descend these finitely many equations to one later stage using equality in a
   filtered ring colimit (lem-pc-filtered-colimit-commrings-elementwise), then take
   a common upper bound of the finitely many indices by directedness.
5. The image of the initial algebra at this stage is finite over the base ring,
   since its finitely many algebra generators are integral
   (lem-weil-pbc-finite-of-integral-generators).
6. The later algebra is finite over that image: its module generators over the
   initial algebra still generate over the image. Products of module generators
   show it is finite over the base ring.
7. Take a common upper bound of the stages chosen for each affine open. Finite
   transitions remain finite on these opens (lem-weil-pbc-finite-local-on-target),
   and composition is finite (lem-weil-pbc-finite-composition). Finiteness is local
   on the target (lem-weil-pbc-finite-local-on-target), giving every later stage.
   For an empty base use the empty cover and choose any index. -/
theorem eventually_finite
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsFinite (D.map g)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj S)
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsIntegralHom f] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsFinite (h.app (op i)) := by
  obtain ⟨a, ha⟩ := eventually_affine S D h c _hc f _hf
  exact eventually_finite_of_eventually_affine S D h c _hc f _hf ⟨a, ha⟩

end AlgebraicGeometry
