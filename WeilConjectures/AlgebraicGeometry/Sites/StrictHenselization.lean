/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# The strict henselization of a scheme at a geometric point

Let `V` be a scheme and let `v : Spec Ω ⟶ V` be a geometric point of `V`, i.e. `Ω` is a
separably closed field. The *strict henselization* of `V` at `v` is the filtered colimit of the
rings of sections `Γ(V', 𝒪)` over the cofiltered category of étale neighbourhoods `V' ⟶ V`
of `v`. We define it as the fiber of the structure presheaf of the small étale site at the point
`AlgebraicGeometry.Scheme.pointSmallEtale v`, i.e. as the geometric stalk of the structure
sheaf, and we show that it is a strictly Henselian local ring.

## Main definitions

- `AlgebraicGeometry.Scheme.strictHenselization`: the strict henselization `𝒪^{sh}_{V, v}`.
- `AlgebraicGeometry.Scheme.strictHenselizationEval`: the evaluation `𝒪^{sh}_{V, v} ⟶ Ω` of a
  germ at the geometric point; its kernel is the maximal ideal, see
  `AlgebraicGeometry.Scheme.maximalIdeal_strictHenselization`.
- `AlgebraicGeometry.Scheme.AffineEtaleNbhd`: an affine étale neighbourhood of `v`. These are
  cofinal among all étale neighbourhoods, see
  `AlgebraicGeometry.Scheme.exists_affineEtaleNbhd_range_toStrictHenselization_subset`.

## Main results

- `AlgebraicGeometry.Scheme.isStrictlyHenselianLocalRing_strictHenselization`: the strict
  henselization is a strictly Henselian local ring.

The substance is `AlgebraicGeometry.Scheme.exists_isRoot_and_strictHenselizationEval_eq`: a
monic polynomial over the colimit whose reduction at the geometric point has a simple root `β`
already has a root with value `β`. Indeed, the polynomial descends to some affine étale
neighbourhood `Spec R`, and the standard étale algebra `(R[X]/f)[1/f']` is a further étale
neighbourhood of `v` carrying an honest root. Henselianity is this statement applied to an
approximate root, and separable closedness of the residue field is the same argument applied to
a separable polynomial.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry.Scheme

variable {V : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The structure presheaf of the small étale site of a scheme `V`. -/
def etaleStructurePresheaf (V : Scheme.{u}) : V.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Etale.forget V ⋙ CategoryTheory.Over.forget V).op ⋙ Scheme.Γ

@[simp]
lemma etaleStructurePresheaf_obj (X : V.Etale) :
    (etaleStructurePresheaf V).obj (op X) = Γ(X.left, ⊤) := rfl

variable (v : Spec (.of Ω) ⟶ V)

/-- The strict henselization of `V` at the geometric point `v`. -/
def strictHenselization : CommRingCat.{u} :=
  (pointSmallEtale v).presheafFiber.obj (etaleStructurePresheaf V)

/-- The germ map `Γ(X, 𝒪) ⟶ 𝒪^{sh}_{V, v}` of an étale neighbourhood `X` of the geometric
point `v`, with `x` the chosen lift of `v` to `X`. -/
def toStrictHenselization (X : V.Etale) (x : (pointSmallEtale v).fiber.obj X) :
    Γ(X.left, ⊤) ⟶ strictHenselization v :=
  (pointSmallEtale v).toPresheafFiber X x (etaleStructurePresheaf V)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The evaluation of germs at the geometric point: the ring homomorphism
`𝒪^{sh}_{V, v} ⟶ Ω` induced by evaluating a section at `v`. -/
def strictHenselizationEval : strictHenselization v ⟶ CommRingCat.of Ω :=
  (pointSmallEtale v).presheafFiberDesc
    (fun X x ↦ Scheme.Γ.map (x.left).op ≫ (Scheme.ΓSpecIso (.of Ω)).hom)
    (fun X Y f x ↦ by
      change Scheme.Γ.map ((Etale.forget V).map f).left.op ≫ Scheme.Γ.map x.left.op ≫ _ =
        Scheme.Γ.map (x.left ≫ ((Etale.forget V).map f).left).op ≫ _
      rw [op_comp, Scheme.Γ.map_comp, Category.assoc])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma toStrictHenselization_comp_strictHenselizationEval (X : V.Etale)
    (x : (pointSmallEtale v).fiber.obj X) :
    toStrictHenselization v X x ≫ strictHenselizationEval v =
      Scheme.Γ.map (x.left).op ≫ (Scheme.ΓSpecIso (.of Ω)).hom :=
  (pointSmallEtale v).toPresheafFiber_presheafFiberDesc _ _ X x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma map_comp_toStrictHenselization {X Y : V.Etale} (f : X ⟶ Y)
    (x : (pointSmallEtale v).fiber.obj X) :
    Scheme.Γ.map f.left.op ≫ toStrictHenselization v X x =
      toStrictHenselization v Y ((pointSmallEtale v).fiber.map f x) :=
  (pointSmallEtale v).toPresheafFiber_w (P := etaleStructurePresheaf V) f x

/-- An affine étale neighbourhood of a geometric point `v : Spec Ω ⟶ V` is an affine scheme
`Spec R` étale over `V`, together with a lift of `v` to `Spec R`. Such neighbourhoods are
cofinal among all étale neighbourhoods of `v`, hence compute the strict henselization. -/
structure AffineEtaleNbhd where
  /-- the ring of the neighbourhood -/
  R : CommRingCat.{u}
  /-- the structure morphism of the neighbourhood -/
  hom : Spec R ⟶ V
  etale : Etale hom
  /-- the lift of the geometric point, as a ring homomorphism -/
  pt : R ⟶ CommRingCat.of Ω
  w : Spec.map pt ≫ hom = v

namespace AffineEtaleNbhd

attribute [instance] AffineEtaleNbhd.etale

variable {v} (N : AffineEtaleNbhd v)

/-- The object of the small étale site of `V` underlying an affine étale neighbourhood. -/
def obj : V.Etale := Etale.mk N.hom

omit [IsSepClosed Ω] in
@[simp] lemma obj_left : N.obj.left = Spec N.R := rfl

omit [IsSepClosed Ω] in
@[simp] lemma obj_hom : N.obj.hom = N.hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The lift of the geometric point, as an element of the fiber at `N.obj`. -/
def fiberPt : (pointSmallEtale v).fiber.obj N.obj :=
  CategoryTheory.Over.homMk (Spec.map N.pt) N.w

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma fiberPt_left : N.fiberPt.left = Spec.map N.pt := rfl

/-- The canonical map from the ring of an affine étale neighbourhood of `v` to the strict
henselization of `V` at `v`. -/
def ι : N.R ⟶ strictHenselization v :=
  (Scheme.ΓSpecIso N.R).inv ≫ toStrictHenselization v N.obj N.fiberPt

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_comp_strictHenselizationEval : N.ι ≫ strictHenselizationEval v = N.pt := by
  rw [ι, Category.assoc, toStrictHenselization_comp_strictHenselizationEval, fiberPt_left,
    Scheme.Γ_map_op, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma comp_ι {N N' : AffineEtaleNbhd v} (u : N.R ⟶ N'.R)
    (hu : Spec.map u ≫ N.hom = N'.hom) (hu' : u ≫ N'.pt = N.pt) :
    u ≫ N'.ι = N.ι := by
  let g : N'.obj ⟶ N.obj := MorphismProperty.Over.homMk (Spec.map u) hu
  have hg : (pointSmallEtale v).fiber.map g N'.fiberPt = N.fiberPt := by
    apply CategoryTheory.Over.OverMorphism.ext
    change Spec.map N'.pt ≫ Spec.map u = Spec.map N.pt
    rw [← Spec.map_comp, hu']
  have h2 : Scheme.Γ.map (Spec.map u).op ≫ toStrictHenselization v N'.obj N'.fiberPt =
      toStrictHenselization v N.obj N.fiberPt :=
    (map_comp_toStrictHenselization v g N'.fiberPt).trans (by rw [hg])
  rw [ι, ι, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Γ_map_op, h2]

end AffineEtaleNbhd

section Descent

variable {v}

set_option backward.isDefEq.respectTransparency false in
lemma range_toStrictHenselization_subset {e e' : (pointSmallEtale v).fiber.Elements}
    (f : e ⟶ e') : Set.range (toStrictHenselization v e'.1 e'.2) ⊆
      Set.range (toStrictHenselization v e.1 e.2) := by
  rintro _ ⟨b, rfl⟩
  refine ⟨Scheme.Γ.map f.1.left.op b, ?_⟩
  have h := map_comp_toStrictHenselization v f.1 e.2
  rw [f.2] at h
  exact congr($h b)

set_option backward.isDefEq.respectTransparency false in
/-- Any finite family of elements of the strict henselization comes from a single étale
neighbourhood. -/
lemma exists_forall_mem_range_toStrictHenselization (n : ℕ)
    (a : Fin n → ToType (strictHenselization v)) :
    ∃ e : (pointSmallEtale v).fiber.Elements,
      ∀ i, a i ∈ Set.range (toStrictHenselization v e.1 e.2) := by
  induction n with
  | zero =>
    obtain ⟨e⟩ := IsCofiltered.nonempty (C := (pointSmallEtale v).fiber.Elements)
    exact ⟨e, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih (fun i ↦ a i.succ)
    obtain ⟨X, x, z, hz⟩ :=
      (pointSmallEtale v).toPresheafFiber_jointly_surjective (P := etaleStructurePresheaf V) (a 0)
    refine ⟨IsCofiltered.min e (Functor.elementsMk _ X x), Fin.cases ?_ ?_⟩
    · exact range_toStrictHenselization_subset (IsCofiltered.minToRight _ _) ⟨z, hz⟩
    · exact fun i ↦ range_toStrictHenselization_subset (IsCofiltered.minToLeft _ _) (he i)

set_option backward.isDefEq.respectTransparency false in
lemma AffineEtaleNbhd.toStrictHenselization_mem_range_ι (N : AffineEtaleNbhd v)
    (b : Γ(Spec N.R, ⊤)) :
    toStrictHenselization v N.obj N.fiberPt b ∈ Set.range N.ι := by
  refine ⟨(Scheme.ΓSpecIso N.R).hom b, ?_⟩
  have h : (Scheme.ΓSpecIso N.R).hom ≫ N.ι = toStrictHenselization v N.obj N.fiberPt := by
    rw [AffineEtaleNbhd.ι, Iso.hom_inv_id_assoc]
  exact congr($h b)

set_option backward.isDefEq.respectTransparency false in
/-- Affine étale neighbourhoods are cofinal: every étale neighbourhood of `v` is refined by
an affine one. -/
lemma exists_affineEtaleNbhd_range_toStrictHenselization_subset
    (e : (pointSmallEtale v).fiber.Elements) :
    ∃ N : AffineEtaleNbhd v, Set.range (toStrictHenselization v e.1 e.2) ⊆ Set.range N.ι := by
  let y : Spec (CommRingCat.of Ω) ⟶ e.1.left := e.2.left
  have hyw : y ≫ e.1.hom = v := CategoryTheory.Over.w e.2
  obtain ⟨R, j, hj, hmem, -⟩ := exists_affine_mem_range_and_range_subset
    (x := y default) (U := ⊤) trivial
  have hsub : Set.range y ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default]
  have hl : IsOpenImmersion.lift j y hsub ≫ j = y := IsOpenImmersion.lift_fac _ _ _
  have hspec : Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) =
    IsOpenImmersion.lift j y hsub := Spec.map_preimage _
  have hw : Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) ≫ (j ≫ e.1.hom) = v := by
    rw [hspec, ← Category.assoc, hl, hyw]
  let N : AffineEtaleNbhd v :=
    ⟨R, j ≫ e.1.hom, inferInstance, Spec.preimage (IsOpenImmersion.lift j y hsub), hw⟩
  have hg : (pointSmallEtale v).fiber.map
      (MorphismProperty.Over.homMk (A := N.obj) (B := e.1) j rfl) N.fiberPt = e.2 := by
    apply CategoryTheory.Over.OverMorphism.ext
    change Spec.map (Spec.preimage (IsOpenImmersion.lift j y hsub)) ≫ j = y
    rw [hspec, hl]
  refine ⟨N, subset_trans (range_toStrictHenselization_subset
    (e := Functor.elementsMk _ N.obj N.fiberPt) (e' := e)
    (CategoryOfElements.homMk _ _ (MorphismProperty.Over.homMk j rfl) hg)) ?_⟩
  rintro _ ⟨b, rfl⟩
  exact AffineEtaleNbhd.toStrictHenselization_mem_range_ι _ b

/-- Any finite family of elements of the strict henselization comes from a single affine
étale neighbourhood. -/
lemma exists_affineEtaleNbhd_forall_mem_range (n : ℕ)
    (a : Fin n → ToType (strictHenselization v)) :
    ∃ N : AffineEtaleNbhd v, ∀ i, a i ∈ Set.range N.ι := by
  obtain ⟨e, he⟩ := exists_forall_mem_range_toStrictHenselization n a
  obtain ⟨N, hN⟩ := exists_affineEtaleNbhd_range_toStrictHenselization_subset e
  exact ⟨N, fun i ↦ hN (he i)⟩

end Descent

section StandardEtale

variable {v}

set_option backward.isDefEq.respectTransparency false in
/-- Given an affine étale neighbourhood `N` of the geometric point `v`, a standard étale pair
`P` over `N.R` and a point `β : Ω` at which `P.f` vanishes and `P.g` is invertible, the
standard étale algebra of `P` is again an affine étale neighbourhood of `v`, and it carries a
root of `P.f`. -/
lemma AffineEtaleNbhd.exists_standardEtale (N : AffineEtaleNbhd v)
    (P : StandardEtalePair ↑N.R) (β : Ω)
    (h₁ : (P.f.map N.pt.hom).eval β = 0) (h₂ : (P.g.map N.pt.hom).eval β ≠ 0) :
    ∃ (N' : AffineEtaleNbhd v) (u : N.R ⟶ N'.R) (t : N'.R),
      u ≫ N'.ι = N.ι ∧ (P.f.map u.hom).eval t = 0 ∧
        IsUnit ((P.g.map u.hom).eval t) ∧ N'.pt t = β := by
  let _inst : Algebra ↑N.R Ω := N.pt.hom.toAlgebra
  have halg : algebraMap ↑N.R Ω = N.pt.hom := N.pt.hom.algebraMap_toAlgebra
  have hae : ∀ (p : (↑N.R)[X]) (x : Ω), aeval x p = (p.map N.pt.hom).eval x := fun p x ↦ by
    rw [Polynomial.eval_map, Polynomial.aeval_def, halg]
  have hβ : P.HasMap β :=
    ⟨by rw [hae]; exact h₁, by rw [hae]; exact isUnit_iff_ne_zero.mpr h₂⟩
  have hae' : ∀ (p : (↑N.R)[X]) (x : P.Ring),
      aeval x p = (p.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring)).hom).eval x :=
    fun p x ↦ by
    rw [Polynomial.eval_map, Polynomial.aeval_def, CommRingCat.hom_ofHom]
  have hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (by rw [CommRingCat.hom_ofHom]; exact RingHom.etale_algebraMap.mpr inferInstance)
  have hpt : CommRingCat.ofHom (algebraMap ↑N.R P.Ring) ≫
      CommRingCat.ofHom (P.lift β hβ).toRingHom = N.pt := by
    ext r
    change (P.lift β hβ) (algebraMap ↑N.R P.Ring r) = N.pt r
    rw [AlgHom.commutes, halg]
  refine ⟨⟨CommRingCat.of P.Ring,
      Spec.map (CommRingCat.ofHom (algebraMap ↑N.R P.Ring)) ≫ N.hom, inferInstance,
      CommRingCat.ofHom (P.lift β hβ).toRingHom, ?_⟩,
    CommRingCat.ofHom (algebraMap ↑N.R P.Ring), P.X, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hpt, N.w]
  · exact comp_ι _ rfl hpt
  · rw [← hae']; exact P.hasMap_X.1
  · rw [← hae']; exact P.hasMap_X.2
  · exact P.lift_X β hβ

end StandardEtale

section Local

variable {v}

@[simp]
lemma AffineEtaleNbhd.strictHenselizationEval_ι (N : AffineEtaleNbhd v) (c : N.R) :
    strictHenselizationEval v (N.ι c) = N.pt c := by
  rw [← CommRingCat.comp_apply, N.ι_comp_strictHenselizationEval]

lemma isUnit_of_strictHenselizationEval_ne_zero {a : ↑(strictHenselization v)}
    (ha : strictHenselizationEval v a ≠ 0) : IsUnit a := by
  obtain ⟨N, hN⟩ := exists_affineEtaleNbhd_forall_mem_range 1 (fun _ ↦ a)
  obtain ⟨c, rfl⟩ := hN 0
  rw [AffineEtaleNbhd.strictHenselizationEval_ι] at ha
  obtain ⟨N', u, t, hu, ht, htu, -⟩ := N.exists_standardEtale
    ⟨X - C c, monic_X_sub_C c, X, X, 0, 1, by simp⟩ (N.pt c) (by simp) (by simpa using ha)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X,
    eval_C, sub_eq_zero] at ht
  rw [Polynomial.map_X, eval_X, ht] at htu
  rw [← hu, CommRingCat.comp_apply]
  exact htu.map N'.ι.hom

lemma isUnit_iff_strictHenselizationEval_ne_zero (a : ↑(strictHenselization v)) :
    IsUnit a ↔ strictHenselizationEval v a ≠ 0 :=
  ⟨fun h ↦ (h.map (strictHenselizationEval v).hom).ne_zero,
    isUnit_of_strictHenselizationEval_ne_zero⟩

instance nontrivial_strictHenselization : Nontrivial ↑(strictHenselization v) :=
  ⟨1, 0, fun h ↦ one_ne_zero (α := Ω)
    (by rw [← map_one (strictHenselizationEval v).hom, h, map_zero])⟩

instance isLocalRing_strictHenselization : IsLocalRing ↑(strictHenselization v) :=
  .of_nonunits_add fun a b ha hb ↦ by
    simp only [mem_nonunits_iff, isUnit_iff_strictHenselizationEval_ne_zero, not_not] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]

lemma mem_maximalIdeal_strictHenselization_iff (a : ↑(strictHenselization v)) :
    a ∈ IsLocalRing.maximalIdeal ↑(strictHenselization v) ↔
      strictHenselizationEval v a = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_strictHenselizationEval_ne_zero, not_not]

/-- The maximal ideal of the strict henselization is the kernel of the evaluation at the
geometric point. -/
lemma maximalIdeal_strictHenselization :
    IsLocalRing.maximalIdeal ↑(strictHenselization v) =
      RingHom.ker (strictHenselizationEval v).hom :=
  Ideal.ext fun a ↦ (mem_maximalIdeal_strictHenselization_iff a).trans RingHom.mem_ker.symm

end Local

section Henselian

variable {v}

/-- The key lemma: a monic polynomial over the strict henselization whose reduction at the
geometric point has a simple root `β` already has a root in the strict henselization, with
value `β` at the geometric point. -/
lemma exists_isRoot_and_strictHenselizationEval_eq
    {f : (↑(strictHenselization v))[X]} (hf : f.Monic) {β : Ω}
    (h₁ : (f.map (strictHenselizationEval v).hom).eval β = 0)
    (h₂ : (derivative (f.map (strictHenselizationEval v).hom)).eval β ≠ 0) :
    ∃ a : ↑(strictHenselization v), f.IsRoot a ∧ strictHenselizationEval v a = β := by
  obtain ⟨N, hN⟩ :=
    exists_affineEtaleNbhd_forall_mem_range (f.natDegree + 1) (fun i ↦ f.coeff i)
  have hlifts : f ∈ Polynomial.lifts N.ι.hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ f.natDegree
    · exact hN ⟨n, by omega⟩
    · rw [f.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, map_zero _⟩
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  have hcomp : (strictHenselizationEval v).hom.comp N.ι.hom = N.pt.hom := by
    rw [← CommRingCat.hom_comp, N.ι_comp_strictHenselizationEval]
  have hmap : f.map (strictHenselizationEval v).hom = g.map N.pt.hom := by
    rw [← hg, Polynomial.map_map, hcomp]
  obtain ⟨N', u, t, hu, ht, -, hpt⟩ := N.exists_standardEtale
    ⟨g, hgm, derivative g, 1, 0, 1, by simp⟩ β (by rwa [← hmap]) (by
      rw [← Polynomial.derivative_map, ← hmap]; exact h₂)
  refine ⟨N'.ι t, ?_, by rw [AffineEtaleNbhd.strictHenselizationEval_ι, hpt]⟩
  have : f = (g.map u.hom).map N'.ι.hom := by
    rw [Polynomial.map_map, ← CommRingCat.hom_comp, hu, hg]
  rw [Polynomial.IsRoot.def, this, Polynomial.eval_map_apply, ht, map_zero]

instance henselianLocalRing_strictHenselization :
    HenselianLocalRing ↑(strictHenselization v) where
  is_henselian f hf a₀ h₁ h₂ := by
    rw [mem_maximalIdeal_strictHenselization_iff] at h₁
    have e₁ : (f.map (strictHenselizationEval v).hom).eval
        (strictHenselizationEval v a₀) = 0 := by
      rw [Polynomial.eval_map_apply, h₁]
    have e₂ : (derivative (f.map (strictHenselizationEval v).hom)).eval
        (strictHenselizationEval v a₀) ≠ 0 := by
      rw [Polynomial.derivative_map, Polynomial.eval_map_apply]
      exact (h₂.map (strictHenselizationEval v).hom).ne_zero
    obtain ⟨a, ha, hb⟩ := exists_isRoot_and_strictHenselizationEval_eq hf e₁ e₂
    exact ⟨a, ha, by rw [mem_maximalIdeal_strictHenselization_iff, map_sub, hb, sub_self]⟩

/-- The residue field of the strict henselization of `V` at a geometric point with values in
`Ω` embeds into `Ω`: it is the separable closure of the residue field of the image point
inside `Ω`. -/
def strictHenselizationResidueFieldEmb :
    IsLocalRing.ResidueField ↑(strictHenselization v) →+* Ω :=
  Ideal.Quotient.lift _ (strictHenselizationEval v).hom fun a ha ↦
    (mem_maximalIdeal_strictHenselization_iff a).1 ha

@[simp]
lemma strictHenselizationResidueFieldEmb_residue (a : ↑(strictHenselization v)) :
    strictHenselizationResidueFieldEmb (IsLocalRing.residue _ a) =
      strictHenselizationEval v a :=
  rfl

lemma strictHenselizationResidueFieldEmb_comp_residue :
    (strictHenselizationResidueFieldEmb (v := v)).comp
      (IsLocalRing.residue ↑(strictHenselization v)) = (strictHenselizationEval v).hom :=
  RingHom.ext fun a ↦ strictHenselizationResidueFieldEmb_residue a

instance isSepClosed_residueField_strictHenselization :
    IsSepClosed (IsLocalRing.ResidueField ↑(strictHenselization v)) := by
  refine IsSepClosed.of_exists_root _ fun p hpm hpi hps ↦ ?_
  obtain ⟨f, hf, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p) hpm
  have hmap : f.map (strictHenselizationEval v).hom = p.map strictHenselizationResidueFieldEmb := by
    rw [← hf, Polynomial.map_map, strictHenselizationResidueFieldEmb_comp_residue]
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_root (k := Ω)
    (p.map strictHenselizationResidueFieldEmb)
    (by rw [hpm.degree_map]; exact (degree_pos_of_irreducible hpi).ne') hps.map
  have e₁ : (f.map (strictHenselizationEval v).hom).eval β = 0 := by rw [hmap]; exact hβ
  have e₂ : (derivative (f.map (strictHenselizationEval v).hom)).eval β ≠ 0 := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
    exact hps.eval₂_derivative_ne_zero _
      (by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hβ)
  obtain ⟨a, ha, -⟩ := exists_isRoot_and_strictHenselizationEval_eq hfm e₁ e₂
  exact ⟨IsLocalRing.residue _ a,
    by rw [← hf, Polynomial.eval_map_apply, ha.eq_zero, map_zero]⟩

instance isStrictlyHenselianLocalRing_strictHenselization :
    IsStrictlyHenselianLocalRing ↑(strictHenselization v) where
  isSepClosed_residueField := inferInstance

end Henselian

end AlgebraicGeometry.Scheme
