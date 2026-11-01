/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ProductTangentSpaceDirectSum
import WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Power maps: tangent spaces and smooth local graph data

Source: the current blueprint, `thm-trf-frobenius-fixed-points`, proof Step 3,
with the local-ring expansion in the DAG proof
(blueprint: lem-trf-power-map-smooth-graph-local-data).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
namespace PowerMapLocalData

/-- The structural map from the base field to a stalk.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def stalkStructure (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (x : X) : k →+* X.presheaf.stalk x :=
  (StructureSheaf.toStalk k (s x) ≫ s.stalkMap x).hom

/-- The structural residue map at a point.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def residueStructure (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (x : X) : k →+* X.residueField x :=
  (X.residue x).hom.comp (stalkStructure k X s x)

/-- The graph morphism into the relative square, without a separatedness assumption.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def graph {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s) : X ⟶ pullback s s :=
  pullback.lift (𝟙 X) h (by simpa using hs.symm)

/-- The fixed-point scheme is the graph/diagonal fibre product.
Source: blueprint Frobenius fixed points, Steps 0 and 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def fixedScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s) : Scheme.{u} :=
  pullback (graph s h hs) (pullback.diagonal s)

/-- The specified fixed rational point lifts canonically to the fixed scheme.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def fixedLift {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ h = x) :
    Spec (.of k) ⟶ fixedScheme s h hs :=
  pullback.lift x x (by
    apply pullback.hom_ext <;> simp [graph, hx])

/-- The structural morphism of the fixed scheme.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def fixedStructure {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s) :
    fixedScheme s h hs ⟶ Spec (.of k) :=
  pullback.fst (graph s h hs) (pullback.diagonal s) ≫ s

/-- The underlying point specified by the fixed rational point.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def fixedPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ h = x) : fixedScheme s h hs :=
  fixedLift s h hs x hx (IsLocalRing.closedPoint k)

/-- The rational product point specified by `(x,x)`.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def productPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) : (pullback s s : Scheme.{u}) :=
  pullback.lift x x rfl (IsLocalRing.closedPoint k)

/-- The stalk map with its target point transported along the specified equality.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hf : f x = y) : Y.presheaf.stalk y →+* X.presheaf.stalk x :=
  ((Y.presheaf.stalkCongr (.of_eq hf)).inv ≫ f.stalkMap x).hom

/-- The structural map into the sections of an open subscheme.
Source: blueprint Frobenius fixed points, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data). -/
noncomputable def sectionStructure {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (O : X.Opens) : k →+* Γ(X, O) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top).hom

end PowerMapLocalData

open PowerMapLocalData

set_option backward.isDefEq.respectTransparency false in
private theorem residueStructure_eq (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (y : X) :
    residueStructure k X s y = s.residueFieldAlgebraMap y := by
  symm
  unfold Scheme.Hom.residueFieldAlgebraMap
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
    Scheme.residue_residueFieldMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rational_residueStructure (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (xs : x ≫ s = 𝟙 _) :
    Function.Bijective (residueStructure k X s (x (IsLocalRing.closedPoint k))) := by
  rw [residueStructure_eq]
  exact s.bijective_residueFieldAlgebraMap_of_comp_eq_id x xs _

set_option backward.isDefEq.respectTransparency false in
private theorem rational_point_canonical (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (xs : x ≫ s = 𝟙 _)
    (hr : Function.Bijective (residueStructure k X s (x (IsLocalRing.closedPoint k)))) :
    Spec.map (CommRingCat.ofHom
      (RingEquiv.ofBijective (residueStructure k X s (x (IsLocalRing.closedPoint k)))
        hr).symm.toRingHom) ≫ X.fromSpecResidueField (x (IsLocalRing.closedPoint k)) = x := by
  let y := x (IsLocalRing.closedPoint k)
  let r := residueStructure k X s y
  let φ := X.descResidueField (Scheme.stalkClosedPointTo x)
  have hφ : Spec.map φ ≫ X.fromSpecResidueField y = x :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x
  have hb : X.fromSpecResidueField y ≫ s = Spec.map (CommRingCat.ofHom r) := by
    change X.fromSpecResidueField y ≫ s = Spec.map
      (CommRingCat.ofHom (residueStructure k X s y))
    rw [residueStructure_eq]
    exact (s.specMap_residueFieldAlgebraMap y).symm
  have he : φ.hom.comp r = RingHom.id k := by
    have hh : CommRingCat.ofHom r ≫ φ = 𝟙 (CommRingCat.of k) := by
      apply Spec.map_inj.mp
      simpa only [Spec.map_comp, Spec.map_id, ← hb, ← Category.assoc, hφ] using xs
    exact congrArg CommRingCat.Hom.hom hh
  have hφeq : φ.hom = (RingEquiv.ofBijective r hr).symm.toRingHom := by
    apply RingHom.ext
    intro a
    obtain ⟨c, rfl⟩ := hr.2 a
    exact (congrArg (fun f : k →+* k ↦ f c) he).trans
      ((RingEquiv.ofBijective r hr).symm_apply_apply c).symm
  calc
    _ = Spec.map φ ≫ X.fromSpecResidueField y := by
      congr 2
      exact CommRingCat.hom_ext hφeq.symm
    _ = x := hφ

set_option backward.isDefEq.respectTransparency false in
private theorem tangent_zero_val (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (y : X) :
    (0 : schemeTangentSpace k X s y).val =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom (X.residueField y)
        (X.residueField y))) ≫ X.fromSpecResidueField y := by
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_tangentVectors_vectorSpace k X s y).2.2.2)).1

set_option backward.isDefEq.respectTransparency false in
private theorem dual_pow_snd (K : Type u) [Field K] (p : ℕ) [CharP K p]
    (n : ℕ) (hn : 1 ≤ n) (a : DualNumber K) : (a ^ (p ^ n)).snd = 0 := by
  rw [TrivSqZeroExt.snd_pow, nsmul_eq_mul]
  simp [Nat.cast_pow, Nat.ne_zero_of_lt hn]

set_option backward.isDefEq.respectTransparency false in
private theorem power_map_dualNumber_ext
    {k B K : Type u} [Field k] [CommRing B] [Field K]
    (p : ℕ) [CharP K p] (n : ℕ) (hn : 1 ≤ n)
    (σ : k →+* B) (r : ℕ) (t : Fin r → B)
    (ht : Subring.closure (Set.range σ ∪ Set.range t) = ⊤)
    (H : B →+* B) (hH : ∀ i, H (t i) = t i ^ (p ^ n))
    (a b : B →+* DualNumber K)
    (hc : ∀ c, a (H (σ c)) = b (σ c))
    (hf : ∀ z, (a (H z)).fst = (b z).fst)
    (hb : ∀ z, (b z).snd = 0) : a.comp H = b := by
  apply RingHom.eq_of_eqOn_set_dense ht
  intro z hz
  rcases hz with ⟨c, rfl⟩ | ⟨i, rfl⟩
  · exact hc c
  · apply TrivSqZeroExt.ext
    · exact hf _
    · change (a (H (t i))).snd = (b (t i)).snd
      rw [hH, map_pow, dual_pow_snd K p n hn, hb]

set_option backward.isDefEq.respectTransparency false in
private theorem affine_appLE_ext {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (O : X.Opens) (hO : IsAffineOpen O)
    (f g : Spec (.of A) ⟶ X) (hf : ⊤ ≤ f ⁻¹ᵁ O) (hg : ⊤ ≤ g ⁻¹ᵁ O)
    (he : f.appLE O ⊤ hf = g.appLE O ⊤ hg) : f = g := by
  have h1 := hO.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hf
  have h2 := hO.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hg
  rw [he] at h1
  rw [h2] at h1
  rw [IsAffineOpen.fromSpec_top] at h1
  exact (cancel_epi (Spec (.of A)).isoSpec.inv).mp h1.symm

private abbrev sectionsToLocal {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : Spec (.of A) ⟶ X) (O : X.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ O) :
    Γ(X, O) ⟶ CommRingCat.of A :=
  f.appLE O ⊤ hf ≫ (Scheme.ΓSpecIso (.of A)).hom

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsToLocal_congr {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f g : Spec (.of A) ⟶ X) (O : X.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ O)
    (hg : ⊤ ≤ g ⁻¹ᵁ O) (he : f = g) :
    sectionsToLocal f O hf = sectionsToLocal g O hg := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsToLocal_post {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (f : Spec (.of A) ⟶ X) (g : X ⟶ Y) (O : Y.Opens) (V : X.Opens)
    (hg : V ≤ g ⁻¹ᵁ O) (hf : ⊤ ≤ f ⁻¹ᵁ V) :
    g.appLE O V hg ≫ sectionsToLocal f V hf =
      sectionsToLocal (f ≫ g) O (hf.trans ((TopologicalSpace.Opens.map f.base).map
        (homOfLE hg)).le) := by
  unfold sectionsToLocal
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsToLocal_pre {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} (f : Spec (.of A) ⟶ X) (O : X.Opens)
    (hf : ⊤ ≤ f ⁻¹ᵁ O) (φ : CommRingCat.of A ⟶ CommRingCat.of B) :
    sectionsToLocal (Spec.map φ ≫ f) O (by
      simpa only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
        TopologicalSpace.Opens.map_top] using
          (TopologicalSpace.Opens.map (Spec.map φ).base).monotone hf) =
      sectionsToLocal f O hf ≫ φ := by
  unfold sectionsToLocal
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) f O ⊤ ⊤ hf (by simp)]
  simp only [Category.assoc]
  have hh : (Spec.map φ).appLE ⊤ ⊤ (by simp) = (Spec.map φ).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [hh, Scheme.ΓSpecIso_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem tangent_closedPoint (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (y : X) (v : schemeTangentSpace k X s y) :
    v.val (IsLocalRing.closedPoint (DualNumber (X.residueField y))) = y := by
  have H := congrArg (fun f : Spec (X.residueField y) ⟶ X ↦
    f (IsLocalRing.closedPoint (X.residueField y))) v.property.1
  have hh : Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (X.residueField y) (X.residueField y)
        (X.residueField y)).toRingHom)
      (IsLocalRing.closedPoint (X.residueField y)) =
      IsLocalRing.closedPoint (DualNumber (X.residueField y)) :=
    by
      have : IsLocalHom (TrivSqZeroExt.fstHom (X.residueField y) (X.residueField y)
          (X.residueField y)).toRingHom :=
        ⟨fun _ h ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h⟩
      exact IsLocalRing.comap_closedPoint _
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at H
  exact (congrArg (fun z ↦ v.val z) hh).symm.trans H

set_option backward.isDefEq.respectTransparency false in
private theorem tangent_power_zero
    (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (h : X ⟶ X) (hs : h ≫ s = s)
    (x : Spec (.of k) ⟶ X) (xs : x ≫ s = 𝟙 _) (hx : x ≫ h = x)
    (O : X.Opens) (hO : IsAffineOpen O) (xO : x (IsLocalRing.closedPoint k) ∈ O)
    (hstable : O ≤ h ⁻¹ᵁ O) (r : ℕ) (t : Fin r → Γ(X, O))
    (ht : Subring.closure (Set.range (sectionStructure s O) ∪ Set.range t) = ⊤)
    (n : ℕ) (hn : 1 ≤ n)
    (hpower : ∀ i, (h.appLE O O hstable).hom (t i) = t i ^ (p ^ n))
    (v : schemeTangentSpace k X s (x (IsLocalRing.closedPoint k))) :
    v.val ≫ h = (0 : schemeTangentSpace k X s (x (IsLocalRing.closedPoint k))).val := by
  let y := x (IsLocalRing.closedPoint k)
  let K := X.residueField y
  let c : Spec (.of K) ⟶ Spec (.of (DualNumber K)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
  let q : Spec (.of (DualNumber K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
  let b := X.fromSpecResidueField y
  let z : schemeTangentSpace k X s y := 0
  have hr := rational_residueStructure k X s x xs
  have : CharP K p := charP_of_injective_ringHom hr.1 p
  have hcanon := rational_point_canonical k X s x xs hr
  let e := RingEquiv.ofBijective (residueStructure k X s y) hr
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.inv)
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ b = x at hcanon
  have hbfix : b ≫ h = b := by
    apply (cancel_epi (Spec.map (CommRingCat.ofHom e.symm.toRingHom))).mp
    simpa only [← Category.assoc, hcanon] using hx
  have hz : z.val = q ≫ b := tangent_zero_val k X s y
  have hyv : ⊤ ≤ v.val ⁻¹ᵁ O :=
    (Scheme.preimage_eq_top_of_closedPoint_mem v.val (by
      simpa only [tangent_closedPoint] using xO)).ge
  have hyz : ⊤ ≤ z.val ⁻¹ᵁ O :=
    (Scheme.preimage_eq_top_of_closedPoint_mem z.val (by
      simpa only [tangent_closedPoint] using xO)).ge
  have hyvh : ⊤ ≤ (v.val ≫ h) ⁻¹ᵁ O :=
    hyv.trans ((TopologicalSpace.Opens.map v.val.base).map (homOfLE hstable)).le
  let a := sectionsToLocal v.val O hyv
  let a₀ := sectionsToLocal z.val O hyz
  have hstruct : (sectionStructure s O) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top).hom := rfl
  have hHσ : (h.appLE O O hstable).hom.comp (sectionStructure s O) =
      sectionStructure s O := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top) ≫
      h.appLE O O hstable).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top).hom
    apply congrArg CommRingCat.Hom.hom
    change (Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top ≫
      h.appLE O O hstable = (Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top
    rw [Scheme.Hom.appLE_comp_appLE, hs]
  have hσ : a.hom.comp (sectionStructure s O) =
      a₀.hom.comp (sectionStructure s O) := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top ≫ a).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top ≫ a₀).hom
    dsimp only [a, a₀]
    rw [sectionsToLocal_post, sectionsToLocal_post]
    have hvs : v.val ≫ s = z.val ≫ s := v.property.2.trans z.property.2.symm
    simp only [hvs]
    rfl
  have hc : c ≫ v.val ≫ h = c ≫ z.val := by
    rw [← Category.assoc c v.val, v.property.1, hbfix]
    rw [hz, ← Category.assoc c q]
    have hcq : c ≫ q = 𝟙 _ := by
      dsimp [c, q]
      rw [← Spec.map_comp]
      change Spec.map (𝟙 (.of K)) = 𝟙 _
      exact Spec.map_id _
    rw [hcq, Category.id_comp]
  have hf : ∀ w, (a.hom ((h.appLE O O hstable).hom w)).fst = (a₀.hom w).fst := by
    intro w
    have hh : h.appLE O O hstable ≫ a ≫ CommRingCat.ofHom
        (TrivSqZeroExt.fstHom K K K).toRingHom =
        a₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom := by
      rw [← Category.assoc, sectionsToLocal_post,
        ← sectionsToLocal_pre, ← sectionsToLocal_pre]
      apply sectionsToLocal_congr
      exact hc
    exact congrArg (fun f : Γ(X, O) ⟶ CommRingCat.of K ↦ f.hom w) hh
  have hb : ∀ w, (a₀.hom w).snd = 0 := by
    have hh : a₀ = sectionsToLocal b O (by
        rw [Scheme.preimage_eq_top_of_closedPoint_mem b (by
          simpa only [b, Scheme.fromSpecResidueField_apply] using xO)]) ≫
        CommRingCat.ofHom (TrivSqZeroExt.inlHom K K) := by
      dsimp only [a₀]
      calc
        _ = sectionsToLocal (q ≫ b) O _ :=
          sectionsToLocal_congr _ _ _ _ _ hz
        _ = _ := sectionsToLocal_pre b O _ _
    intro w
    rw [hh]
    rfl
  have heq := power_map_dualNumber_ext p n hn (sectionStructure s O) r t ht
    (h.appLE O O hstable).hom hpower a.hom a₀.hom
    (fun (c : k) ↦ by
      have hh := congrArg (fun f : k →+* Γ(X, O) ↦ f c) hHσ
      change a.hom ((h.appLE O O hstable).hom ((sectionStructure s O) c)) = _
      change (h.appLE O O hstable).hom ((sectionStructure s O) c) = _ at hh
      rw [hh]
      exact congrArg (fun f : k →+* DualNumber K ↦ f c) hσ) hf hb
  apply affine_appLE_ext O hO (v.val ≫ h) z.val hyvh hyz
  apply (cancel_mono (Scheme.ΓSpecIso (.of (DualNumber K))).hom).mp
  change sectionsToLocal (v.val ≫ h) O hyvh = a₀
  rw [← sectionsToLocal_post v.val h O O hstable hyv]
  exact CommRingCat.hom_ext heq

set_option backward.isDefEq.respectTransparency false in
private theorem rational_product_tangent
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (xs : x ≫ s = 𝟙 _)
    (hr : Function.Bijective (residueStructure k X s (x (IsLocalRing.closedPoint k)))) :
    let y := x (IsLocalRing.closedPoint k)
    let z := productPoint s x
    let d := Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
      ((residueStructure k (pullback s s) (pullback.fst s s ≫ s) z).comp
        (RingEquiv.ofBijective (residueStructure k X s y) hr).symm.toRingHom)))
    ∃ E : schemeTangentSpace k (pullback s s) (pullback.fst s s ≫ s) z ≃ₗ[k]
        (schemeTangentSpace k X s y × schemeTangentSpace k X s y),
      ∀ v, v.val ≫ pullback.fst s s = d ≫ (E v).1.val ∧
        v.val ≫ pullback.snd s s = d ≫ (E v).2.val := by
  let y := x (IsLocalRing.closedPoint k)
  let r := residueStructure k X s y
  let a := Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective r hr).symm.toRingHom) ≫
    X.fromSpecResidueField y
  have ha : a = x := rational_point_canonical k X s x xs hr
  let i : X ⟶ pullback s s := pullback.lift (𝟙 X) (s ≫ a) (by
    rw [ha, Category.id_comp, Category.assoc, xs, Category.comp_id])
  have hi : x ≫ i = pullback.lift x x rfl := by
    apply pullback.hom_ext
    · simp [i, Category.assoc]
    · simp [i, Category.assoc, ← Category.assoc x s, xs, ha]
  have hz : i y = productPoint s x :=
    congrArg (fun f : Spec (.of k) ⟶ pullback s s ↦ f (IsLocalRing.closedPoint k)) hi
  have H : ∃ E : schemeTangentSpace k (pullback s s) (pullback.fst s s ≫ s) (i y) ≃ₗ[k]
      (schemeTangentSpace k X s y × schemeTangentSpace k X s y),
      ∀ v, v.val ≫ pullback.fst s s =
          Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
            ((residueStructure k (pullback s s) (pullback.fst s s ≫ s) (i y)).comp
              (RingEquiv.ofBijective r hr).symm.toRingHom))) ≫ (E v).1.val ∧
        v.val ≫ pullback.snd s s =
          Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
            ((residueStructure k (pullback s s) (pullback.fst s s ≫ s) (i y)).comp
              (RingEquiv.ofBijective r hr).symm.toRingHom))) ≫ (E v).2.val := by
    obtain ⟨E, hE, _, _⟩ := product_tangentSpace_directSum k X X s s y y hr hr
    exact ⟨E, hE⟩
  rw [hz] at H
  exact H

set_option backward.isDefEq.respectTransparency false in
private theorem rational_tangent_dimension
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k)) (y : X)
    (hr : Function.Bijective (residueStructure k X s y))
    [IsRegularLocalRing (X.presheaf.stalk y)] :
    ringKrullDim (X.presheaf.stalk y) =
      Module.finrank k (schemeTangentSpace k X s y) := by
  let R : Type u := X.presheaf.stalk y
  let K : Type u := X.residueField y
  let : Module (X.residueField y) (IsLocalRing.CotangentSpace (X.presheaf.stalk y)) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField (X.presheaf.stalk y))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk y)))
  let r := residueStructure k X s y
  let : Module k (IsLocalRing.CotangentSpace (X.presheaf.stalk y)) :=
    Module.compHom (IsLocalRing.CotangentSpace (X.presheaf.stalk y)) r
  have rankC : Module.rank k (IsLocalRing.CotangentSpace R) =
      Module.rank K (IsLocalRing.CotangentSpace R) :=
    rank_eq_of_equiv_equiv r (AddEquiv.refl _) hr (fun _ _ ↦ rfl)
  have finrankC : Module.finrank k (IsLocalRing.CotangentSpace R) =
      Module.finrank K (IsLocalRing.CotangentSpace R) := congrArg Cardinal.toNat rankC
  obtain ⟨E, _⟩ := exists_rationalPoint_tangent_cotangent_linearEquiv k X s y hr
  have hdim := E.finrank_eq
  rw [Subspace.dual_finrank_eq, finrankC] at hdim
  exact ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm.trans
    (congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞)) hdim.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem graph_chart
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (h : X ⟶ X) (hs : h ≫ s = s) (x : Spec (.of k) ⟶ X)
    (_xs : x ≫ s = 𝟙 _) (hx : x ≫ h = x)
    (U : X.Opens) (xU : x (IsLocalRing.closedPoint k) ∈ U) [Smooth (U.ι ≫ s)] :
    ∃ (W V : X.Opens) (hWV : W ≤ V),
      V ≤ U ∧ x (IsLocalRing.closedPoint k) ∈ W ∧
      IsAffineOpen W ∧ IsAffineOpen V ∧ W ≤ h ⁻¹ᵁ V ∧
      Smooth (pullback.fst (W.ι ≫ s) (V.ι ≫ s) ≫ W.ι ≫ s) ∧
    ∃ (hW : W.toScheme ⟶ V.toScheme), hW ≫ V.ι = W.ι ≫ h ∧
    ∃ (gW dW : W.toScheme ⟶ pullback (W.ι ≫ s) (V.ι ≫ s)),
      gW ≫ pullback.fst _ _ = 𝟙 _ ∧ gW ≫ pullback.snd _ _ = hW ∧
      dW ≫ pullback.fst _ _ = 𝟙 _ ∧ dW ≫ pullback.snd _ _ = X.homOfLE hWV ∧
      IsClosedImmersion gW ∧ IsClosedImmersion dW ∧
    ∃ (m : pullback (W.ι ≫ s) (V.ι ≫ s) ⟶ pullback s s),
      m ≫ pullback.fst s s = pullback.fst _ _ ≫ W.ι ∧
      m ≫ pullback.snd s s = pullback.snd _ _ ≫ V.ι ∧
      IsOpenImmersion m ∧ productPoint s x ∈ Set.range m := by
  obtain ⟨_, ⟨V, hV, rfl⟩, xV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open xU U.isOpen
  have hxy : h (x (IsLocalRing.closedPoint k)) = x (IsLocalRing.closedPoint k) :=
    congrArg (fun f : Spec (.of k) ⟶ X ↦ f (IsLocalRing.closedPoint k)) hx
  obtain ⟨_, ⟨W, hW, rfl⟩, xW, hWsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x (IsLocalRing.closedPoint k) ∈ V ⊓ h ⁻¹ᵁ V from ⟨xV, by simpa [hxy]⟩)
      (V ⊓ h ⁻¹ᵁ V).isOpen
  let W : X.Opens := W
  let V : X.Opens := V
  have hWV : W ≤ V := fun z hz ↦ (hWsub hz).1
  have hWhV : W ≤ h ⁻¹ᵁ V := fun z hz ↦ (hWsub hz).2
  have : Smooth (V.ι ≫ s) := by
    rw [← X.homOfLE_ι hVU, Category.assoc]
    infer_instance
  have : Smooth (W.ι ≫ s) := by
    rw [← X.homOfLE_ι hWV, Category.assoc]
    infer_instance
  let hW' := h.resLE V W hWhV
  have hh : hW' ≫ (V.ι ≫ s) = W.ι ≫ s := by
    dsimp only [hW']
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hs]
  let gW := pullback.lift (𝟙 W.toScheme) hW' ((Category.id_comp _).trans hh.symm)
  let dW : W.toScheme ⟶
      pullback (W.ι ≫ s) (V.ι ≫ s) :=
    pullback.lift (𝟙 W.toScheme) (X.homOfLE hWV)
    (by rw [Category.id_comp, ← Category.assoc, Scheme.homOfLE_ι])
  have : IsAffine V.toScheme := hV
  have : IsSeparated (pullback.fst (W.ι ≫ s) (V.ι ≫ s)) := inferInstance
  have hgW : IsClosedImmersion gW := by
    have : IsClosedImmersion (gW ≫ pullback.fst (W.ι ≫ s) (V.ι ≫ s)) := by
      simp only [gW, pullback.lift_fst]
      infer_instance
    exact IsClosedImmersion.of_comp gW (pullback.fst _ _)
  have hdW : IsClosedImmersion dW := by
    have : IsClosedImmersion (dW ≫ pullback.fst (W.ι ≫ s) (V.ι ≫ s)) := by
      simp only [dW, pullback.lift_fst]
      infer_instance
    exact IsClosedImmersion.of_comp dW (pullback.fst _ _)
  let m := pullback.map (W.ι ≫ s) (V.ι ≫ s) s s W.ι V.ι (𝟙 _)
    (by simp) (by simp)
  have hm : IsOpenImmersion m := inferInstance
  have xWtop : ⊤ ≤ x ⁻¹ᵁ W := (Scheme.preimage_eq_top_of_closedPoint_mem x xW).ge
  let xW' := x.resLE W ⊤ xWtop
  let xW'' := (Spec (.of k)).topIso.inv ≫ xW'
  have hxW' : xW'' ≫ W.ι = x := by simp [xW'', xW', Scheme.Hom.resLE_comp_ι]
  let xV' := xW'' ≫ X.homOfLE hWV
  have hxV' : xV' ≫ V.ι = x := by simp [xV', hxW']
  let xp : Spec (.of k) ⟶
      pullback (W.ι ≫ s) (V.ι ≫ s) :=
    pullback.lift xW'' xV' (by
    simp only [← Category.assoc, hxW', hxV'])
  have hxp : xp ≫ m = pullback.lift x x rfl := by
    apply pullback.hom_ext <;> simp [xp, m, hxW', hxV']
  refine ⟨W, V, hWV, hVU, xW, hW, hV, hWhV, inferInstance,
    hW', Scheme.Hom.resLE_comp_ι _ _, gW, dW,
    pullback.lift_fst .., pullback.lift_snd .., pullback.lift_fst ..,
    pullback.lift_snd .., hgW, hdW, m, pullback.lift_fst .., pullback.lift_snd .., hm, ?_⟩
  exact ⟨xp (IsLocalRing.closedPoint k),
    congrArg (fun f : Spec (.of k) ⟶ pullback s s ↦ f (IsLocalRing.closedPoint k)) hxp⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem spec_stalkMapAt {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (y : Y) (z : Z) (e : f y = z) :
    Spec.map (CommRingCat.ofHom (stalkMapAt f y z e)) ≫ Z.fromSpecStalk z =
      Y.fromSpecStalk y ≫ f := by
  subst z
  simpa only [stalkMapAt, TopCat.Presheaf.stalkCongr_inv, Iso.symm_inv,
    eqToHom_refl, Category.id_comp, CommRingCat.ofHom_hom, Spec.map_comp,
    Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc] using
    Scheme.SpecMap_stalkMap_fromSpecStalk f (x := y)

set_option backward.isDefEq.respectTransparency false in
private theorem stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (e : f x = y) (e' : g y = z)
    (e'' : (f ≫ g) x = z) :
    stalkMapAt (f ≫ g) x z e'' = (stalkMapAt f x y e).comp (stalkMapAt g y z e') := by
  suffices H : CommRingCat.ofHom (stalkMapAt (f ≫ g) x z e'') =
      CommRingCat.ofHom ((stalkMapAt f x y e).comp (stalkMapAt g y z e')) by
    exact congrArg CommRingCat.Hom.hom H
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk z)).mp
  rw [spec_stalkMapAt]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [Category.assoc, spec_stalkMapAt, ← Category.assoc,
    ← Category.assoc, spec_stalkMapAt]

set_option backward.isDefEq.respectTransparency false in
private theorem stalkMapAt_section_surjective {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ Y) (hfg : f ≫ g = 𝟙 Y)
    (y : Y) (z : Z) (e : f y = z) :
    Function.Surjective (stalkMapAt f y z e) := by
  have e' : g z = y := by
    rw [← e, ← Scheme.Hom.comp_apply, hfg]
    rfl
  have e'' : (f ≫ g) y = y := by rw [hfg]; rfl
  have H := stalkMapAt_comp f g y z y e e' e''
  have HI : stalkMapAt (f ≫ g) y y e'' = RingHom.id _ := by
    suffices H : CommRingCat.ofHom (stalkMapAt (f ≫ g) y y e'') = 𝟙 _ by
      exact congrArg CommRingCat.Hom.hom H
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk y)).mp
    rw [spec_stalkMapAt, hfg]
    simp
  rw [HI] at H
  intro a
  exact ⟨stalkMapAt g z y e' a, (RingHom.congr_fun H a).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem local_source_factor {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (l : Spec (.of R) ⟶ Y) (y : Y)
    (e : l (IsLocalRing.closedPoint R) = y) :
    ∃ u : Y.presheaf.stalk y →+* R, IsLocalHom u ∧
      Spec.map (CommRingCat.ofHom u) ≫ Y.fromSpecStalk y = l := by
  subst y
  exact ⟨(Scheme.stalkClosedPointTo l).hom, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk l⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem stalk_pullback_quotient {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Mono g]
    (w : ↥(pullback f g)) (x : X) (y : Y) (z : Z)
    (hwx : pullback.fst f g w = x) (hwy : pullback.snd f g w = y)
    (hxz : f x = z) (hyz : g y = z)
    (hf : Function.Surjective (stalkMapAt f x z hxz))
    (hg : Function.Surjective (stalkMapAt g y z hyz))
    (hwz : (pullback.fst f g ≫ f) w = z) :
    ∃ e : (Z.presheaf.stalk z ⧸
        (RingHom.ker (stalkMapAt f x z hxz) ⊔ RingHom.ker (stalkMapAt g y z hyz))) ≃+*
        (pullback f g).presheaf.stalk w,
      ∀ a, e (Ideal.Quotient.mk _ a) = stalkMapAt (pullback.fst f g ≫ f) w z hwz a := by
  let A := Z.presheaf.stalk z
  let B := X.presheaf.stalk x
  let C := Y.presheaf.stalk y
  let D := (pullback f g).presheaf.stalk w
  let α := stalkMapAt f x z hxz
  let β := stalkMapAt g y z hyz
  let π := stalkMapAt (pullback.fst f g ≫ f) w z hwz
  let σ := stalkMapAt (pullback.fst f g) w x hwx
  let τ := stalkMapAt (pullback.snd f g) w y hwy
  have hπα : π = σ.comp α := stalkMapAt_comp _ _ _ _ _ _ _ _
  have hwz' : (pullback.snd f g ≫ g) w = z := by
    rw [← pullback.condition (f := f) (g := g)]; exact hwz
  have hπβ : π = τ.comp β := by
    rw [← stalkMapAt_comp _ _ w y z hwy hyz hwz']
    dsimp only [π]
    congr 1
    exact pullback.condition (f := f) (g := g)
  let K := RingHom.ker α ⊔ RingHom.ker β
  have hK : K ≤ RingHom.ker π := sup_le
    (by intro a ha; change π a = 0; rw [hπα]; simpa using congrArg σ ha)
    (by intro a ha; change π a = 0; rw [hπβ]; simpa using congrArg τ ha)
  have hKproper : K ≠ ⊤ := by
    intro H
    have : (1 : A) ∈ RingHom.ker π := hK (H ▸ (show (1 : A) ∈ (⊤ : Ideal A) from trivial))
    exact one_ne_zero ((map_one π).symm.trans this)
  let Q := A ⧸ K
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hKproper
  let q : A →+* Q := Ideal.Quotient.mk K
  have : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let j : Q →+* D := Ideal.Quotient.lift K π hK
  have hqb : RingHom.ker α ≤ RingHom.ker q := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show RingHom.ker α ≤ K from le_sup_left) ha)
  have hqc : RingHom.ker β ≤ RingHom.ker q := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show RingHom.ker β ≤ K from le_sup_right) ha)
  let b : B →+* Q := α.liftOfSurjective hf ⟨q, hqb⟩
  let c : C →+* Q := β.liftOfSurjective hg ⟨q, hqc⟩
  have hb : b.comp α = q := RingHom.liftOfSurjective_comp _ _ _
  have hc : c.comp β = q := RingHom.liftOfSurjective_comp _ _ _
  have hbSurj : Function.Surjective b := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨α a, RingHom.congr_fun hb a⟩
  have hcSurj : Function.Surjective c := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨β a, RingHom.congr_fun hc a⟩
  have : IsLocalHom b := IsLocalHom.of_surjective b hbSurj
  have : IsLocalHom c := IsLocalHom.of_surjective c hcSurj
  let lX := Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk x
  let lY := Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk y
  have hlX : lX ≫ f = Spec.map (CommRingCat.ofHom q) ≫ Z.fromSpecStalk z := by
    dsimp only [lX]
    rw [Category.assoc, ← spec_stalkMapAt f x z hxz, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  have hlY : lY ≫ g = Spec.map (CommRingCat.ofHom q) ≫ Z.fromSpecStalk z := by
    dsimp only [lY]
    rw [Category.assoc, ← spec_stalkMapAt g y z hyz, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let l := pullback.lift lX lY (hlX.trans hlY.symm)
  have hlw : l (IsLocalRing.closedPoint Q) = w := by
    apply (pullback.fst f g).injective
    change (l ≫ pullback.fst f g) _ = _
    rw [pullback.lift_fst, hwx]
    dsimp only [lX]
    rw [Scheme.Hom.comp_apply, Spec_closedPoint]
    exact Scheme.fromSpecStalk_closedPoint (x := x)
  obtain ⟨u, hu, huf⟩ := local_source_factor l w hlw
  have hju : u.comp j = RingHom.id Q := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change u (π a) = q a
    suffices H : u.comp π = q from RingHom.congr_fun H a
    suffices H : CommRingCat.ofHom (u.comp π) = CommRingCat.ofHom q by
      exact congrArg CommRingCat.Hom.hom H
    apply Spec.map_injective
    apply (cancel_mono (Z.fromSpecStalk z)).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, spec_stalkMapAt,
      ← Category.assoc, huf]
    rw [← Category.assoc, pullback.lift_fst, hlX]
  have hjb : j.comp b = σ := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := hf a
    have h : b (α a) = q a := RingHom.congr_fun hb a
    change j (b (α a)) = σ (α a)
    rw [h]
    exact RingHom.congr_fun hπα a
  have hjc : j.comp c = τ := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := hg a
    have h : c (β a) = q a := RingHom.congr_fun hc a
    change j (c (β a)) = τ (β a)
    rw [h]
    exact RingHom.congr_fun hπβ a
  have huj : j.comp u = RingHom.id D := by
    suffices H : CommRingCat.ofHom (j.comp u) = 𝟙 D by
      exact congrArg CommRingCat.Hom.hom H
    apply Spec.map_injective
    apply (cancel_mono ((pullback f g).fromSpecStalk w)).mp
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, huf]
    rw [Spec.map_id D]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      dsimp only [lX]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb,
        spec_stalkMapAt]
      exact congrArg (fun a ↦ a ≫ pullback.fst f g)
        (Category.id_comp ((pullback f g).fromSpecStalk w)).symm
    · rw [Category.assoc, pullback.lift_snd]
      dsimp only [lY]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjc,
        spec_stalkMapAt]
      exact congrArg (fun a ↦ a ≫ pullback.snd f g)
        (Category.id_comp ((pullback f g).fromSpecStalk w)).symm
  exact ⟨{ j with invFun := u
                  left_inv := fun a ↦ RingHom.congr_fun hju a
                  right_inv := fun a ↦ RingHom.congr_fun huj a }, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_base (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (y : X) :
    X.fromSpecStalk y ≫ s = Spec.map (CommRingCat.ofHom (stalkStructure k X s y)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq,
    ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem stalkStructure_natural (k : Type u) [Field k] (X Y : Scheme.{u})
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (x : X) (y : Y) (hxy : f x = y) :
    (stalkMapAt f x y hxy).comp (stalkStructure k Y sY y) = stalkStructure k X sX x := by
  suffices H : CommRingCat.ofHom ((stalkMapAt f x y hxy).comp
      (stalkStructure k Y sY y)) = CommRingCat.ofHom (stalkStructure k X sX x) by
    exact congrArg CommRingCat.Hom.hom H
  apply Spec.map_injective
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← stalk_base, ← Category.assoc,
    spec_stalkMapAt, Category.assoc, hf, stalk_base]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_residue_bijective {k A B : Type u} [Field k]
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (a : k →+* A) (b : k →+* B) (f : A →+* B) (hf : Function.Surjective f)
    (hfab : f.comp a = b)
    (hb : Function.Bijective ((IsLocalRing.residue B).comp b))
    [IsLocalRing (A ⧸ RingHom.ker f)] :
    Function.Bijective ((IsLocalRing.residue (A ⧸ RingHom.ker f)).comp
      ((Ideal.Quotient.mk _).comp a)) := by
  let e := f.quotientKerEquivOfSurjective hf
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let r := IsLocalRing.ResidueField.mapEquiv e
  have H : r.toRingHom.comp ((IsLocalRing.residue (A ⧸ RingHom.ker f)).comp
      ((Ideal.Quotient.mk _).comp a)) = (IsLocalRing.residue B).comp b := by
    ext c
    change IsLocalRing.ResidueField.map e.toRingHom
      (IsLocalRing.residue _ (Ideal.Quotient.mk _ (a c))) = _
    rw [IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue B (f (a c)) = _
    exact congrArg (IsLocalRing.residue B) (RingHom.congr_fun hfab c)
  refine ⟨(RingHom.comp _ _).injective, ?_⟩
  intro c
  obtain ⟨d, hd⟩ := hb.2 (r c)
  exact ⟨d, r.injective ((RingHom.congr_fun H d).trans hd)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem regular_at_open {X Y : Scheme.{u}} (m : X ⟶ Y) [IsOpenImmersion m]
    [IsRegular X] (y : Y) (hy : y ∈ Set.range m) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := hy
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (m.stalkMap x)).commRingCatIsoToRingEquiv.symm

set_option backward.isDefEq.respectTransparency false in
private theorem graph_point (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (h : X ⟶ X) (hs : h ≫ s = s)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ h = x) :
    graph s h hs (x (IsLocalRing.closedPoint k)) = productPoint s x := by
  have he : x ≫ graph s h hs = pullback.lift x x rfl := by
    apply pullback.hom_ext <;> simp [graph, hx]
  exact congrArg (fun f : Spec (.of k) ⟶ pullback s s ↦ f (IsLocalRing.closedPoint k)) he

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_point (k : Type u) [Field k] (X : Scheme.{u})
    (s : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) :
    pullback.diagonal s (x (IsLocalRing.closedPoint k)) = productPoint s x := by
  have he : x ≫ pullback.diagonal s = pullback.lift x x rfl := by
    apply pullback.hom_ext <;> simp
  exact congrArg (fun f : Spec (.of k) ⟶ pullback s s ↦ f (IsLocalRing.closedPoint k)) he

set_option backward.isDefEq.respectTransparency false in
/-- The power differential vanishes even at singular points; at smooth fixed points with
structurally trivial equalizer stalk, the graph and diagonal have the asserted local data.
Source: main-20261015, thm-trf-frobenius-fixed-points.proof.md, Step 3
(blueprint: lem-trf-power-map-smooth-graph-local-data).

Proof:
1. Every dual-number tangent vector factors through the given affine neighbourhood.
   Its composite with h agrees with the zero vector on constants and generators:
   the fixed-point identity determines first coordinates, and the square-zero power
   formula in characteristic p makes the second coordinate of a p^n-th power zero.
2. The product tangent equivalence identifies the graph and diagonal with (v,0)
   and (v,v). Their intersection is zero, and (a,b)=(a-b,0)+(b,b) proves their sum is full.
3. Smooth regularity transfers to the source stalk. The rational tangent/cotangent
   equivalence and regular-local cotangent dimension formula compute its dimension.
4. Choose affine V inside U and affine W inside V intersect h^{-1}(V). The local
   product is smooth. Both graph maps are sections of its separated first projection,
   hence closed immersions. Its open immersion into the global product identifies
   stalks; regularity and the product tangent formula give the ambient dimension 2d.
5. Graph and diagonal are sections of the first global projection, so their stalk
   maps are surjective. The quotient-by-kernel equivalences transfer regularity,
   dimensions and the structural residue-field identifications from the source stalk.
6. The quotient by the sum of kernels is the fixed-scheme stalk: quotient maps from
   both source stalks give a morphism from its local spectrum to the pullback, whose
   closed point is the specified fixed point. The local-spectrum universal property
   provides the inverse stalk homomorphism. Check both composites by cancelling
   canonical stalk-to-scheme monomorphisms and using pullback extensionality.
7. Compose this equivalence with the inverse of the assumed structural isomorphism
   from k. The resulting quotient map to k has the ambient maximal ideal as its kernel.
-/
theorem powerMap_smooth_graph_local_data
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : p.Prime)
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s]
    (h : X ⟶ X) (hs : h ≫ s = s)
    (x : Spec (.of k) ⟶ X) (xs : x ≫ s = 𝟙 _) (hx : x ≫ h = x)
    (O : X.Opens) (hO : IsAffineOpen O) (xO : x (IsLocalRing.closedPoint k) ∈ O)
    (hstable : O ≤ h ⁻¹ᵁ O) (r : ℕ) (t : Fin r → Γ(X, O))
    (ht : Subring.closure (Set.range (sectionStructure s O) ∪ Set.range t) = ⊤)
    (n : ℕ) (hn : 1 ≤ n)
    (hpower : ∀ i : Fin r, (h.appLE O O hstable).hom (t i) = t i ^ (p ^ n)) :
    ∃ (hr : Function.Bijective
        (residueStructure k X s (x (IsLocalRing.closedPoint k))))
      (hg : graph s h hs (x (IsLocalRing.closedPoint k)) = productPoint s x)
      (hd : pullback.diagonal s (x (IsLocalRing.closedPoint k)) = productPoint s x),
    ∃ D : schemeTangentSpace k X s (x (IsLocalRing.closedPoint k)) →ₗ[k]
        schemeTangentSpace k X s (x (IsLocalRing.closedPoint k)),
      (∀ v, (D v).val = v.val ≫ h) ∧ D = 0 ∧ LinearMap.id - D = LinearMap.id ∧
    ∃ E : schemeTangentSpace k (pullback s s) (pullback.fst s s ≫ s)
        (productPoint s x) ≃ₗ[k]
      (schemeTangentSpace k X s (x (IsLocalRing.closedPoint k)) ×
        schemeTangentSpace k X s (x (IsLocalRing.closedPoint k))),
      (∀ v, v.val ≫ pullback.fst s s =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((residueStructure k (pullback s s) (pullback.fst s s ≫ s)
            (productPoint s x)).comp
            (RingEquiv.ofBijective
              (residueStructure k X s (x (IsLocalRing.closedPoint k))) hr).symm.toRingHom))) ≫
          (E v).1.val) ∧
      (∀ v, v.val ≫ pullback.snd s s =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((residueStructure k (pullback s s) (pullback.fst s s ≫ s)
            (productPoint s x)).comp
            (RingEquiv.ofBijective
              (residueStructure k X s (x (IsLocalRing.closedPoint k))) hr).symm.toRingHom))) ≫
          (E v).2.val) ∧
      (∀ v, (E.symm (v, 0)).val =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((residueStructure k (pullback s s) (pullback.fst s s ≫ s)
            (productPoint s x)).comp
            (RingEquiv.ofBijective
              (residueStructure k X s (x (IsLocalRing.closedPoint k))) hr).symm.toRingHom))) ≫
          v.val ≫ graph s h hs) ∧
      (∀ v, (E.symm (v, v)).val =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((residueStructure k (pullback s s) (pullback.fst s s ≫ s)
            (productPoint s x)).comp
            (RingEquiv.ofBijective
              (residueStructure k X s (x (IsLocalRing.closedPoint k))) hr).symm.toRingHom))) ≫
          v.val ≫ pullback.diagonal s) ∧
      (Set.range (fun v ↦ E.symm (v, 0)) ∩ Set.range (fun v ↦ E.symm (v, v)) = {0}) ∧
      (∀ a, ∃ v w, a = E.symm (v, 0) + E.symm (w, w)) ∧
      ∀ (U : X.Opens), x (IsLocalRing.closedPoint k) ∈ U → Smooth (U.ι ≫ s) →
        Function.Bijective
          (stalkStructure k (fixedScheme s h hs) (fixedStructure s h hs)
            (fixedPoint s h hs x hx)) →
      ∃ (d : ℕ),
        ringKrullDim (X.presheaf.stalk (x (IsLocalRing.closedPoint k))) = d ∧
        Module.finrank k (schemeTangentSpace k X s (x (IsLocalRing.closedPoint k))) = d ∧
      ∃ (W V : X.Opens) (hWV : W ≤ V),
        V ≤ U ∧ x (IsLocalRing.closedPoint k) ∈ W ∧
        IsAffineOpen W ∧ IsAffineOpen V ∧ W ≤ h ⁻¹ᵁ V ∧
        Smooth (pullback.fst (W.ι ≫ s) (V.ι ≫ s) ≫ W.ι ≫ s) ∧
      ∃ (hW : W.toScheme ⟶ V.toScheme), hW ≫ V.ι = W.ι ≫ h ∧
      ∃ (gW dW : W.toScheme ⟶ pullback (W.ι ≫ s) (V.ι ≫ s)),
        gW ≫ pullback.fst _ _ = 𝟙 _ ∧ gW ≫ pullback.snd _ _ = hW ∧
        dW ≫ pullback.fst _ _ = 𝟙 _ ∧ dW ≫ pullback.snd _ _ = X.homOfLE hWV ∧
        IsClosedImmersion gW ∧ IsClosedImmersion dW ∧
      ∃ (m : pullback (W.ι ≫ s) (V.ι ≫ s) ⟶ pullback s s),
        m ≫ pullback.fst s s = pullback.fst _ _ ≫ W.ι ∧
        m ≫ pullback.snd s s = pullback.snd _ _ ≫ V.ι ∧
        IsOpenImmersion m ∧ productPoint s x ∈ Set.range m ∧
      ∃ (I J : Ideal ((pullback s s).presheaf.stalk (productPoint s x))),
        I = RingHom.ker (stalkMapAt (graph s h hs) (x (IsLocalRing.closedPoint k))
          (productPoint s x) hg) ∧
        J = RingHom.ker (stalkMapAt (pullback.diagonal s) (x (IsLocalRing.closedPoint k))
          (productPoint s x) hd) ∧
      ∃ (_ : IsRegularLocalRing ((pullback s s).presheaf.stalk (productPoint s x)))
        (_ : IsRegularLocalRing (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ I))
        (_ : IsRegularLocalRing (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ J)),
        Function.Bijective
          (residueStructure k (pullback s s) (pullback.fst s s ≫ s) (productPoint s x)) ∧
        Function.Bijective
          ((IsLocalRing.residue (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ I)).comp
            ((Ideal.Quotient.mk I).comp (stalkStructure k (pullback s s)
              (pullback.fst s s ≫ s) (productPoint s x)))) ∧
        Function.Bijective
          ((IsLocalRing.residue (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ J)).comp
            ((Ideal.Quotient.mk J).comp (stalkStructure k (pullback s s)
              (pullback.fst s s ≫ s) (productPoint s x)))) ∧
        ringKrullDim ((pullback s s).presheaf.stalk (productPoint s x)) = 2 * d ∧
        ringKrullDim (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ I) = d ∧
        ringKrullDim (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ J) = d ∧
        I ⊔ J = IsLocalRing.maximalIdeal
          ((pullback s s).presheaf.stalk (productPoint s x)) ∧
      ∃ (eI : (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ I) ≃+*
          X.presheaf.stalk (x (IsLocalRing.closedPoint k)))
        (eJ : (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ J) ≃+*
          X.presheaf.stalk (x (IsLocalRing.closedPoint k))),
        (∀ a, eI (Ideal.Quotient.mk I a) =
          stalkMapAt (graph s h hs) (x (IsLocalRing.closedPoint k)) (productPoint s x) hg a) ∧
        (∀ a, eJ (Ideal.Quotient.mk J a) =
          stalkMapAt (pullback.diagonal s) (x (IsLocalRing.closedPoint k))
            (productPoint s x) hd a) ∧
      ∃ (hf : (pullback.fst (graph s h hs) (pullback.diagonal s) ≫ graph s h hs)
          (fixedPoint s h hs x hx) = productPoint s x)
        (eF : (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ (I ⊔ J)) ≃+*
          (fixedScheme s h hs).presheaf.stalk (fixedPoint s h hs x hx))
        (eK : (((pullback s s).presheaf.stalk (productPoint s x)) ⧸ (I ⊔ J)) ≃+* k),
        (∀ a, eF (Ideal.Quotient.mk (I ⊔ J) a) =
          stalkMapAt (pullback.fst (graph s h hs) (pullback.diagonal s) ≫ graph s h hs)
            (fixedPoint s h hs x hx) (productPoint s x) hf a) ∧
        ∀ c : k, eK (eF.symm
          (stalkStructure k (fixedScheme s h hs) (fixedStructure s h hs)
            (fixedPoint s h hs x hx) c)) = c := by
  have _hp := hp
  have hr := rational_residueStructure k X s x xs
  have hg := graph_point k X s h hs x hx
  have hd := diagonal_point k X s x
  refine ⟨hr, hg, hd, (0 : schemeTangentSpace k X s _ →ₗ[k] _), ?_, rfl, sub_zero _, ?_⟩
  · intro v
    simp only [LinearMap.zero_apply]
    exact (tangent_power_zero k p X s h hs x xs hx O hO xO hstable r t ht n hn hpower v).symm
  · obtain ⟨E, hE⟩ := rational_product_tangent k X s x xs hr
    refine ⟨E, fun v ↦ (hE v).1, fun v ↦ (hE v).2, ?_, ?_, ?_, ?_, ?_⟩
    · intro v
      apply pullback.hom_ext
      · simpa only [Category.assoc, graph, pullback.lift_fst, Category.comp_id,
          LinearEquiv.apply_symm_apply] using (hE (E.symm (v, 0))).1
      · simp only [Category.assoc]
        rw [show graph s h hs ≫ pullback.snd s s = h from
          pullback.lift_snd .., tangent_power_zero k p X s h hs x xs hx O hO xO
          hstable r t ht n hn hpower]
        simpa only [LinearEquiv.apply_symm_apply] using (hE (E.symm (v, 0))).2
    · intro v
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
          LinearEquiv.apply_symm_apply] using (hE (E.symm (v, v))).1
      · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
          LinearEquiv.apply_symm_apply] using (hE (E.symm (v, v))).2
    · ext a
      constructor
      · rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
        have H : (v, 0) = (w, w) := E.symm.injective (hv.trans hw.symm)
        have hw0 : w = 0 := (congrArg Prod.snd H).symm
        have hv0 : v = 0 := (congrArg Prod.fst H).trans hw0
        simpa only [Set.mem_singleton_iff, hv0, ← Prod.zero_eq_mk, map_zero] using hv.symm
      · rintro rfl
        exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
    · intro a
      refine ⟨(E a).1 - (E a).2, (E a).2, ?_⟩
      apply E.injective
      simp only [map_add, LinearEquiv.apply_symm_apply, Prod.mk_add_mk, zero_add,
        sub_add_cancel, Prod.eta]
    · intro U xU hU hF
      let y := x (IsLocalRing.closedPoint k)
      let z := productPoint s x
      have : Smooth (U.ι ≫ s) := hU
      have : IsRegular U.toScheme := IsRegular.of_smooth (U.ι ≫ s)
      have hR : IsRegularLocalRing (X.presheaf.stalk y) :=
        regular_at_open U.ι y ⟨⟨y, xU⟩, rfl⟩
      let := hR
      let d := Module.finrank k (schemeTangentSpace k X s y)
      have hdR : ringKrullDim (X.presheaf.stalk y) = d :=
        rational_tangent_dimension k X s y hr
      refine ⟨d, hdR, rfl, ?_⟩
      obtain ⟨W, V, hWV, hVU, xW, hW, hV, hWh, hsm, hW', hhW, gW, dW,
        hgf, hgs, hdf, hds, hgc, hdc, m, hmf, hms, hm, hzm⟩ :=
        graph_chart k X s h hs x xs hx U xU
      refine ⟨W, V, hWV, hVU, xW, hW, hV, hWh, hsm, hW', hhW,
        gW, dW, hgf, hgs, hdf, hds, hgc, hdc, m, hmf, hms, hm, hzm, ?_⟩
      have : Smooth (pullback.fst (W.ι ≫ s) (V.ι ≫ s) ≫ W.ι ≫ s) := hsm
      have : IsRegular (pullback (W.ι ≫ s) (V.ι ≫ s)) :=
        IsRegular.of_smooth (pullback.fst (W.ι ≫ s) (V.ι ≫ s) ≫ W.ι ≫ s)
      have : IsOpenImmersion m := hm
      have hA : IsRegularLocalRing ((pullback s s).presheaf.stalk z) :=
        regular_at_open m z hzm
      let := hA
      have hpr : pullback.lift x x rfl ≫ (pullback.fst s s ≫ s) = 𝟙 _ := by
        simp only [← Category.assoc, pullback.lift_fst, xs]
      have hrZ := rational_residueStructure k (pullback s s) (pullback.fst s s ≫ s)
        (pullback.lift x x rfl) hpr
      let α := stalkMapAt (graph s h hs) y z hg
      let β := stalkMapAt (pullback.diagonal s) y z hd
      have hα : Function.Surjective α := stalkMapAt_section_surjective
        (graph s h hs) (pullback.fst s s) (pullback.lift_fst ..) y z hg
      have hβ : Function.Surjective β := stalkMapAt_section_surjective
        (pullback.diagonal s) (pullback.fst s s) (pullback.diagonal_fst s) y z hd
      let I := RingHom.ker α
      let J := RingHom.ker β
      let eI := α.quotientKerEquivOfSurjective hα
      let eJ := β.quotientKerEquivOfSurjective hβ
      have hRI : IsRegularLocalRing (((pullback s s).presheaf.stalk z) ⧸ I) :=
        IsRegularLocalRing.of_ringEquiv eI.symm
      have hRJ : IsRegularLocalRing (((pullback s s).presheaf.stalk z) ⧸ J) :=
        IsRegularLocalRing.of_ringEquiv eJ.symm
      let := hRI
      let := hRJ
      refine ⟨I, J, rfl, rfl, hA, hRI, hRJ, hrZ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact quotient_residue_bijective
          (stalkStructure k (pullback s s) (pullback.fst s s ≫ s) z)
          (stalkStructure k X s y) α hα
          (stalkStructure_natural k X (pullback s s) s (pullback.fst s s ≫ s)
            (graph s h hs) (by simp [graph, ← Category.assoc]) y z hg) hr
      · exact quotient_residue_bijective
          (stalkStructure k (pullback s s) (pullback.fst s s ≫ s) z)
          (stalkStructure k X s y) β hβ
          (stalkStructure_natural k X (pullback s s) s (pullback.fst s s ≫ s)
            (pullback.diagonal s) (by simp [← Category.assoc]) y z hd) hr
      · rw [rational_tangent_dimension k (pullback s s) (pullback.fst s s ≫ s) z hrZ,
          E.finrank_eq]
        simp only [Module.finrank, rank_prod', ← two_mul, Cardinal.toNat_mul]
        simp [d, y, Module.finrank]
      · exact (ringKrullDim_eq_of_ringEquiv eI).trans hdR
      · exact (ringKrullDim_eq_of_ringEquiv eJ).trans hdR
      · let w := fixedPoint s h hs x hx
        have hwx : pullback.fst (graph s h hs) (pullback.diagonal s) w = y := by
          change (fixedLift s h hs x hx ≫ pullback.fst _ _) _ = y
          simp only [fixedLift, pullback.lift_fst]
          rfl
        have hwy : pullback.snd (graph s h hs) (pullback.diagonal s) w = y := by
          change (fixedLift s h hs x hx ≫ pullback.snd _ _) _ = y
          simp only [fixedLift, pullback.lift_snd]
          rfl
        have hwz : (pullback.fst (graph s h hs) (pullback.diagonal s) ≫
            graph s h hs) w = z := by
          rw [Scheme.Hom.comp_apply, hwx]; exact hg
        obtain ⟨eF, heF⟩ := stalk_pullback_quotient (graph s h hs) (pullback.diagonal s)
          w y y z hwx hwy hg hd hα hβ hwz
        let b := stalkStructure k (fixedScheme s h hs) (fixedStructure s h hs) w
        let eB := RingEquiv.ofBijective b hF
        let eK := eF.trans eB.symm
        have hK : I ⊔ J = IsLocalRing.maximalIdeal ((pullback s s).presheaf.stalk z) := by
          have hk : RingHom.ker (eK.toRingHom.comp (Ideal.Quotient.mk (I ⊔ J))) = I ⊔ J := by
            ext c
            change eK (Ideal.Quotient.mk (I ⊔ J) c) = 0 ↔ c ∈ I ⊔ J
            rw [← eK.map_zero, eK.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
          rw [← hk]
          exact IsLocalRing.ker_eq_maximalIdeal _
            (eK.surjective.comp Ideal.Quotient.mk_surjective)
        refine ⟨hK, eI, eJ, fun _ ↦ rfl, fun _ ↦ rfl, hwz, eF, eK, heF, ?_⟩
        intro c
        change eB.symm (eF (eF.symm (b c))) = c
        rw [eF.apply_symm_apply]
        exact eB.symm_apply_apply c

end AlgebraicGeometry
