/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.JacobsonSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The fibre stalk of an affine principal hypersurface

Source: Stacks Project, Tags 01JU, 0HA1 and 00CT; More on Morphisms,
Tag 0570, `lemma-slice-CM`, positive-dimensional induction step.
(blueprint: lem-trf-principal-hypersurface-fibre-stalk).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private lemma spec_stalkCongr {X : Scheme.{u}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.fromSpecStalk x =
      X.fromSpecStalk y := by
  subst y
  simp

private lemma spec_pointedStalkMap {X Z : Scheme.{u}} (f : Z ⟶ X)
    (z : Z) (x : X) (h : f z = x) :
    Spec.map ((X.presheaf.stalkCongr (.of_eq h)).inv ≫ f.stalkMap z) ≫
      X.fromSpecStalk x = Z.fromSpecStalk z ≫ f := by
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (f.stalkMap z) ≫
    Spec.map (X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ _ = _
  rw [spec_stalkCongr h.symm, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The fibre of an affine principal hypersurface has the expected local quotient
at each closed fibre point where its defining germ is in the maximal ideal.
No flatness, regularity, dimension or Noetherian hypothesis is needed.

Source: Stacks Project, Tags 01JU (`lemma-fibre-product-immersion`), 0HA1
(`lemma-local-ring-fibre`) and 00CT (`proposition-localize-quotient`), applied
in Tag 0570 (`lemma-slice-CM`).
(blueprint: lem-trf-principal-hypersurface-fibre-stalk).

Proof: Let F be the original fibre, E the hypersurface fibre and j : E → F
the canonical map. Its composite with F → Y is a composite of preimmersions,
so j is a preimmersion and is surjective on stalks. Set A = O(F,y) and Q = A/(b).
Since b is in the maximal ideal, Q is a nonzero local ring. The map from B to A
and then Q kills a, hence factors through B/(a). Its spectrum and the canonical
map Spec(Q) → F give, by the fibre universal property, a map r : Spec(Q) → E
whose composite with j is Spec(Q) → F. The image yD of the closed point maps
to y. Injectivity of j shows that {yD} is the inverse image of {y}, hence closed.
The pointed stalk map v : A → O(E,yD) is surjective. The map B → O(E,yD)
factors through B/(a), so v kills b. Conversely, the local stalk map of r gives
ψ : O(E,yD) → Q with ψv equal to the quotient map, proving ker(v) = (b).
The first isomorphism theorem gives the required ring equivalence. Naturality
of the canonical maps from spectra of stalks identifies the pointed stalk map
from Y with the composite through v; the quotient equivalence therefore has
exactly the asserted compatibility on every original germ. -/
theorem exists_closed_fiber_point_principal_stalk_equiv
    {Y S : Scheme.{u}} (g : Y ⟶ S) (s : S) (y : g.fiber s)
    (hy : y ∈ closedPoints (g.fiber s))
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : g.fiberι s y ∈ U) (a : Γ(Y, U))
    (hb : (g.fiberι s).stalkMap y (Y.presheaf.germ U (g.fiberι s y) hx a) ∈
      IsLocalRing.maximalIdeal ((g.fiber s).presheaf.stalk y)) :
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
      hU.fromSpec
    let b := (g.fiberι s).stalkMap y (Y.presheaf.germ U (g.fiberι s y) hx a)
    ∃ (yD : (i ≫ g).fiber s)
      (hyD : ((i ≫ g).fiberι s ≫ i) yD = g.fiberι s y),
      yD ∈ closedPoints ((i ≫ g).fiber s) ∧
      ∃ e : ((i ≫ g).fiber s).presheaf.stalk yD ≃+*
          ((g.fiber s).presheaf.stalk y ⧸ Ideal.span {b}),
        ∀ r : Y.presheaf.stalk (g.fiberι s y),
          e (((i ≫ g).fiberι s ≫ i).stalkMap yD
            ((Y.presheaf.stalkCongr (.of_eq hyD)).inv r)) =
            Ideal.Quotient.mk (Ideal.span {b}) ((g.fiberι s).stalkMap y r) := by
  classical
  let F := g.fiber s
  let A := F.presheaf.stalk y
  let x := g.fiberι s y
  let b : A := (g.fiberι s).stalkMap y (Y.presheaf.germ U x hx a)
  let D := Spec (.of (Γ(Y, U) ⧸ Ideal.span {a}))
  let m : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ Ideal.span {a}) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))
  let i : D ⟶ Y := Spec.map m ≫ hU.fromSpec
  let E := (i ≫ g).fiber s
  let j : E ⟶ F := pullback.lift ((i ≫ g).fiberι s ≫ i)
    ((i ≫ g).fiberToSpecResidueField s) (by simp [Scheme.Hom.fiber_fac])
  have hj : j ≫ g.fiberι s = (i ≫ g).fiberι s ≫ i := pullback.lift_fst ..
  have : IsClosedImmersion (Spec.map m) :=
    IsClosedImmersion.spec_of_surjective m Ideal.Quotient.mk_surjective
  have : IsPreimmersion i := inferInstance
  have : IsPreimmersion (j ≫ g.fiberι s) := hj.symm ▸ inferInstance
  have : IsPreimmersion j := IsPreimmersion.of_comp j (g.fiberι s)
  let Q := CommRingCat.of (A ⧸ Ideal.span {b})
  have hproper : Ideal.span {b} ≠ ⊤ := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.span_le.mpr (by
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact hb))
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
  let q : F.presheaf.stalk y ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let k : Γ(Y, U) ⟶ F.presheaf.stalk y :=
    Y.presheaf.germ U x hx ≫ (g.fiberι s).stalkMap y
  let φ : CommRingCat.of (Γ(Y, U) ⧸ Ideal.span {a}) ⟶ Q :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ (q.hom.comp k.hom) (by
      change Ideal.span {a} ≤ RingHom.ker (q.hom.comp k.hom)
      rw [Ideal.span_le]
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      change Ideal.Quotient.mk (Ideal.span {b}) b = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))))
  have hφ : m ≫ φ = k ≫ q := rfl
  let p : Spec Q ⟶ F := Spec.map q ≫ F.fromSpecStalk y
  have hl : Spec.map φ ≫ i = p ≫ g.fiberι s := by
    dsimp only [i]
    rw [← Spec.map_comp_assoc, hφ]
    dsimp only [k, p]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
    change Spec.map q ≫ Spec.map ((g.fiberι s).stalkMap y) ≫
      hU.fromSpecStalk hx = _
    rw [hU.fromSpecStalk_eq_fromSpecStalk hx,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm
  let r : Spec Q ⟶ E := pullback.lift (Spec.map φ) (p ≫ g.fiberToSpecResidueField s)
    (by
      rw [← Category.assoc, hl, Category.assoc, g.fiber_fac]
      exact (Category.assoc _ _ _).symm)
  have hrj : r ≫ j = p := by
    apply (cancel_mono (g.fiberι s)).mp
    rw [Category.assoc, hj, ← Category.assoc]
    change (pullback.lift _ _ _ ≫ pullback.fst _ _) ≫ i = _
    rw [pullback.lift_fst, hl]
  let yD := r (IsLocalRing.closedPoint Q)
  have hyj : j yD = y := by
    change (r ≫ j) (IsLocalRing.closedPoint Q) = y
    rw [hrj]
    simp [p]
  have hyD : ((i ≫ g).fiberι s ≫ i) yD = x := by
    rw [← hj, Scheme.Hom.comp_apply, hyj]
  have hyDc : yD ∈ closedPoints E := by
    have hpre : j ⁻¹' {y} = {yD} := by
      rw [← hyj]
      simpa only [Set.image_singleton] using
        Set.preimage_image_eq {yD} j.isEmbedding.injective
    change IsClosed {yD}
    rw [← hpre]
    exact hy.preimage j.continuous
  let v : F.presheaf.stalk y ⟶ E.presheaf.stalk yD :=
    (F.presheaf.stalkCongr (.of_eq hyj)).inv ≫ j.stalkMap yD
  have hv : Spec.map v ≫ F.fromSpecStalk y = E.fromSpecStalk yD ≫ j :=
    spec_pointedStalkMap j yD y hyj
  let c : CommRingCat.of (Γ(Y, U) ⧸ Ideal.span {a}) ⟶ E.presheaf.stalk yD :=
    Spec.preimage (E.fromSpecStalk yD ≫ (i ≫ g).fiberι s)
  have hkv : k ≫ v = m ≫ c := by
    apply Spec.map_injective
    apply (cancel_mono hU.fromSpec).mp
    calc
      Spec.map (k ≫ v) ≫ hU.fromSpec =
          Spec.map v ≫ (Spec.map k ≫ hU.fromSpec) := by
        rw [Spec.map_comp, Category.assoc]
      _ = Spec.map v ≫ (F.fromSpecStalk y ≫ g.fiberι s) := by
        congr 1
        dsimp only [k]
        rw [Spec.map_comp, Category.assoc]
        change Spec.map ((g.fiberι s).stalkMap y) ≫ hU.fromSpecStalk hx = _
        rw [hU.fromSpecStalk_eq_fromSpecStalk hx,
          Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = E.fromSpecStalk yD ≫ j ≫ g.fiberι s := by
        rw [← Category.assoc, hv, Category.assoc]
      _ = (E.fromSpecStalk yD ≫ (i ≫ g).fiberι s) ≫ i := by
        exact (congrArg (fun t : E ⟶ Y ↦ E.fromSpecStalk yD ≫ t) hj).trans
          (Category.assoc _ _ _).symm
      _ = Spec.map (m ≫ c) ≫ hU.fromSpec := by
        conv_rhs => rw [Spec.map_comp, Category.assoc]
        change _ = Spec.map (Spec.preimage _) ≫ i
        rw [Spec.map_preimage]
  have hkill : v b = 0 := by
    have hh := congrArg (fun f : Γ(Y, U) ⟶ E.presheaf.stalk yD ↦ f a) hkv
    change v b = c (Ideal.Quotient.mk _ a) at hh
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero] at hh
    exact hh
  let ψ : E.presheaf.stalk yD ⟶ Q := Scheme.stalkClosedPointTo r
  have hψ : Spec.map ψ ≫ E.fromSpecStalk yD = r :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk r
  have hvψ : v ≫ ψ = q := by
    apply Spec.map_injective
    apply (cancel_mono (F.fromSpecStalk y)).mp
    rw [Spec.map_comp, Category.assoc, hv, ← Category.assoc, hψ, hrj]
  have hs : Function.Surjective v :=
    (j.stalkMap_surjective yD).comp
      (ConcreteCategory.bijective_of_isIso (F.presheaf.stalkCongr (.of_eq hyj)).inv).2
  have hker : RingHom.ker v.hom = Ideal.span {b} := by
    apply le_antisymm
    · intro z hz
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q z = 0
      rw [← hvψ, CommRingCat.comp_apply, RingHom.mem_ker.mp hz, map_zero]
    · rw [Ideal.span_le]
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact hkill
  let e : E.presheaf.stalk yD ≃+* (A ⧸ Ideal.span {b}) :=
    ((Ideal.quotEquivOfEq hker.symm).trans
      (v.hom.quotientKerEquivOfSurjective hs)).symm
  let w : Y.presheaf.stalk x ⟶ E.presheaf.stalk yD :=
    (Y.presheaf.stalkCongr (.of_eq hyD)).inv ≫
      ((i ≫ g).fiberι s ≫ i).stalkMap yD
  have hw : w = (g.fiberι s).stalkMap y ≫ v := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk x)).mp
    calc
      Spec.map w ≫ Y.fromSpecStalk x =
          E.fromSpecStalk yD ≫ ((i ≫ g).fiberι s ≫ i) :=
        spec_pointedStalkMap ((i ≫ g).fiberι s ≫ i) yD x hyD
      _ = (E.fromSpecStalk yD ≫ j) ≫ g.fiberι s := by
        exact (congrArg (fun t : E ⟶ Y ↦ E.fromSpecStalk yD ≫ t) hj).symm.trans
          (Category.assoc _ _ _).symm
      _ = (Spec.map v ≫ F.fromSpecStalk y) ≫ g.fiberι s := by rw [hv]
      _ = Spec.map v ≫ Spec.map ((g.fiberι s).stalkMap y) ≫ Y.fromSpecStalk x := by
        rw [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = Spec.map ((g.fiberι s).stalkMap y ≫ v) ≫ Y.fromSpecStalk x := by
        conv_rhs => rw [Spec.map_comp, Category.assoc]
  refine ⟨yD, hyD, hyDc, e, ?_⟩
  intro z
  change e (w z) = _
  rw [hw, CommRingCat.comp_apply]
  change e (e.symm (Ideal.Quotient.mk _ ((g.fiberι s).stalkMap y z))) = _
  exact e.apply_symm_apply _

end AlgebraicGeometry
