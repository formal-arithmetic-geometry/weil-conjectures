/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothConnectedCurveLocalRings
public import WeilConjectures.AlgebraicGeometry.InvertibleModuleGenericStalk
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Orders of a rational section of an invertible module

Source: Stacks Project, Divisors, Section 02SE before Definition 02SF and Lemma 02SG
(blueprint: lem-sc-rational-section-order).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem coefficient_order_nonneg
    (C : Scheme.{u}) [IsIntegral C] (L : C.Modules) [L.IsInvertible] (x : C)
    (v : C.functionFieldˣ →* Multiplicative ℤ)
    (hv : ∀ g : C.functionFieldˣ,
      (∃ r : C.presheaf.stalk x, r ≠ 0 ∧
        algebraMap (C.presheaf.stalk x) C.functionField r = (g : C.functionField)) ↔
        0 ≤ Multiplicative.toAdd (v g))
    (e : ↑(TopCat.Presheaf.stalk L.val.presheaf x))
    (he : Submodule.span (C.presheaf.stalk x) {e} = ⊤)
    (g : C.functionFieldˣ)
    (hg : (g : C.functionField) •
      TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec C).specializes (Set.mem_univ x)) e ∈
      Set.range (TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec C).specializes (Set.mem_univ x)))) :
    0 ≤ Multiplicative.toAdd (v g) := by
  obtain ⟨⟨b, hb⟩, hrange⟩ := ((invertible_module_generic_stalk C L).2.2.1 x).2 e he
  rw [hrange] at hg
  obtain ⟨a, ha⟩ := hg
  have hne := b.ne_zero PUnit.unit
  rw [hb] at hne
  have hcoeff : (g : C.functionField) =
      algebraMap (C.presheaf.stalk x) C.functionField a :=
    smul_left_injective C.functionField hne ha
  apply (hv g).mp
  refine ⟨a, ?_, hcoeff.symm⟩
  intro ha0
  apply g.ne_zero
  simpa only [ha0, map_zero] using hcoeff

private theorem span_germ_of_freeGenerator
    {C : Scheme.{u}} (L : C.Modules) {V : C.Opens} {e : Γ(L, V)}
    (he : IsFreeGenerator e) (x : C) (hx : x ∈ V) :
    Submodule.span (C.presheaf.stalk x)
      {TopCat.Presheaf.germ L.val.presheaf V x hx e} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff]
  intro z
  obtain ⟨W, hWV, hxW, z', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq L.val.presheaf z hx
  obtain ⟨a, ha⟩ := (he.map hWV).exists_smul_eq z'
  refine ⟨C.presheaf.germ W x hxW a, ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply L.val.presheaf (homOfLE hWV) x hxW e]
  rw [← PresheafOfModules.germ_smul]
  change TopCat.Presheaf.germ L.val.presheaf W x hxW
    (a • L.presheaf.map (homOfLE hWV).op e) = _
  rw [ha]

set_option maxHeartbeats 800000 in
-- Comparing the section and stalk scalar actions requires extra elaboration heartbeats.
/-- Changing a local generator does not change the order of a nonzero rational section,
and only finitely many closed points have nonzero order.
Source: Stacks Project, Divisors, Section 02SE before Definition 02SF and Lemma 02SG
(blueprint: lem-sc-rational-section-order).

The integral instance and normalized valuations are taken from
`lem-sc-smooth-connected-curve-local-rings`, rather than imposed as extra hypotheses.
`lam` is the specialization map of stalks used in `lem-sc-invertible-module-generic-stalk`.
A generator means that its singleton spans the local stalk. The existential coefficient in
the finite-support set avoids making any choice of local generators; the first clause and
`lem-sc-invertible-module-generic-stalk` make it the same set for every choice.

Proof:
1. For a generator e, the generic-stalk image formula says that a nonzero coefficient
   whose multiple of lam(e) lies in the local stalk image is a nonzero local scalar.
   The valuation characterization in `lem-sc-smooth-connected-curve-local-rings` makes
   its order nonnegative. Apply this to g/g' and g'/g, using the two expressions for s.
   Both differences of orders are nonnegative, so the orders agree.
2. Represent s by a section z on a neighbourhood V of the generic point, and choose a
   local free generator e on a smaller affine neighbourhood W. Write z|W = a • e.
   The germ of a at the generic point is nonzero because s is nonzero. Thus the basic
   open U = D(a) contains the generic point. For each P in U, the germ of a is a unit;
   the germ of e spans the stalk, so the germ of z also spans it. Its generic image is s.
3. Compare any coefficient at a closed point of U with the coefficient 1 for this germ.
   Step 1 makes its order zero. The nonzero-order support is therefore contained in
   C minus U, finite by `lem-sc-nonempty-open-complement-finite-dim-le-one`, using the
   Noetherian and integral conclusions of `lem-sc-smooth-connected-curve-local-rings`
   and the curve dimension bound from `def-sc-curves`. -/
theorem rational_section_order
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) [L.IsInvertible] :
    let hC := Classical.choose (C.smooth_connected_curve_local_rings k f)
    letI := hC
    let h := Classical.choose_spec (C.smooth_connected_curve_local_rings k f)
    let η := genericPoint C
    let lam := fun x : C ↦
      TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec C).specializes (Set.mem_univ x))
    let v := fun P : {P : C // P ∈ closedPoints C} ↦
      Classical.choose ((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)
    ∀ (s : ↑(TopCat.Presheaf.stalk L.val.presheaf η)), s ≠ 0 →
      (∀ (P : {P : C // P ∈ closedPoints C})
        (e e' : ↑(TopCat.Presheaf.stalk L.val.presheaf P.val)),
        Submodule.span (C.presheaf.stalk P.val) {e} = ⊤ →
        Submodule.span (C.presheaf.stalk P.val) {e'} = ⊤ →
        ∀ g g' : C.functionFieldˣ,
          s = (g : C.functionField) • lam P.val e →
          s = (g' : C.functionField) • lam P.val e' →
          Multiplicative.toAdd (v P g) = Multiplicative.toAdd (v P g')) ∧
      Set.Finite {P : C | ∃ hP : P ∈ closedPoints C,
        ∃ e : ↑(TopCat.Presheaf.stalk L.val.presheaf P),
          Submodule.span (C.presheaf.stalk P) {e} = ⊤ ∧
          ∃ g : C.functionFieldˣ,
            s = (g : C.functionField) • lam P e ∧
              Multiplicative.toAdd (v ⟨P, hP⟩ g) ≠ 0} := by
  classical
  let hC := Classical.choose (C.smooth_connected_curve_local_rings k f)
  let := hC
  let h := Classical.choose_spec (C.smooth_connected_curve_local_rings k f)
  let : IsNoetherian C := h.1
  let η := genericPoint C
  let lam := fun x : C ↦ TopCat.Presheaf.stalkSpecializes L.val.presheaf
    ((genericPoint_spec C).specializes (Set.mem_univ x))
  let v := fun P : closedPoints C ↦
    Classical.choose ((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)
  change ∀ s, s ≠ 0 → _
  intro s hs
  have hind (P : closedPoints C)
      (e e' : ↑(TopCat.Presheaf.stalk L.val.presheaf P.val))
      (he : Submodule.span (C.presheaf.stalk P.val) {e} = ⊤)
      (he' : Submodule.span (C.presheaf.stalk P.val) {e'} = ⊤)
      (g g' : C.functionFieldˣ)
      (hg : s = (g : C.functionField) • lam P.val e)
      (hg' : s = (g' : C.functionField) • lam P.val e') :
      Multiplicative.toAdd (v P g) = Multiplicative.toAdd (v P g') := by
    have hv := (Classical.choose_spec
      ((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)).2.2
    have hratio (a b : C.functionFieldˣ)
        (ea eb : ↑(TopCat.Presheaf.stalk L.val.presheaf P.val))
        (ha : s = (a : C.functionField) • lam P.val ea)
        (hb : s = (b : C.functionField) • lam P.val eb) :
        ((a / b : C.functionFieldˣ) : C.functionField) • lam P.val ea =
          lam P.val eb := by
      rw [Units.val_div_eq_div_val, div_eq_mul_inv, mul_comm, mul_smul, ← ha, hb,
        ← mul_smul, inv_mul_cancel₀ b.ne_zero, one_smul]
    have hpos := coefficient_order_nonneg C L P.val (v P) hv e he (g / g')
      ⟨e', (hratio g g' e e' hg hg').symm⟩
    have hneg := coefficient_order_nonneg C L P.val (v P) hv e' he' (g' / g)
      ⟨e, (hratio g' g e' e hg' hg).symm⟩
    simp only [map_div, toAdd_div] at hpos hneg
    omega
  refine ⟨hind, ?_⟩
  obtain ⟨V, hηV, z, hz⟩ := TopCat.Presheaf.exists_germ_eq L.val.presheaf s
  have := IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨W, hηW, hWV, e, he⟩ := exists_isFreeGenerator L hηV
  let a := he.coeff (L.presheaf.map (homOfLE hWV).op z)
  let U := C.basicOpen a
  have hηU : η ∈ U := by
    rw [C.mem_basicOpen a η hηW, isUnit_iff_ne_zero]
    intro ha
    have heq := congrArg (TopCat.Presheaf.germ L.val.presheaf W.1 η hηW)
      (he.coeff_smul (L.presheaf.map (homOfLE hWV).op z))
    rw [PresheafOfModules.germ_smul] at heq
    change C.presheaf.germ W.1 η hηW a • _ = _ at heq
    rw [ha, zero_smul] at heq
    have hres := TopCat.Presheaf.germ_res_apply L.val.presheaf
      (homOfLE hWV) η hηW z
    change TopCat.Presheaf.germ L.val.presheaf W.1 η hηW
      (L.presheaf.map (homOfLE hWV).op z) = _ at hres
    exact hs (hz.symm.trans (hres.symm.trans heq.symm))
  have hfinite := U.isOpen.finite_compl_of_topologicalKrullDim_le_one
    (IsCurve.krullDim_le_one (f := f)) ⟨η, hηU⟩
  apply hfinite.subset
  rintro P ⟨hP, ep, hep, g, hg, hnonzero⟩ hPU
  have hPW : P ∈ W.1 := C.basicOpen_le a hPU
  let eP := TopCat.Presheaf.germ L.val.presheaf W.1 P hPW e
  let aP := C.presheaf.germ W.1 P hPW a
  have haP : IsUnit aP := (C.mem_basicOpen a P hPW).mp hPU
  let t := aP • eP
  have ht : Submodule.span (C.presheaf.stalk P) {t} = ⊤ := by
    rw [Submodule.span_singleton_smul_eq haP]
    exact span_germ_of_freeGenerator L he P hPW
  have hst : s = lam P t := by
    have heq := congrArg (TopCat.Presheaf.germ L.val.presheaf W.1 P hPW)
      (he.coeff_smul (L.presheaf.map (homOfLE hWV).op z))
    rw [PresheafOfModules.germ_smul] at heq
    change t = TopCat.Presheaf.germ L.val.presheaf W.1 P hPW
      (L.presheaf.map (homOfLE hWV).op z) at heq
    rw [heq]
    dsimp only [lam]
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    exact (TopCat.Presheaf.germ_res_apply L.val.presheaf
      (homOfLE hWV) η hηW z |>.trans hz).symm
  have hzero := hind ⟨P, hP⟩ ep t hep ht g 1 hg (by simpa using hst)
  exact hnonzero (hzero.trans (by simp))

end AlgebraicGeometry.Scheme.Modules
