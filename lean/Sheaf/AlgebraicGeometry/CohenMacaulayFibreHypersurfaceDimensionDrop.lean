/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.AlgebraicGeometry.Morphisms.FibreRegularElementFlatHypersurface
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import Sheaf.AlgebraicGeometry.PrincipalHypersurfaceFibreStalk

/-! # A flat hypersurface lowers Cohen–Macaulay fibre local dimension by one

Source: Stacks Project, More on Morphisms, Tag 0570, `lemma-slice-CM`,
positive-dimensional reduction; Tags 056Z and 056Y; Algebra, Tag 02JN.
(blueprint: lem-trf-cm-fibre-hypersurface-dimension-drop).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem exists_regular_of_depth_pos (A : Type u) [CommRing A] [IsLocalRing A]
    (hp : 0 < IsLocalRing.depth (R := A) A) :
    ∃ b : A, b ∈ IsLocalRing.maximalIdeal A ∧
      Function.Injective (fun z : A ↦ b * z) := by
  classical
  have hm : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A A))).symm
  simp only [IsLocalRing.depth, Ideal.depth, if_neg hm] at hp
  obtain ⟨n, ⟨rs, hrs, hmem, rfl⟩, hn⟩ := lt_sSup_iff.mp hp
  cases rs with
  | nil => simp at hn
  | cons b bs =>
    exact ⟨b, hmem b (by simp),
      (RingTheory.Sequence.isWeaklyRegular_cons_iff A b bs).mp hrs.1 |>.1⟩

private theorem depth_ge_of_regular_length (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (rs : List A)
    (hrs : RingTheory.Sequence.IsRegular A rs)
    (hmem : ∀ a ∈ rs, a ∈ IsLocalRing.maximalIdeal A) :
    (rs.length : ℕ∞) ≤ IsLocalRing.depth (R := B) B := by
  classical
  unfold IsLocalRing.depth Ideal.depth
  split_ifs with hm
  · exact le_top
  · apply le_sSup
    refine ⟨rs.map e, ?_, ?_, by simp⟩
    · apply (e.toAddEquiv.isRegular_congr ?_).mp hrs
      exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
        (fun a _ z ↦ e.map_mul a z))
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
      exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem hypersurface_of_regular_fiber_germ
    {Y S : Scheme.{u}} (g : Y ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (s : S) (y : g.fiber s) (h : Y.presheaf.stalk (g.fiberι s y))
    (hh : h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.fiberι s y)))
    (hr : Function.Injective
      (fun z : (g.fiber s).presheaf.stalk y ↦ (g.fiberι s).stalkMap y h * z)) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hx : g.fiberι s y ∈ U) (a : Γ(Y, U)),
      Y.presheaf.germ U (g.fiberι s y) hx a = h ∧
      Flat ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
        hU.fromSpec) ≫ g) ∧
      LocallyOfFinitePresentation
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
          hU.fromSpec) ≫ g) := by
  classical
  let x := g.fiberι s y
  have hx : g.fiberι s y = x := rfl
  clear_value x
  have hs : g x = s := hx ▸ (g.fiberHomeo s y).property
  subst s
  have hy : y = g.asFiber x :=
    (g.fiberι (g x)).isEmbedding.injective (hx.trans (g.fiberι_asFiber x).symm)
  subst y
  let e := Y.presheaf.stalkCongr (.of_eq hx)
  have hh' : e.hom h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv]
    exact Ideal.mem_map_of_mem _ hh
  have hr' : Function.Injective
      (fun z : (g.fiber (g x)).presheaf.stalk (g.asFiber x) ↦
        (g.fiberStalkMap x).hom (e.hom h) * z) := by
    simpa only [Scheme.Hom.fiberStalkMap, e, CommRingCat.comp_apply,
      CommRingCat.inv_hom_apply] using hr
  obtain ⟨U, hU, hxU, a, ha, _, hflat, hfp⟩ :=
    exists_affine_flat_hypersurface_of_fiber_regular g x (Flat.stalkMap g x)
      (e.hom h) hh' hr'
  refine ⟨U, hU, hx.symm ▸ hxU, a, ?_, by simpa only [Category.assoc] using hflat,
    by simpa only [Category.assoc] using hfp⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [← ha]
  have he := congrArg (fun f : Γ(Y, U) ⟶ Y.presheaf.stalk x ↦ f a)
    (Y.presheaf.germ_stalkSpecializes (hx.symm ▸ hxU) (Inseparable.of_eq hx).ge)
  simpa only [e, TopCat.Presheaf.stalkCongr_hom, CommRingCat.comp_apply] using he

/-- A positive-dimensional closed Cohen–Macaulay fibre point of a flat morphism
locally of finite presentation admits an affine principal hypersurface through it,
flat and locally of finite presentation over the base. Its fibre local ring is the
quotient by the chosen regular germ, compatibly with the original local-ring maps,
and is Noetherian with dimension and depth lowered by one.

Source: Stacks Project, More on Morphisms, Tag 0570, `lemma-slice-CM`,
positive-dimensional reduction; Tags 056Z, 056Y and 02JN.
(blueprint: lem-trf-cm-fibre-hypersurface-dimension-drop).

Proof plan, following the five steps of the DAG node:
1. The fibre-stalk quotient theorem `lem-sbc-scheme-fibre-stalk-quotient` makes the
map from the total-space stalk onto the fibre stalk surjective. Since the latter
is a nonzero local ring, its maximal ideal times the module A is proper. The definition
`def-weil-pbc-depth` and the positive depth bound supply a regular sequence of
positive length in its maximal ideal. Its first element is a nonzerodivisor by
`def-weil-pbc-regular-sequence`. Lift it through that surjection. The lift belongs
to the total-space maximal ideal, since otherwise its image would be a unit.
2. Apply `lem-trf-fibre-regular-element-flat-hypersurface` to the lift. Global
flatness gives the required flat stalk map. Obtain an affine neighbourhood and a
section with this germ whose principal quotient is flat and locally of finite
presentation over the base.
3. By `lem-pc-closed-subscheme-base-change-ideal-image`, its fibre is the closed
subscheme cut out by the restricted section. The image ideal is principal: sums
of tensors with multiples of the section map to multiples of its restriction,
and the restriction itself is the image of the generator. Its germ belongs to
the fibre maximal ideal, giving the unique point above the given point. This
point is closed because its singleton is the inverse image of the original
closed singleton under the closed immersion into the open fibre neighbourhood.
4. Choose an affine neighbourhood in the original fibre. Use
`lem-weil-pbc-affine-open-stalk-localization` and
`lem-weil-pbc-localization-at-prime-of-quotient` to identify the new stalk with
the old stalk modulo the regular germ. The extended principal ideal is generated
by the germ. On a fraction b/v from the total-space chart both canonical maps
send it to the fraction of the restricted numerator and denominator, followed
by the quotient. The denominator stays a unit. This proves the compatibility.
5. Apply `lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm`. The regular germ lies
in the maximal ideal, so its quotient is nonzero; the singleton is a regular
sequence including its nonzero-quotient clause. The quotient is Noetherian of
dimension d - 1 and depth at least d - 1. Transport along the displayed ring
equivalence to obtain the same assertions for the new fibre stalk.
-/
theorem exists_affine_flat_hypersurface_of_fiber_depth
    {Y S : Scheme.{u}} (g : Y ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (s : S) (y : g.fiber s) (hy : y ∈ closedPoints (g.fiber s))
    [IsNoetherianRing ((g.fiber s).presheaf.stalk y)]
    (d : ℕ) (hd : ringKrullDim ((g.fiber s).presheaf.stalk y) = (d : WithBot ℕ∞))
    (hdpos : 0 < d)
    (hdepth : (d : ℕ∞) ≤
      IsLocalRing.depth (R := (g.fiber s).presheaf.stalk y)
        ((g.fiber s).presheaf.stalk y)) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hx : g.fiberι s y ∈ U) (a : Γ(Y, U))
      (h : Y.presheaf.stalk (g.fiberι s y)) (hbar : (g.fiber s).presheaf.stalk y)
      (i : Spec (.of (Γ(Y, U) ⧸ Ideal.span {a})) ⟶ Y),
      h = Y.presheaf.germ U (g.fiberι s y) hx a ∧
      hbar = (g.fiberι s).stalkMap y h ∧
      h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.fiberι s y)) ∧
      hbar ∈ IsLocalRing.maximalIdeal ((g.fiber s).presheaf.stalk y) ∧
      Function.Injective (fun z : (g.fiber s).presheaf.stalk y ↦ hbar * z) ∧
      i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
        hU.fromSpec ∧
      Flat (i ≫ g) ∧ LocallyOfFinitePresentation (i ≫ g) ∧
      ∃ (yD : (i ≫ g).fiber s)
        (hyD : ((i ≫ g).fiberι s ≫ i) yD = g.fiberι s y),
        yD ∈ closedPoints ((i ≫ g).fiber s) ∧
        ∃ e : ((i ≫ g).fiber s).presheaf.stalk yD ≃+*
            ((g.fiber s).presheaf.stalk y ⧸ Ideal.span {hbar}),
          (∀ r : Y.presheaf.stalk (g.fiberι s y),
            e (((i ≫ g).fiberι s ≫ i).stalkMap yD
              ((Y.presheaf.stalkCongr (.of_eq hyD)).inv r)) =
              Ideal.Quotient.mk (Ideal.span {hbar}) ((g.fiberι s).stalkMap y r)) ∧
          IsNoetherianRing (((i ≫ g).fiber s).presheaf.stalk yD) ∧
          ringKrullDim (((i ≫ g).fiber s).presheaf.stalk yD) =
            ((d - 1 : ℕ) : WithBot ℕ∞) ∧
          ((d - 1 : ℕ) : ℕ∞) ≤
            IsLocalRing.depth (R := ((i ≫ g).fiber s).presheaf.stalk yD)
              (((i ≫ g).fiber s).presheaf.stalk yD) := by
  classical
  let A := (g.fiber s).presheaf.stalk y
  obtain ⟨b, hb, hreg⟩ := exists_regular_of_depth_pos A
    (lt_of_lt_of_le (by exact_mod_cast hdpos) hdepth)
  obtain ⟨h, hh⟩ := (g.fiberι s).stalkMap_surjective y b
  have hhm : h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.fiberι s y)) := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have hbu := hu.map ((g.fiberι s).stalkMap y).hom
    rw [hh] at hbu
    exact (IsLocalRing.mem_maximalIdeal b).mp hb hbu
  obtain ⟨U, hU, hx, a, ha, hf, hfp⟩ :=
    hypersurface_of_regular_fiber_germ g s y h hhm (by simpa only [hh] using hreg)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))) ≫
    hU.fromSpec
  have hba : (g.fiberι s).stalkMap y (Y.presheaf.germ U (g.fiberι s y) hx a) = b :=
    (congrArg ((g.fiberι s).stalkMap y) ha).trans hh
  have hgeom := exists_closed_fiber_point_principal_stalk_equiv g s y hy U hU hx a
      (hba.symm ▸ hb)
  dsimp only at hgeom
  rw [hba] at hgeom
  obtain ⟨yD, hyD, hyDc, e, he⟩ := hgeom
  have hnd : b ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro z hz
    exact hreg (hz.trans (mul_zero b).symm)
  obtain ⟨hQ, hN, hdim, _, _hdep, rs, hrs, hmem, hlen⟩ :=
    IsLocalRing.depth_quotient_nonzerodivisor A d hd hdepth b hb hnd
  let := hQ
  have hN' : IsNoetherianRing (((i ≫ g).fiber s).presheaf.stalk yD) :=
    isNoetherianRing_of_ringEquiv (A ⧸ Ideal.span {b}) e.symm
  refine ⟨U, hU, hx, a, h, b, i, ha.symm, hh.symm, hhm, hb, hreg, rfl,
    hf, hfp, yD, hyD, hyDc, e, he, hN', ?_, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv e).trans hdim
  · rw [← hlen]
    exact depth_ge_of_regular_length _ _ e.symm rs hrs hmem

end AlgebraicGeometry
