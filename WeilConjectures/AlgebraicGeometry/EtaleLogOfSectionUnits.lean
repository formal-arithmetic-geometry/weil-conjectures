/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Passing the sectionwise log unit condition to geometric stalks

Source: ILO VI 1.1, printed p. 69; the final stalk argument in Step 5 of
lem-trf-prelog-pushout-log-axiom.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem filtered_unit_lift {I : Type v} [Category.{w} I] [IsFiltered I]
    (D : I ⥤ CommMonCat.{u}) (c : Cocone D)
    (hc : IsColimit ((forget CommMonCat).mapCocone c)) (i : I) (x : D.obj i)
    (hx : IsUnit (c.ι.app i x)) : ∃ (j : I) (f : i ⟶ j), IsUnit (D.map f x) := by
  classical
  obtain ⟨b, hb⟩ := hx
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc b.inv
  change c.ι.app j y = b.inv at hy
  let k := IsFiltered.max i j
  let f : i ⟶ k := IsFiltered.leftToMax i j
  let g : j ⟶ k := IsFiltered.rightToMax i j
  let x' := D.map f x
  let y' := D.map g y
  have hh : c.ι.app k (x' * y') = c.ι.app k 1 := by
    change c.ι.app k (D.map f x * D.map g y) = c.ι.app k 1
    rw [map_mul, map_one, c.w_apply f, c.w_apply g, ← hb, hy]
    exact b.val_inv
  obtain ⟨l, h, hl⟩ := Types.FilteredColimit.isColimit_eq_iff' hc (x' * y') 1 |>.mp hh
  change D.map h (x' * y') = D.map h 1 at hl
  refine ⟨l, f ≫ h, isUnit_iff_exists_inv.mpr ⟨D.map h y', ?_⟩⟩
  simpa only [Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply,
    map_mul, map_one, x'] using hl

private theorem filtered_log_condition {I : Type v} [Category.{w} I] [IsFiltered I]
    (D E : I ⥤ CommMonCat.{u}) (d : Cocone D) (e : Cocone E)
    (hd : IsColimit ((forget CommMonCat).mapCocone d))
    (he : IsColimit ((forget CommMonCat).mapCocone e)) (γ : D ⟶ E)
    (f : d.pt →* e.pt) (hf : ∀ (i : I) (x : D.obj i),
      f (d.ι.app i x) = e.ι.app i (γ.app i x))
    (hr : ∀ (i : I) (x : D.obj i), IsUnit (γ.app i x) → IsUnit x)
    (hb : ∀ i : I, Function.Bijective (Units.map (γ.app i).hom)) :
    (∀ x : d.pt, IsUnit (f x) → IsUnit x) ∧ Function.Bijective (Units.map f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, s, rfl⟩ := Types.jointly_surjective_of_isColimit hd x
    change IsUnit (f (d.ι.app i s)) at hx
    change IsUnit (d.ι.app i s)
    rw [hf] at hx
    obtain ⟨j, g, hg⟩ := filtered_unit_lift E e he i (γ.app i s) hx
    have hs : IsUnit (γ.app j (D.map g s)) := by
      rw [γ.naturality_apply g s]
      exact hg
    have hu := (hr j (D.map g s) hs).map (d.ι.app j).hom
    rwa [d.w_apply] at hu
  · intro a b hab
    obtain ⟨i, x, y, hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hd a.val b.val
    change d.ι.app i x = a.val at hx
    change d.ι.app i y = b.val at hy
    have hxu : IsUnit (d.ι.app i x) := hx.symm ▸ a.isUnit
    have hyu : IsUnit (d.ι.app i y) := hy.symm ▸ b.isUnit
    obtain ⟨j, g, hg⟩ := filtered_unit_lift D d hd i x hxu
    obtain ⟨k, h, hh⟩ := filtered_unit_lift D d hd i y hyu
    let l := IsFiltered.max j k
    let p : j ⟶ l := IsFiltered.leftToMax j k
    let q : k ⟶ l := IsFiltered.rightToMax j k
    let x' := D.map p (D.map g x)
    let y' := D.map q (D.map h y)
    have hxx : d.ι.app l x' = a.val := by
      dsimp [x']
      exact (d.w_apply p (D.map g x)).trans ((d.w_apply g x).trans hx)
    have hyy : d.ι.app l y' = b.val := by
      dsimp [y']
      exact (d.w_apply q (D.map h y)).trans ((d.w_apply h y).trans hy)
    have hxy : e.ι.app l (γ.app l x') = e.ι.app l (γ.app l y') := by
      rw [← hf, ← hf, hxx, hyy]
      exact congrArg Units.val hab
    obtain ⟨m, r, hm⟩ :=
      Types.FilteredColimit.isColimit_eq_iff' he (γ.app l x') (γ.app l y') |>.mp hxy
    change E.map r (γ.app l x') = E.map r (γ.app l y') at hm
    have hxm : IsUnit (D.map r x') := ((hg.map (D.map p).hom).map (D.map r).hom)
    have hym : IsUnit (D.map r y') := ((hh.map (D.map q).hom).map (D.map r).hom)
    have huv : Units.map (γ.app m).hom hxm.unit = Units.map (γ.app m).hom hym.unit := by
      apply Units.ext
      simpa only [Units.coe_map, IsUnit.unit_spec, γ.naturality_apply] using hm
    have hv := congrArg Units.val ((hb m).injective huv)
    have hv' : D.map r x' = D.map r y' := by simpa only [IsUnit.unit_spec] using hv
    apply Units.ext
    rw [← hxx, ← hyy, ← d.w_apply r x', ← d.w_apply r y', hv']
  · intro b
    obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit he b.val
    change e.ι.app i x = b.val at hx
    obtain ⟨j, g, hg⟩ := filtered_unit_lift E e he i x (hx.symm ▸ b.isUnit)
    obtain ⟨a, ha⟩ := (hb j).surjective hg.unit
    refine ⟨Units.map (d.ι.app j).hom a, ?_⟩
    apply Units.ext
    change f (d.ι.app j a.val) = b.val
    rw [hf]
    have hav := congrArg Units.val ha
    change γ.app j a.val = hg.unit.val at hav
    rw [hg.unit_spec] at hav
    rw [hav, e.w_apply, hx]

/-- A prelog sheaf satisfying the log unit condition on sections satisfies the
geometric-stalk definition of a log structure.
Source: ILO VI 1.1, printed p. 69; the stalk passage in Step 5 of the associated-log
calculation (blueprint: lem-trf-etale-log-of-section-units).

Proof in words: use the filtered category of pointed étale neighbourhoods of each
geometric point. Both the ring stalk and the monoid stalk are the colimits of their
section diagrams, and the forgetful functors preserve these filtered colimits.
Every monoid germ is represented by a section. If its structural image is a unit,
represent an inverse ring germ on a common neighbourhood. The inverse equations
hold after a further refinement, by the elementwise equality criterion for filtered
colimits. Thus the structural image of the restricted monoid section is a unit.
The sectionwise reflection hypothesis makes the section a monoid unit, whose germ
is the original germ. This proves reflection of units on stalks.
For surjectivity on unit groups, represent a ring unit and its inverse on a common
neighbourhood and refine until both inverse equations hold. Sectionwise surjectivity
of the units map gives a monoid unit lifting that ring unit; taking germs gives the
required preimage. For injectivity, represent each of two monoid units and their
inverses on a common neighbourhood, refining until their inverse equations hold.
If their structural germs agree, refine again until their structural section values
agree. Sectionwise injectivity on unit groups makes the two monoid units equal
there, so their germs agree. Equality of units is equality of their values. These
properties supply exactly the two extra fields of EtaleLogStructure, with the
original prelog sheaf and structural map unchanged. No finiteness, integrality,
nonempty scheme, or cancellation hypothesis is used.
-/
theorem etale_log_of_section_units {X : Scheme.{u}} (M : EtalePrelogStructure X)
    (hreflect : ∀ (V : X.Etaleᵒᵖ) (s : M.monoidSheaf.obj.obj V),
      IsUnit (M.alpha.app V s) → IsUnit s)
    (hbij : ∀ V : X.Etaleᵒᵖ, Function.Bijective (Units.map (M.alpha.app V).hom)) :
    ∃ Λ : EtaleLogStructure X, Λ.toEtalePrelogStructure = M := by
  have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
      (∀ x : M.stalk t, IsUnit (M.stalkAlpha t x) → IsUnit x) ∧
        Function.Bijective (Units.map (M.stalkAlpha t)) := by
    let D := pointedEtaleStalkDiagram M.monoidSheaf t
    let B := (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙
      X.etaleStructurePresheaf
    let E := B ⋙ forget₂ CommRingCat CommMonCat
    let d := colimit.cocone D
    let e := (forget₂ CommRingCat CommMonCat).mapCocone
      ((Scheme.pointSmallEtale t).presheafFiberCocone X.etaleStructurePresheaf)
    have hd : IsColimit ((forget CommMonCat).mapCocone d) :=
      isColimitOfPreserves (forget CommMonCat) (colimit.isColimit D)
    have he : IsColimit ((forget CommMonCat).mapCocone e) :=
      isColimitOfPreserves (forget CommRingCat)
        ((Scheme.pointSmallEtale t).isColimitPresheafFiberCocone X.etaleStructurePresheaf)
    let γ : D ⟶ E := Functor.whiskerLeft
      (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op M.alpha
    apply filtered_log_condition D E d e hd he γ (M.stalkAlpha t)
    · intro i x
      dsimp [EtalePrelogStructure.stalkAlpha]
      change ((colimit.desc D _).hom) ((colimit.ι D i).hom x) = _
      rw [← CommMonCat.comp_apply, colimit.ι_desc]
      rfl
    · intro i x
      exact hreflect (op i.unop.1) x
    · intro i
      exact hbij (op i.unop.1)
  exact ⟨{ toEtalePrelogStructure := M
           reflectsUnits := fun Ω _ _ t ↦ (hstalk Ω t).1
           unitsBijective := fun Ω _ _ t ↦ (hstalk Ω t).2 }, rfl⟩

end AlgebraicGeometry
