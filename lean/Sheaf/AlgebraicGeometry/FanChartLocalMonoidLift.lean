/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison
public import Sheaf.AlgebraicGeometry.AffineFanHomUniversal
public import Sheaf.AlgebraicGeometry.FanChartStalkModel
import Sheaf.AlgebraicGeometry.FanChartGermSpreading
import Sheaf.AlgebraicGeometry.FanChartSectionIsChart
import Sheaf.GroupTheory.IntegralMonoidFreeSharpeningSplitting
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Zariski local monoid lifts of a prescribed characteristic fan chart

Source: ILO, Exposé VI 3.7(a), printed p.75; Exposé VIII 3.1.4(iii),
3.1.8(ii), 3.1.10(ii), printed pp.98--100, and 3.3.12--3.3.13, pp.108--109
(blueprint: lem-trf-fan-chart-local-monoid-lift).

The stalk and its group completion below are ordinary Zariski stalks. The quotient
map is constructed from sectionwise sharpening and the specified fan-chart isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem group_hom_ext {A B : Type u} [CommMonoid A] [CommGroup B]
    {f g : Algebra.GrothendieckGroup A →* B}
    (h : ∀ a, f (Algebra.GrothendieckGroup.of a) = g (Algebra.GrothendieckGroup.of a)) :
    f = g :=
  Algebra.GrothendieckGroup.lift.symm.injective (MonoidHom.ext h)

private theorem group_lift_of {A B : Type u} [CommMonoid A] [CommGroup B]
    (f : A →* B) (a : A) :
    Algebra.GrothendieckGroup.lift f (Algebra.GrothendieckGroup.of a) = f a := by
  exact DFunLike.congr_fun (Algebra.GrothendieckGroup.lift.symm_apply_apply f) a

private noncomputable def group_equiv {A B : Type u} [CommMonoid A] [CommMonoid B]
    (e : A ≃* B) : Algebra.GrothendieckGroup A ≃* Algebra.GrothendieckGroup B := by
  let f := Algebra.GrothendieckGroup.lift
    (Algebra.GrothendieckGroup.of.comp e.toMonoidHom)
  let g := Algebra.GrothendieckGroup.lift
    (Algebra.GrothendieckGroup.of.comp e.symm.toMonoidHom)
  have hgf : g.comp f = MonoidHom.id _ := by
    apply group_hom_ext
    intro a
    change g (f (Algebra.GrothendieckGroup.of a)) = Algebra.GrothendieckGroup.of a
    dsimp only [f, g]
    rw [group_lift_of]
    change Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp e.symm.toMonoidHom)
        (Algebra.GrothendieckGroup.of (e a)) = Algebra.GrothendieckGroup.of a
    rw [group_lift_of]
    exact congrArg Algebra.GrothendieckGroup.of (e.symm_apply_apply a)
  have hfg : f.comp g = MonoidHom.id _ := by
    apply group_hom_ext
    intro b
    change f (g (Algebra.GrothendieckGroup.of b)) = Algebra.GrothendieckGroup.of b
    dsimp only [f, g]
    rw [group_lift_of]
    change Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp e.toMonoidHom)
        (Algebra.GrothendieckGroup.of (e.symm b)) = Algebra.GrothendieckGroup.of b
    rw [group_lift_of]
    exact congrArg Algebra.GrothendieckGroup.of (e.apply_symm_apply b)
  exact
    { toFun := f
      invFun := g
      left_inv := fun a ↦ DFunLike.congr_fun hgf a
      right_inv := fun b ↦ DFunLike.congr_fun hfg b
      map_mul' := f.map_mul }

private theorem group_equiv_of {A B : Type u} [CommMonoid A] [CommMonoid B]
    (e : A ≃* B) (a : A) :
    group_equiv e (Algebra.GrothendieckGroup.of a) =
      Algebra.GrothendieckGroup.of (e a) := by
  exact group_lift_of (Algebra.GrothendieckGroup.of.comp e.toMonoidHom) a

private theorem monoid_sections_of_group_sections
    {R P : Type u} [CommMonoid R] [CommMonoid P]
    (q : R →* P) (e : Associates R ≃* P)
    (he : ∀ r, e (Associates.mk r) = q r)
    (hR : Function.Injective (Algebra.GrothendieckGroup.of (M := R)))
    (hfree : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ
      (Additive (Algebra.GrothendieckGroup P)))) :
    (∃ s : Algebra.GrothendieckGroup P →* Algebra.GrothendieckGroup R,
      Function.RightInverse s
        (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp q))) ∧
    ∀ s : Algebra.GrothendieckGroup P →* Algebra.GrothendieckGroup R,
      Function.RightInverse s
        (Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp q)) →
      ∃ j : P →* R, q.comp j = MonoidHom.id P ∧
        ∀ p, Algebra.GrothendieckGroup.of (j p) = s (Algebra.GrothendieckGroup.of p) := by
  classical
  let E := group_equiv e
  let π := Algebra.GrothendieckGroup.lift
    (Algebra.GrothendieckGroup.of.comp (Associates.mkMonoidHom : R →* Associates R))
  let Q := Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp q)
  have hQ : E.toMonoidHom.comp π = Q := by
    apply group_hom_ext
    intro r
    change group_equiv e (Algebra.GrothendieckGroup.lift
        (Algebra.GrothendieckGroup.of.comp Associates.mkMonoidHom)
          (Algebra.GrothendieckGroup.of r)) =
      Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp q)
        (Algebra.GrothendieckGroup.of r)
    rw [group_lift_of, group_lift_of]
    change group_equiv e (Algebra.GrothendieckGroup.of (Associates.mk r)) = _
    rw [group_equiv_of]
    exact congrArg Algebra.GrothendieckGroup.of (he r)
  obtain ⟨n, ⟨b⟩⟩ := hfree
  have hfree' : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ
      (Additive (Algebra.GrothendieckGroup (Associates R)))) :=
    ⟨n, ⟨b.map E.symm.toAdditive.toIntLinearEquiv⟩⟩
  obtain ⟨hA, _, hker, t, ht, _⟩ :=
    Algebra.integral_monoid_free_sharpening_splitting R hR hfree'
  have hP : Function.Injective (Algebra.GrothendieckGroup.of (M := P)) := by
    intro p p' h
    apply e.symm.injective
    apply hA
    apply E.injective
    change group_equiv e (Algebra.GrothendieckGroup.of (e.symm p)) =
      group_equiv e (Algebra.GrothendieckGroup.of (e.symm p'))
    rw [group_equiv_of, group_equiv_of, e.apply_symm_apply, e.apply_symm_apply]
    exact h
  refine ⟨?_, ?_⟩
  · refine ⟨t.comp E.symm.toMonoidHom, ?_⟩
    intro p
    change Q (t (E.symm p)) = p
    rw [← hQ]
    change E (π (t (E.symm p))) = p
    have hp := DFunLike.congr_fun ht (E.symm p)
    change π (t (E.symm p)) = E.symm p at hp
    rw [hp, E.apply_symm_apply]
  · intro s hs
    have hex : ∀ p : P, ∃ r : R,
        Algebra.GrothendieckGroup.of r = s (Algebra.GrothendieckGroup.of p) := by
      intro p
      obtain ⟨r, hr⟩ := Associates.mk_surjective (e.symm p)
      have hqr : q r = p := by rw [← he, hr, e.apply_symm_apply]
      let g := s (Algebra.GrothendieckGroup.of p) / Algebra.GrothendieckGroup.of r
      have hQg : Q g = 1 := by
        change Q (s (Algebra.GrothendieckGroup.of p) / _) = 1
        rw [map_div, hs]
        change Algebra.GrothendieckGroup.of p /
          Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp q)
            (Algebra.GrothendieckGroup.of r) = 1
        rw [group_lift_of]
        change Algebra.GrothendieckGroup.of p / Algebra.GrothendieckGroup.of (q r) = 1
        rw [hqr, div_self']
      have hπg : π g = 1 := by
        apply E.injective
        have h := DFunLike.congr_fun hQ g
        change E (π g) = Q g at h
        simpa [hQg] using h
      obtain ⟨v, hv⟩ := (hker g).mp hπg
      refine ⟨(v : R) * r, ?_⟩
      rw [map_mul, hv]
      exact div_mul_cancel _ _
    choose j hj using hex
    let J : P →* R :=
      { toFun := j
        map_one' := hR (by rw [hj]; simp)
        map_mul' := fun p p' ↦ hR (by simp only [map_mul, hj]) }
    refine ⟨J, ?_, hj⟩
    ext p
    apply hP
    have h : Q (Algebra.GrothendieckGroup.of (J p)) =
        Algebra.GrothendieckGroup.of p := by
      change Q (Algebra.GrothendieckGroup.of (j p)) = _
      rw [hj, hs]
    exact (group_lift_of (Algebra.GrothendieckGroup.of.comp q) (J p)).symm.trans h

/-- A prescribed fan chart has a Zariski local log-chart lift, realizing every prescribed
section of its ordinary stalk group quotient. The equality at all restricted stalks
states equality of the entire homomorphisms to the characteristic sheaf; the factorization
through the fan open fixes the original continuous map and all its sheaf maps.

Source: ILO VI 3.7(a), p.75; VIII 3.1.4(iii), 3.1.8(ii), 3.1.10(ii), pp.98--100;
3.3.12--3.3.13, pp.108--109 (blueprint: lem-trf-fan-chart-local-monoid-lift).

Proof:
1. By lem-trf-fine-fan-point-localization the generalization open is the normalized
sharp spectrum of the actual fan stalk P. The chart identifies P with the characteristic
stalk. The Zariski/etale comparison lem-trf-zariski-log-stalk-unit-extension and
lem-trf-fs-face-sharpening show that P is sharp fs and its group completion is finite free.
2. By lem-trf-integral-monoid-free-sharpening-splitting the ordinary log stalk L is
integral and L^gp -> P^gp has kernel the ring units and admits a section. For any section
t and p in P, choose l in L representing p. Then t(p)/l is a unit, so t(p) belongs to L.
Thus every group section restricts to a monoid section, without any log-regularity assumption.
3. Choose finitely many generators and the finite relations supplied by
lem-trf-fg-commutative-monoid-finite-presentation. Represent their lifted germs on a common
Zariski neighborhood in the inverse image of the generalization open. Shrink for each
relation and each equality with the prescribed characteristic sections. This yields h
with exactly that germ and sharpening. Empty lists require no shrinking.
4. The associated-log universal property of lem-trf-associated-log-universal-stalks
supplies its canonical map to N. At any geometric point y, let E be the face mapping to
ring units. The localization formulas of lem-trf-affine-fan-localization-sections and
lem-trf-fs-face-sharpening identify both characteristics with (P-E)/E^gp, using
lem-trf-zariski-prelog-logification-comparison and lem-trf-zariski-log-stalk-unit-extension.
The stalk map P plus_E O_y^units -> N_y is surjective because all characteristic classes
are represented by p-e and h(e) is a unit. If h(p)u=h(p')u', then p-p'=e-e', so
p+e'=p'+e; cancellation gives u*h(e)=u'*h(e'). The pushout relations identify the two
representatives. Hence it is bijective at every geometric point.
5. Apply lem-weil-pbc-sets-etale-iso-on-geometric-stalks to obtain the log-chart property.
By lem-trf-affine-fan-hom-universal, equality of canonical-section homomorphisms identifies
the entire sharpened morphism with the prescribed fan chart. The groupification of its
germ is t by construction in steps 2--3. -/
theorem fan_chart_local_monoid_lift
    {X : FineSaturatedLogScheme.{u}} {F : FineFan.Fan.{u}}
    (c : LogFanChart X F) (x : X.scheme) :
    ∃ L : FineFan.PointLocalization F (c.map.hom.base x),
      IsFineSaturatedMonoid (FineFan.stalk F.space.presheaf (c.map.hom.base x)) ∧
      FineFan.IsSharp (FineFan.stalk F.space.presheaf (c.map.hom.base x)) ∧
      (∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ
        (Additive (Algebra.GrothendieckGroup
          (FineFan.stalk F.space.presheaf (c.map.hom.base x)))))) ∧
      (∃ s : Algebra.GrothendieckGroup
          (FineFan.stalk F.space.presheaf (c.map.hom.base x)) →*
          Algebra.GrothendieckGroup (FineFan.stalk X.logStructure.zariskiPresheaf x),
        Function.RightInverse s (c.stalkGroupQuotient x)) ∧
      ∀ s : Algebra.GrothendieckGroup
          (FineFan.stalk F.space.presheaf (c.map.hom.base x)) →*
          Algebra.GrothendieckGroup (FineFan.stalk X.logStructure.zariskiPresheaf x),
        Function.RightInverse s (c.stalkGroupQuotient x) →
        ∃ (U : X.scheme.Opens) (hx : x ∈ U)
          (h : FineFan.stalk F.space.presheaf (c.map.hom.base x) →*
            X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj U)))
          (a : X.logStructure.sharpSpace.restrict U.isOpenEmbedding ⟶
            F.space.restrict L.openSet.isOpenEmbedding),
          (∀ y ∈ U, c.map.hom.base y ∈ L.openSet) ∧
          X.logStructure.IsChart ((logOpenEtale X.scheme).obj U) h ∧
          a ≫ F.space.ofRestrict L.openSet.isOpenEmbedding =
            X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding ≫ c.map ∧
          (∀ (p : FineFan.stalk F.space.presheaf (c.map.hom.base x))
            (y : X.scheme) (hy : y ∈ U),
            FineFan.stalkMap (X.logStructure.sharpSpace.ofRestrict U.isOpenEmbedding)
                ⟨y, hy⟩ (FineFan.germ X.logStructure.sharpSpace.presheaf U y hy
                  (X.logStructure.sharpSection U (h p))) =
              FineFan.germ (X.logStructure.sharpSpace.restrict U.isOpenEmbedding).presheaf
                ⊤ ⟨y, hy⟩ (by trivial) (FineFan.affinePullback (a ≫ L.iso.hom) p)) ∧
          ∀ p : FineFan.stalk F.space.presheaf (c.map.hom.base x),
            Algebra.GrothendieckGroup.of
                (FineFan.germ X.logStructure.zariskiPresheaf U x hx (h p)) =
              s (Algebra.GrothendieckGroup.of p) := by
  obtain ⟨L, e, he, hR, hP, hsharp, hfree⟩ := fan_chart_stalk_model c x
  obtain ⟨hsplit, hlift⟩ := monoid_sections_of_group_sections
    (c.stalkQuotient x) e he hR hfree
  refine ⟨L, hP, hsharp, hfree, hsplit, ?_⟩
  intro s hs
  obtain ⟨j, hj, hjs⟩ := hlift s hs
  have hj' : ∀ p, c.stalkQuotient x (j p) = p :=
    fun p ↦ DFunLike.congr_fun hj p
  obtain ⟨U, hx, h, a, hU, ha, hh, hgerm⟩ := fan_chart_germ_spreading c x L j hj'
  refine ⟨U, hx, h, a, hU, fan_chart_section_is_chart c x L hP U h a ha hh, ha, hh, ?_⟩
  intro p
  rw [hgerm, hjs]

end AlgebraicGeometry
