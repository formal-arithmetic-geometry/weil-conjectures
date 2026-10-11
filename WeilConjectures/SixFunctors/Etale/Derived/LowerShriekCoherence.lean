/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.RefinementUniqueness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence

/-!

# Coherence of the compactification comparisons

Let `f : X ⟶ Y` be a morphism of schemes and let `r : c.Refinement d` be a refinement of
compactifications of `f`, with `u = r.hom : c.Z ⟶ d.Z`, whose square over `X` is cartesian
(this holds automatically when `c` is dense, by
`AlgebraicGeometry.Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`).
This file proves the coherence of the comparisons between the derived lower shrieks attached
to different compactifications (blueprint `sk-prop-sf-comp-coherence`):

* on `d.Z`, the canonical map `α_u : j_{d!} K ⟶ Ru_* j_{c!} K` is an isomorphism for torsion
  coefficients, it is the identity for the identity refinement and it is transitive under
  composition of refinements;
* consequently, the comparison `Rf_!(d) ⟶ Rf_!(c)` of the candidates
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`) is
  `R(d.g)_* α_u` followed by the composition isomorphism `R(d.g)_* Ru_* ≅ R(c.g)_*`;
* the isomorphism `Rf_!(c) ≅ Rf_!(d)` obtained from a common refinement does not depend on
  the chosen common refinement, and these isomorphisms satisfy the cocycle condition;
* for an arbitrary refinement `r`, not necessarily cartesian over `X`, the comparison
  `Rf_!(d) ≅ Rf_!(c)` is defined through the dense refinement `Compactification.inf c c ⟶ c`;
  it agrees with the one above for cartesian `r`, satisfies the identity and transitivity
  laws, and independence of the common refinement holds for arbitrary common refinements.

The comparison `α_u` on `d.Z` is only treated for refinements with cartesian square over `X`.

## Main definitions

- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison`: the comparison
  `α_u : D⁺(d.i)_! ⟶ D⁺(c.i)_! ⋙ R⁺u_*`.
- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekRestrictionIso`: the isomorphism
  `θ_u : (d.i)^* Ru_* (c.i)_! K ≅ K` of blueprint `rem-ptr-weil-pbc-proper-open-comparison-1`,
  whose inverse is adjoint to `α_u`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso`: the
  comparison `Rf_!(d) ≅ Rf_!(c)` along an arbitrary refinement.

## Main results

- `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_id` and
  `AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_comp`: the identity and
  transitivity of `α_u`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq`: independence
  of the common refinement.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans`: the cocycle
  condition.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`:
  independence of the common refinement, for arbitrary refinements.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_comp`:
  identity and transitivity for arbitrary refinements.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Compactification.Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A refinement out of the common refinement `Compactification.inf c d` of a quasi-compact
morphism has cartesian square over `X`, since `Compactification.inf c d` is dense. -/
theorem isPullback_of_inf [QuasiCompact f] {c d e : Compactification f}
    (r : (Compactification.inf c d).Refinement e) :
    IsPullback (Compactification.inf c d).i (𝟙 X) r.hom e.i := by
  have := Compactification.isSchemeTheoreticallyDominant_inf_i c d
  have : QuasiCompact (Compactification.inf c d).i :=
    (Compactification.inf c d).quasiCompact_openImmersion ‹_›
  exact r.isPullback_of_isSchemeTheoreticallyDominant

end Compactification.Refinement

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The comparison `α_u : j_{d!} K ⟶ Ru_* j_{c!} K` on bounded below derived categories
attached to a refinement `r : c.Refinement d`, with `u = r.hom`, whose square over `X` is
cartesian: the unit of `D⁺u^* ⊣ R⁺u_*` at `j_{d!} K` followed by `Ru_*` of the inverse of the
base change isomorphism `u^* j_{d!} ≅ j_{c!}`. (blueprint: `sk-prop-sf-comp-coherence`) -/
noncomputable def refinementOpenImmersionLowerShriekComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction A r.hom)
    (d.i)_!open[A].mapDerivedCategoryPlus ⟶
      (c.i)_!open[A].mapDerivedCategoryPlus ⋙ (r.hom)_*[A].rightDerivedFunctorPlus :=
  haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  Functor.whiskerLeft (d.i)_!open[A].mapDerivedCategoryPlus
      (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).inv
      (r.hom)_*[A].rightDerivedFunctorPlus

/-- The comparison of candidates `Rf_!(d) ⟶ Rf_!(c)` along a refinement is `R(d.g)_*` of the
comparison `α_u` of `refinementOpenImmersionLowerShriekComparison`, followed by the
composition isomorphism `Ru_* ⋙ R(d.g)_* ≅ R(c.g)_*`. (blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusComparison_eq
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction A r.hom)
    rightDerivedLowerShriekOfCompactificationPlusComparison A r hcart =
      Functor.whiskerRight (refinementOpenImmersionLowerShriekComparison A r hcart)
          (d.g)_*[A].rightDerivedFunctorPlus ≫
        Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[A] (d.g)_*[A]
            (refinementLowerStarComp A r)).hom := by
  ext K : 2
  simp [rightDerivedLowerShriekOfCompactificationPlusComparison,
    refinementOpenImmersionLowerShriekComparison]

/-- **Identity law for `α_u`**: for the identity refinement of `c`, the comparison
`α : j_{c!} ⟶ R(𝟙)_* j_{c!}` is the inverse of the identity isomorphism `R(𝟙)_* ≅ 𝟭`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem refinementOpenImmersionLowerShriekComparison_id
    (hcart : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i) :
    refinementOpenImmersionLowerShriekComparison A (Compactification.Refinement.id c) hcart =
      Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
        (lowerStarIdDerivedPlus A c.Z).inv := by
  ext W : 2
  have hB := NatTrans.congr_app (derivedPlus_unit_comp_upperStarIdDerivedPlus A c.Z)
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hBC := NatTrans.congr_app
    (refinementLowerShriekBaseChangeDerivedPlusIso_inv_id A c hcart) W
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hB
  simp only [refinementOpenImmersionLowerShriekComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [hBC, Functor.whiskerLeft_app]
  exact hB

/-- **Transitivity of `α_u`**: for refinements `r : c.Refinement d` and `s : d.Refinement e`
with cartesian squares over `X`, the comparison attached to `r.comp s` is the composite of
`α_s`, of `R(s.hom)_*` applied to `α_r` and of the composition isomorphism of the derived
pushforwards. (blueprint: `sk-prop-sf-comp-coherence`) -/
theorem refinementOpenImmersionLowerShriekComparison_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction A r.hom)
    refinementOpenImmersionLowerShriekComparison A (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs) =
      refinementOpenImmersionLowerShriekComparison A s hs ≫
        Functor.whiskerRight (refinementOpenImmersionLowerShriekComparison A r hr)
          (s.hom)_*[A].rightDerivedFunctorPlus ≫
        Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[A] (s.hom)_*[A]
            (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom := by
  have hI1 : (((r.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  have hI2 : (((s.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A s.hom)
  have hI : ((((r.comp s).hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (r.comp s).hom)
  ext W : 2
  have hBCinv := NatTrans.congr_app
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp A r s hr hs) W
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hBCinv
  have hstep2 := Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus A r.hom s.hom
    ((r.comp s).hom) rfl (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hnatXi := (Functor.rightDerivedFunctorPlusCompIso' ((r.hom)_*[A]) ((s.hom)_*[A])
      (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom.naturality
    (((r.hom)^*[A]).mapDerivedCategoryPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatXi
  have hnatEta1 := (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.naturality
    ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnatEta1
  have hinner : (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
        (((s.hom)^*[A]).mapDerivedCategoryPlus.obj
          (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)) ≫
      ((r.hom)_*[A]).rightDerivedFunctorPlus.map
        (((r.hom)^*[A]).mapDerivedCategoryPlus.map
            ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) =
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W ≫
        (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
          (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
        ((r.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) := by
    rw [Functor.map_comp, ← reassoc_of% hnatEta1]
  simp only [refinementOpenImmersionLowerShriekComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  rw [hBCinv, Functor.map_comp, ← Category.assoc, hstep2, Category.assoc, Category.assoc,
    ← hnatXi, ← Functor.map_comp_assoc, hinner, Functor.map_comp, Category.assoc,
    Functor.map_comp_assoc]

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The comparison `α_u` is an isomorphism** for torsion coefficients: this is
`isIso_derivedPlus_unit_app_openImmersionLowerShriek`, which rests on proper base change for
`u = r.hom`. (blueprint: `sk-prop-sf-comp-coherence`) -/
instance isIso_refinementOpenImmersionLowerShriekComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hcart) := by
  have : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction _ r.hom)
  have : ∀ K, IsIso ((Functor.whiskerLeft D+((d.i)_!open[ModuleCat.{u + 1} Λ])
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit).app K) :=
    fun K ↦ isIso_derivedPlus_unit_app_openImmersionLowerShriek Λ r hcart K
  have : IsIso (Functor.whiskerLeft D+((d.i)_!open[ModuleCat.{u + 1} Λ])
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit) :=
    NatIso.isIso_of_isIso_app _
  unfold refinementOpenImmersionLowerShriekComparison
  infer_instance

/-- The unit `K ⟶ (j^* j_!) K` of the bounded below derived adjunction `D⁺j_! ⊣ D⁺j^*` of an
open immersion `j` is an isomorphism: `D⁺j_!` is fully faithful, since the unbounded `Dj_!` is
and the bounded below derived categories are a full subcategory. -/
instance isIso_derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus_unit {Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).unit := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  have := adj.fullyFaithfulLOfIsIsoUnit.full
  have := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Full :=
    Functor.Full.of_iso ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
  have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Faithful :=
    Functor.Faithful.of_iso
      ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
  have : D+((j)_!open[ModuleCat.{u + 1} Λ]).Full :=
    Functor.Full.of_comp_faithful _ DerivedCategory.Plus.ι
  have : D+((j)_!open[ModuleCat.{u + 1} Λ]).Faithful :=
    Functor.Faithful.of_comp _ DerivedCategory.Plus.ι
  infer_instance

/-- The isomorphism `θ_u : (d.i)^* Ru_* (c.i)_! K ≅ K` of
blueprint `rem-ptr-weil-pbc-proper-open-comparison-1`, for a refinement `r : c.Refinement d`
with cartesian square over `X` and `u = r.hom`: the restriction to `X` of the inverse of the
isomorphism `α_u` of `refinementOpenImmersionLowerShriekComparison`, followed by the inverse of
the unit isomorphism `K ≅ (d.i)^* (d.i)_! K`. Its inverse is adjoint to `α_u`
(`homEquiv_refinementOpenImmersionLowerShriekComparison_app`). -/
noncomputable def refinementOpenImmersionLowerShriekRestrictionIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    haveI : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction _ r.hom)
    D+((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ (r.hom)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙
        D+((d.i)^*[ModuleCat.{u + 1} Λ]) ≅
      𝟭 _ :=
  haveI : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction _ r.hom)
  (Functor.isoWhiskerRight
      (asIso (refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hcart))
      D+((d.i)^*[ModuleCat.{u + 1} Λ])).symm ≪≫
    (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) d.i).unit).symm

/-- The comparison `α_u` is the adjoint, under `D⁺(d.i)_! ⊣ D⁺(d.i)^*`, of the inverse of
`θ_u = refinementOpenImmersionLowerShriekRestrictionIso`.
(blueprint: `rem-ptr-weil-pbc-proper-open-comparison-1`) -/
theorem homEquiv_refinementOpenImmersionLowerShriekComparison_app
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) d.i).homEquiv
        _ _ ((refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hcart).app K) =
      (refinementOpenImmersionLowerShriekRestrictionIso r Λ hcart).inv.app K := by
  simp [refinementOpenImmersionLowerShriekRestrictionIso, Adjunction.homEquiv_unit]

end Torsion

section Independence

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Comparing through a common refinement `e` of `c` and `d` gives the same isomorphism
`Rf_!(c) ≅ Rf_!(d)` as comparing through any further refinement of `e`. -/
lemma rightDerivedLowerShriekOfCompactificationPlusComparison_trans_eq_of_refinement
    {c d e e' : Compactification f} (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i)
    (t : e'.Refinement e) (ht : IsPullback e'.i (𝟙 X) t.hom e.i) :
    asIso (rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ) r hr) ≪≫
        (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ s hs)).symm =
      asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ (t.comp r)
          (Compactification.Refinement.isPullback_comp t r ht hr)) ≪≫
        (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ (t.comp s)
          (Compactification.Refinement.isPullback_comp t s ht hs))).symm := by
  have h : ∀ {c' : Compactification f} (r' : e.Refinement c')
      (hr' : IsPullback e.i (𝟙 X) r'.hom c'.i),
      asIso (rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ)
          (t.comp r') (Compactification.Refinement.isPullback_comp t r' ht hr')) =
        asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ r' hr') ≪≫
          asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ t ht) := by
    intro c' r' hr'
    ext : 1
    exact rightDerivedLowerShriekOfCompactificationPlusComparison_comp _ t r' ht hr'
  rw [h r hr, h s hs]
  ext : 1
  simp

/-- Equal refinements give equal comparisons. -/
lemma asIso_rightDerivedLowerShriekOfCompactificationPlusComparison_congr
    {c d : Compactification f} {r r' : c.Refinement d} (h : r = r')
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hr' : IsPullback c.i (𝟙 X) r'.hom d.i) :
    asIso (rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ) r hr) =
      asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ r' hr') := by
  subst h
  rfl

variable [QuasiCompact f]

/-- **Independence of the common refinement**: for any common refinement `e` of two
compactifications `c` and `d` of `f`, with refinements `r : e.Refinement c` and
`s : e.Refinement d` whose squares over `X` are cartesian, the isomorphism
`Rf_!(c) ≅ Rf_!(d)` obtained by comparing both with `e` is
`rightDerivedLowerShriekOfCompactificationPlusIso`, the one obtained through the common
refinement `Compactification.inf c d`. The proof compares both with the dense common refinement
`Compactification.inf e (Compactification.inf c d)`, out of which refinements are unique.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusIso_eq
    {c d e : Compactification f} (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i) :
    rightDerivedLowerShriekOfCompactificationPlusIso Λ c d =
      asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ r hr) ≪≫
        (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ s hs)).symm := by
  set e' := Compactification.inf c d
  set e'' := Compactification.inf e e'
  have hdense := Compactification.isSchemeTheoreticallyDominant_inf_i e e'
  rw [rightDerivedLowerShriekOfCompactificationPlusIso,
    rightDerivedLowerShriekOfCompactificationPlusComparison_trans_eq_of_refinement Λ r s hr hs
      (Compactification.infFst e e') (Compactification.isPullback_infFst e e'),
    rightDerivedLowerShriekOfCompactificationPlusComparison_trans_eq_of_refinement Λ _ _
      (Compactification.isPullback_infFst c d) (Compactification.isPullback_infSnd c d)
      (Compactification.infSnd e e') (Compactification.isPullback_infSnd e e'),
    asIso_rightDerivedLowerShriekOfCompactificationPlusComparison_congr Λ
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infFst c d))
        ((Compactification.infFst e e').comp r)),
    asIso_rightDerivedLowerShriekOfCompactificationPlusComparison_congr Λ
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infSnd c d))
        ((Compactification.infFst e e').comp s))]

/-- For a refinement `r : c.Refinement d` whose square over `X` is cartesian, the isomorphism
`Rf_!(c) ≅ Rf_!(d)` is the inverse of the comparison along `r`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusIso_eq_symm {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    rightDerivedLowerShriekOfCompactificationPlusIso Λ c d =
      (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _ r hr)).symm := by
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i := by
    rw [Compactification.Refinement.id_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ (Compactification.Refinement.id c) r
    hid hr]
  ext : 1
  simp [rightDerivedLowerShriekOfCompactificationPlusComparison_id]

/-- The isomorphism `Rf_!(c) ≅ Rf_!(c)` is the identity. (blueprint: `sk-prop-sf-comp-coherence`)
-/
@[simp]
theorem rightDerivedLowerShriekOfCompactificationPlusIso_refl (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusIso Λ c c = Iso.refl _ := by
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ (Compactification.infFst c c)
    (Compactification.infFst c c) (Compactification.isPullback_infFst c c)
    (Compactification.isPullback_infFst c c)]
  ext : 1
  simp

/-- **The cocycle condition**: for three compactifications `c₁`, `c₂`, `c₃` of `f`, the
isomorphisms `Rf_!(c₁) ≅ Rf_!(c₂) ≅ Rf_!(c₃)` compose to `Rf_!(c₁) ≅ Rf_!(c₃)`. The proof
compares all three with one common refinement.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusIso_trans (c₁ c₂ c₃ : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusIso Λ c₁ c₂ ≪≫
        rightDerivedLowerShriekOfCompactificationPlusIso Λ c₂ c₃ =
      rightDerivedLowerShriekOfCompactificationPlusIso Λ c₁ c₃ := by
  set e₁₂ := Compactification.inf c₁ c₂
  set e := Compactification.inf e₁₂ c₃
  have h₁ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infFst c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infFst c₁ c₂)
  have h₂ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infSnd c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infSnd c₁ c₂)
  have h₃ := Compactification.isPullback_infSnd e₁₂ c₃
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ _ _ h₁ h₂,
    rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ _ _ h₂ h₃,
    rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ _ _ h₁ h₃]
  ext : 1
  simp

/-- The isomorphism `Rf_!(d) ≅ Rf_!(c)` is the inverse of `Rf_!(c) ≅ Rf_!(d)`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusIso_symm (c d : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationPlusIso Λ c d).symm =
      rightDerivedLowerShriekOfCompactificationPlusIso Λ d c := by
  have h := rightDerivedLowerShriekOfCompactificationPlusIso_trans Λ c d c
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_refl] at h
  ext : 1
  rw [Iso.symm_hom, ← cancel_epi (rightDerivedLowerShriekOfCompactificationPlusIso Λ c d).hom,
    Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm


/-! ### Arbitrary refinements

A refinement `r : c.Refinement d` need not have a cartesian square over `X`. The comparison
along `r` is then defined through the dense refinement `v : Compactification.inf c c ⟶ c`:
both `v` and `v.comp r` have cartesian squares, since they come out of a dense
compactification, and the comparison along `r` is `ρ_{v.comp r} ≫ ρ_v⁻¹`. It agrees with
`ρ_r` when the square of `r` is cartesian, and it satisfies the identity and transitivity laws
and independence of the common refinement for arbitrary refinements. -/

/-- The comparison `Rf_!(d) ≅ Rf_!(c)` along an arbitrary refinement `r : c.Refinement d`:
the comparison along `v.comp r` followed by the inverse of the comparison along `v`, for the
dense refinement `v = Compactification.infFst c c` of `c`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusRefinementIso
    (r : c.Refinement d) :
    Rf_!(d)[ModuleCat.{u + 1} Λ]+ ≅ Rf_!(c)[ModuleCat.{u + 1} Λ]+ :=
  asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _
      ((Compactification.infFst c c).comp r)
      (Compactification.Refinement.isPullback_of_inf _)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _
      (Compactification.infFst c c) (Compactification.isPullback_infFst c c))).symm

/-- Along a refinement whose square over `X` is cartesian, the comparison
`rightDerivedLowerShriekOfCompactificationPlusRefinementIso` is
`rightDerivedLowerShriekOfCompactificationPlusComparison`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusRefinementIso_hom (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r).hom =
      rightDerivedLowerShriekOfCompactificationPlusComparison _ r hr := by
  simp [rightDerivedLowerShriekOfCompactificationPlusRefinementIso,
    rightDerivedLowerShriekOfCompactificationPlusComparison_comp _
      (Compactification.infFst c c) r (Compactification.isPullback_infFst c c) hr]

/-- **Independence of the common refinement, for arbitrary refinements**: for any common
refinement `e` of `c` and `d`, with arbitrary refinements `r : e.Refinement c` and
`s : e.Refinement d`, the isomorphism `Rf_!(c) ≅ Rf_!(d)` obtained by comparing both with `e`
is `rightDerivedLowerShriekOfCompactificationPlusIso`.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso
    {c d e : Compactification f} (r : e.Refinement c) (s : e.Refinement d) :
    rightDerivedLowerShriekOfCompactificationPlusIso Λ c d =
      rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r ≪≫
        (rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ s).symm := by
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_eq Λ
    ((Compactification.infFst e e).comp r) ((Compactification.infFst e e).comp s)
    (Compactification.Refinement.isPullback_of_inf _)
    (Compactification.Refinement.isPullback_of_inf _)]
  ext : 1
  simp [rightDerivedLowerShriekOfCompactificationPlusRefinementIso]

/-- **Identity law for arbitrary refinements**: the comparison along the identity refinement
is the identity. (blueprint: `sk-prop-sf-comp-coherence`) -/
@[simp]
theorem rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ
      (Compactification.Refinement.id c) = Iso.refl _ := by
  rw [rightDerivedLowerShriekOfCompactificationPlusRefinementIso,
    asIso_rightDerivedLowerShriekOfCompactificationPlusComparison_congr Λ
      (Compactification.Refinement.comp_id (Compactification.infFst c c)) _
      (Compactification.isPullback_infFst c c)]
  ext : 1
  simp

/-- The comparison along an arbitrary refinement `r : c.Refinement d` is the inverse of the
isomorphism `Rf_!(c) ≅ Rf_!(d)`. (blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq (r : c.Refinement d) :
    rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r =
      (rightDerivedLowerShriekOfCompactificationPlusIso Λ c d).symm := by
  rw [rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso Λ
    (Compactification.Refinement.id c) r]
  ext : 1
  simp

/-- **Transitivity for arbitrary refinements**: the comparison along a composite `r.comp s`
of refinements is the composite of the two comparisons, in reverse order.
(blueprint: `sk-prop-sf-comp-coherence`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusRefinementIso_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ (r.comp s) =
      rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ s ≪≫
        rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r := by
  simp only [rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq,
    ← Iso.trans_symm, rightDerivedLowerShriekOfCompactificationPlusIso_trans]

end Independence

end Etale

end AlgebraicGeometry

/-! ### Axiom census

The transitivity of `α_u` depends only on the three standard axioms; the check below is run by
the build. The statements involving the inverse of a comparison use that `α_u` is an
isomorphism, which rests on proper base change
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`, blueprint
`sk-thm-properbasechange`), not proved yet. -/

/--
info: 'AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_comp' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison_comp

