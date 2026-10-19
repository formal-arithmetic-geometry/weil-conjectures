/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-!
# Bounded derived smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1437
(blueprint: sbc-thm-bounded-derived-smooth-base-change); Stacks Project, Tags 0EYU and 0F09.

The exchange is the canonical module-coefficient exchange on the unbounded derived
categories, with the square's vertical and horizontal roles exchanged.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Smooth pullback commutes with derived direct image of bounded constructible complexes
with the prescribed finite coefficients. The conclusion is in the ambient unbounded
module derived category; it imposes no boundedness or constructibility on either endpoint.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1437; Stacks Project,
Tags 0EYU, 0F09, 015J, 0D6J and 07A7
(blueprint: sbc-thm-bounded-derived-smooth-base-change).

Proof:
1. The lower cohomological bound in bounded constructibility makes K an object of D+.
2. Every sheaf of Λ-modules is torsion of invertible order: N is positive, kills Λ,
   and is invertible on S. Apply the existing module-coefficient bounded-below smooth
   base-change theorem to all cohomology sheaves of K. Its proof uses sheaf smooth
   base change and triangulated truncation devissage.
3. The upstream comparison identifies the bounded-below and unbounded canonical
   module exchanges up to invertible endpoint comparisons. Their invertibility is
   therefore equivalent at K, giving the asserted unbounded exchange isomorphism. -/
theorem isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g) (N : ℕ)
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ T) (hK : DerivedCategory.isBoundedConstructible Λ T K) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K) := by
  obtain ⟨a, _, _, hbounds⟩ := hK.2
  have ha : K.IsGE a := (_root_.DerivedCategory.isGE_iff K a).2
    (fun q hq ↦ hbounds q (Or.inl hq))
  let Kplus : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K, ⟨a, ha⟩⟩
  apply (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ)
    sq.toCommSq.flip Kplus).2
  rw [← baseChange_eq_derivedBaseChangeMapPlus]
  exact isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ f
    (CategoryTheory.IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
      sq.hom_fst sq.hom_snd).flip Kplus (fun _ ↦
        Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N
          (Nat.ne_of_gt hcoeff.1) hcoeff.2.2.1 hcoeff.2.2.2 _)

end AlgebraicGeometry.Etale
