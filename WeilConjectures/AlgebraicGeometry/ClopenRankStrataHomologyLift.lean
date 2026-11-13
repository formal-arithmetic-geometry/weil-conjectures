/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ClopenRankStratumDerivedProjector

/-! # Lifting a map from one clopen rank stratum

Source: rank-idempotent splitting and single-degree truncation in steps 1--2
of clopen rank-stratum formality (the expansion of the reconstruction argument
motivated by Stacks Tag 0BQZ). Supporting sources: Stacks Tags 00EE
(clopen idempotents), 0118 (canonical truncation), and 0AVW (algebra setup).
-/

@[expose] public section

universe u wA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

private theorem lift_to_concentrated
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (L : DerivedCategory C) (n : ℤ)
    (hL : ∀ m : ℤ, m ≠ n → IsZero ((DerivedCategory.homologyFunctor C m).obj L))
    (M : C) (a : M ⟶ (DerivedCategory.homologyFunctor C n).obj L) :
    ∃ f : (DerivedCategory.singleFunctor C n).obj M ⟶ L,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app M ≫
        (DerivedCategory.homologyFunctor C n).map f = a := by
  have : L.IsGE n := (DerivedCategory.isGE_iff L n).mpr fun m hm ↦ hL m (ne_of_lt hm)
  have : L.IsLE n := (DerivedCategory.isLE_iff L n).mpr fun m hm ↦ hL m (ne_of_gt hm)
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L n
  let H := DerivedCategory.homologyFunctor C n
  let S := DerivedCategory.singleFunctor C n
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso C n
  let b : M ⟶ N := a ≫ H.map e.hom ≫ ε.hom.app N
  refine ⟨S.map b ≫ e.inv, ?_⟩
  change ε.inv.app M ≫ H.map (S.map b ≫ e.inv) = a
  rw [Functor.map_comp, ← Category.assoc]
  rw [show ε.inv.app M ≫ H.map (S.map b) = b ≫ ε.inv.app N from (ε.inv.naturality b).symm]
  dsimp only [b]
  simp only [Category.assoc, ε.hom_inv_id_app]
  change a ≫ H.map e.hom ≫ 𝟙 (H.obj (S.obj N)) ≫ H.map e.inv = a
  rw [Category.id_comp, ← H.map_comp, e.hom_inv_id, H.map_id, Category.comp_id]

/-- The rank-stratum projector gives a concentrated retract of `K`, and maps
from the module on that stratum are fixed by the induced homology projector.
The whole object `K` need not be concentrated.

Source: rank-idempotent splitting, steps 1--2 of clopen rank-stratum formality;
Stacks Tag 00EE for the characteristic idempotent and Tag 08J5 for the
single-degree presentation of the resulting retract. -/
theorem clopenRankStrata_homology_presentation
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T m))) :
    ∃ (L : DerivedCategory
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
      (ι : L ⟶ K) (π : K ⟶ L),
      ι ≫ π = 𝟙 L ∧
      (∀ m : ℤ, m ≠ n → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj L)) ∧
      (∀ a : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n) ⟶
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K,
        a ≫ (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map π ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map ι = a) := by
  let C := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))
  let g := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  by_cases hn : 0 ≤ n
  · obtain ⟨L, ι, π, hsplit, hdisjoint, hfixed⟩ :=
      clopenRankStratum_derived_projector i r n.toNat K
    have hL : ∀ m : ℤ, m ≠ n → IsZero ((DerivedCategory.homologyFunctor C m).obj L) := by
      intro m hmn
      obtain ⟨em⟩ := hother m hmn
      by_cases hm : 0 ≤ m
      · apply hdisjoint m m.toNat (E m.toNat)
        · omega
        · exact ⟨em ≪≫ eqToIso (congrArg g.obj ((hT m).trans (ite_eq_left hm)))⟩
      · have hTm : T m = 0 := (hT m).trans (ite_eq_right hm)
        have hK : IsZero ((DerivedCategory.homologyFunctor C m).obj K) :=
          (g.map_isZero (hTm ▸ isZero_zero _)).of_iso em
        apply (IsZero.iff_id_eq_zero _).mpr
        have hs := congrArg (DerivedCategory.homologyFunctor C m).map hsplit
        rw [Functor.map_comp, CategoryTheory.Functor.map_id] at hs
        rw [← hs, hK.eq_zero_of_tgt ((DerivedCategory.homologyFunctor C m).map ι),
          zero_comp]
    have hTn : T n =
        (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
          (E n.toNat) := (hT n).trans (ite_eq_left hn)
    have hfix : ∀ b : g.obj (T n) ⟶ (DerivedCategory.homologyFunctor C n).obj K,
        b ≫ (DerivedCategory.homologyFunctor C n).map π ≫
          (DerivedCategory.homologyFunctor C n).map ι = b := by
      rw [hTn]
      exact hfixed n (E n.toNat)
    exact ⟨L, ι, π, hsplit, hL, hfix⟩
  · have hTn : T n = 0 := (hT n).trans (ite_eq_right hn)
    have hM : IsZero (g.obj (T n)) := g.map_isZero (hTn ▸ isZero_zero _)
    refine ⟨0, 0, 0, ?_, ?_, ?_⟩
    · exact (isZero_zero _).eq_of_tgt _ _
    · intro m _
      exact (DerivedCategory.homologyFunctor C m).map_isZero (isZero_zero _)
    · intro a
      exact hM.eq_of_src _ _

/-- A module in degree n supported on its clopen rank stratum maps into a
complex through its degree-n homology, provided all other homology degrees
are supported on their respective different rank strata. The degree-n
homology need not be prescribed, and the map need not be an isomorphism.
No finite-image assumption on the rank function is needed for this one-stratum
lifting statement.

Source: rank-idempotent splitting and single-degree truncation, steps 1--2
of `lem-sc-clopen-rank-strata-formality` (expanding the reconstruction argument
motivated by Tag 0BQZ); Stacks Tags 00EE (clopen idempotents), 0118
(canonical truncation), and 0AVW (direct-image algebra setup).
The rank-stratum expansion is given here, not stated verbatim in 0BQZ. -/
theorem clopenRankStrata_homology_lift
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) m).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T m)))
    (a : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K) :
    ∃ f : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
          ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n)) ⟶ K,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).inv.app
          ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n)) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).map f = a := by
  obtain ⟨L, ι, π, _, hL, hfixed⟩ :=
    clopenRankStrata_homology_presentation i r E T hT K n hother
  obtain ⟨f, hf⟩ := lift_to_concentrated L n hL _
    (a ≫ (DerivedCategory.homologyFunctor _ n).map π)
  refine ⟨f ≫ ι, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hf, Category.assoc]
  exact hfixed a

end AlgebraicGeometry
