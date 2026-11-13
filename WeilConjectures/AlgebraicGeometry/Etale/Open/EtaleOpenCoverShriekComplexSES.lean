/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekNaturalSES

/-! # The termwise extension-by-zero short exact sequence
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The short exact complex before passage to the derived category. -/
theorem exists_shortExact_openCover_lowerShriek_complex
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    let E (T : X.Opens) :=
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
    ∃ (α : E (U ⊓ V) ⟶ E U ⊞ E V) (β : E U ⊞ E V ⟶ L) (hz : α ≫ β = 0),
      (ShortComplex.mk α β hz).ShortExact := by
  obtain ⟨tU, tV, hS⟩ := exists_natural_shortExact_openCover_lowerShriek Λ U V hcover
  let E (T : X.Opens) :=
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
  let iU : E (U ⊓ V) ⟶ E U :=
    { f := fun n ↦ tU.app (L.X n)
      comm' := fun i j _ ↦ (tU.naturality (L.d i j)).symm }
  let iV : E (U ⊓ V) ⟶ E V :=
    { f := fun n ↦ tV.app (L.X n)
      comm' := fun i j _ ↦ (tV.naturality (L.d i j)).symm }
  let ε (T : X.Opens) : E T ⟶ L :=
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app L
  have hz : biprod.lift iU (-iV) ≫ biprod.desc (ε U) (ε V) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (biprod.lift iU (-iV) ≫ biprod.desc (ε U) (ε V)).f n = 0
    rw [biprod.lift_desc]
    change tU.app (L.X n) ≫ _ + (-(tV.app (L.X n))) ≫ _ = 0
    simpa only [biprod.lift_desc, ε,
      Adjunction.mapHomologicalComplex_counit_app_f] using (hS (L.X n)).choose
  refine ⟨biprod.lift iU (-iV), biprod.desc (ε U) (ε V), hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨hzn, hn⟩ := hS (L.X n)
  let Q := HomologicalComplex.eval
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ) n
  let e := Q.mapBiprod (E U) (E V)
  apply ShortComplex.shortExact_of_iso _ hn
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · change Q.map (biprod.lift iU (-iV)) =
      biprod.lift (Q.map iU) (-(Q.map iV)) ≫ e.inv
    simpa only [Functor.map_neg] using
      (biprod.lift_mapBiprod Q (E U) (E V) iU (-iV)).symm
  · change e.inv ≫ Q.map (biprod.desc (ε U) (ε V)) =
      biprod.desc (Q.map (ε U)) (Q.map (ε V))
    exact biprod.mapBiprod_inv_map_desc Q (E U) (E V) (ε U) (ε V)

end AlgebraicGeometry.Etale
