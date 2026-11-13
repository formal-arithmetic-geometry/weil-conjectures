/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Representing affine perfect derived arrows by chain maps

## References

* Stacks Project, Tag 08CR (second proof); Tag 06Z0 (affine derived equivalence).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived arrow between strictly perfect complexes on an affine open is represented by
an actual chain map (Stacks, Tags 08CR and 06Z0). -/
theorem perfect_affine_map_representative (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hU : IsAffineOpen U)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (f : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    ∃ α : A ⟶ B, DerivedCategory.Q.map α = f := by
  let R := X.presheaf.obj (.op U)
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let F := (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)
  obtain ⟨P, hP, ⟨eA⟩⟩ := affine_perfect_module_model X U hU A hA
  obtain ⟨T, _, ⟨eB⟩⟩ := affine_perfect_module_model X U hU B hB
  have : P.IsKProjective := hP
  obtain ⟨G, hG, ⟨c⟩⟩ := affine_localized_derived_sheafification X U hU
  have : G.Full := hG
  let a := c.app P ≪≫ DerivedCategory.Q.mapIso eA
  let b := c.app T ≪≫ DerivedCategory.Q.mapIso eB
  let g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj T :=
    G.preimage (a.hom ≫ f ≫ b.inv)
  obtain ⟨β, hβ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P T g
  refine ⟨eA.inv ≫ F.map β ≫ eB.hom, ?_⟩
  have hc := c.hom.naturality β
  change G.map (DerivedCategory.Q.map β) ≫ (c.app T).hom =
    (c.app P).hom ≫ DerivedCategory.Q.map (F.map β) at hc
  rw [hβ] at hc
  have hg : G.map g = a.hom ≫ f ≫ b.inv := G.map_preimage _
  rw [hg] at hc
  have hc' : DerivedCategory.Q.map (F.map β) =
      (c.app P).inv ≫ a.hom ≫ f ≫ b.inv ≫ (c.app T).hom := by
    calc
      _ = (c.app P).inv ≫ ((c.app P).hom ≫
          DerivedCategory.Q.map (F.map β)) := by simp
      _ = _ := by rw [← hc]; simp only [Category.assoc]
  simp only [Functor.map_comp, hc', Category.assoc]
  dsimp [a, b]
  simp


end AlgebraicGeometry.Scheme
