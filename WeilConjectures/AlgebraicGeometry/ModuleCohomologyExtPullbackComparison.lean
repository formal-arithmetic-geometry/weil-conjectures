/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison

/-! # Module and Ext cohomology comparisons compatible with scheme maps

## References

* [Stacks, Tags 03FD, 01FB and 01F7]
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules


/-- The module/Ext comparison can be normalized on both schemes so that
it intertwines the base-change unit h-map with exact abelian inverse image on Ext
(Stacks, Tags 03FD, 01FB and 01F7). -/
theorem exists_moduleCohomology_ext_pullback_comparison
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) (p : ℕ) :
    ∃ E : ∀ M : Y.Modules,
        ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj M) ≃+ H M p,
      ∃ E' : ∀ M : (baseChangedScheme (S := B) h).Modules,
        ((RingedSpace.moduleCohomology
          (baseChangedScheme (S := B) h).toRingedSpace p).obj M) ≃+ H M p,
        (∀ (M M' : Y.Modules) (φ : M ⟶ M')
          (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj M),
          E M' (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) =
            H.map φ p (E M x)) ∧
        (∀ (M M' : (baseChangedScheme (S := B) h).Modules) (φ : M ⟶ M')
          (x : (RingedSpace.moduleCohomology
            (baseChangedScheme (S := B) h).toRingedSpace p).obj M),
          E' M' (((RingedSpace.moduleCohomology
            (baseChangedScheme (S := B) h).toRingedSpace p).map φ).hom x) =
            H.map φ p (E' M x)) ∧
        (∀ (N : Y.Modules)
          (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj N),
          E' (baseChangedModule (S := B) h N)
            (moduleCohomologyFMap (baseChangeFst (S := B) h)
              (baseChangeUnit (S := B) h N) p x) =
            H.baseChangeLinear (S := B) h N p (E N x)) := by
  classical
  obtain ⟨E, E', hE, hE', hedge⟩ := exists_moduleCohomology_ext_edge_comparison
    (R := R) (B := B) (Y := Y) h p
  refine ⟨E, E', hE, hE', ?_⟩
  intro N x
  have hs := moduleCohomology_transport_coefficient
    (X := baseChangedScheme (S := B) h) (Y := Y)
    (baseChangeFst (S := B) h) N (baseChangedModule (S := B) h N)
    (baseChangeUnit (S := B) h N) p (fun M y ↦ E M y)
    (fun y ↦ E' (baseChangedModule (S := B) h N) y)
    (hE N _ (baseChangeUnit (S := B) h N)) (hedge (baseChangedModule (S := B) h N)) x
  dsimp only [H.baseChangeLinear, cohomologyComparisonLinear]
  exact hs

end AlgebraicGeometry.Scheme.Modules
