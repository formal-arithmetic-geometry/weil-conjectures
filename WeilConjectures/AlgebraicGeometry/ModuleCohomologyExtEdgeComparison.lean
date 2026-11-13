/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge

/-! # Module/Ext comparisons compatible with the direct-image edge map

## References

* [Stacks, Tags 03FD, 01FB and 01F7]
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- For the base-change projection f, comparisons can be chosen coherently
for the direct-image edge map (Stacks, Tags 03FD, 01FB and 01F7). -/
theorem exists_moduleCohomology_ext_edge_comparison
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
      (∀ (F : (baseChangedScheme (S := B) h).Modules)
        (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj
          ((pushforward (baseChangeFst (S := B) h)).obj F)),
        E' F (moduleCohomologyEdgeMap (baseChangeFst (S := B) h) F p x) =
          Sheaf.H.map (coeff (baseChangeFst (S := B) h)
            (𝟙 ((pushforward (baseChangeFst (S := B) h)).obj F))) p
            (Sheaf.H.mapFunctor (invImage (baseChangeFst (S := B) h))
              (constIso (baseChangeFst (S := B) h)).symm
              ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
                ((pushforward (baseChangeFst (S := B) h)).obj F)) p
              (E ((pushforward (baseChangeFst (S := B) h)).obj F) x))) := by
  refine ⟨fun M ↦ moduleCohomologyExtResolutionEquiv Y M p,
    fun M ↦ moduleCohomologyExtResolutionEquiv (baseChangedScheme (S := B) h) M p,
    ?_, ?_, ?_⟩
  · exact moduleCohomologyExtResolutionEquiv_naturality Y p
  · exact moduleCohomologyExtResolutionEquiv_naturality (baseChangedScheme (S := B) h) p
  · intro F x
    exact moduleCohomologyExtResolutionEquiv_edge (baseChangeFst (S := B) h) F p x

end AlgebraicGeometry.Scheme.Modules
