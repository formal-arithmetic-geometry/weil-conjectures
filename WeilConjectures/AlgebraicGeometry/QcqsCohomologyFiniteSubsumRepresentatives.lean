/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit
import WeilConjectures.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram
import WeilConjectures.Topology.ModuleCohomologyTopComparison
import Mathlib.AlgebraicGeometry.Properties

/-! # Finite-stage representatives for cohomology of a coproduct

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 09J7](https://stacks.math.columbia.edu/tag/09J7)
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

open Classical in
/-- Every cohomology class of a coproduct is the image of a class in a finite partial
biproduct. This asserts only existence of a finite-stage representative; it does not
identify the cohomology of that finite stage with a direct sum of cohomology modules. -/
theorem moduleCohomology_finiteSubsum_representative (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (_hS : IsColimit (Cofan.mk S ι)) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj S) :
    ∃ (J : Finset I)
      (y : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (⨁ (fun j : J ↦ F j))),
      ((RingedSpace.moduleCohomology X.toRingedSpace p).map
        (biproduct.desc (fun j : J ↦ ι j))).hom y = x := by
  obtain ⟨A, instPreorder, instNonempty, instDirected, D, τ, hc, hstage⟩ :=
    exists_small_finiteSubsum_diagram X I F S ι _hS
  obtain ⟨e⟩ := RingedSpace.nonempty_moduleCohomology_top_iso X.toRingedSpace p
  let H := RingedSpace.moduleCohomology X.toRingedSpace p
  obtain ⟨a, z, hz⟩ := (openModuleCohomology_directedColimit X
    PrespectralSpace.isTopologicalBasis D (Cocone.mk S τ) hc ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X))) p).1
      ((e.hom.app S).hom x)
  obtain ⟨J, b, hb⟩ := hstage a
  let w : H.obj (D.obj a) := (e.inv.app (D.obj a)).hom z
  have hw : (H.map (τ.app a)).hom w = x := by
    have hn := congrArg (fun f ↦ f.hom z) (e.inv.naturality (τ.app a))
    change (e.inv.app S).hom
      (((RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).map (τ.app a)).hom z) =
        (H.map (τ.app a)).hom w at hn
    rw [hz] at hn
    rw [← hn]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app S) x
  refine ⟨J, (H.map b.hom).hom w, ?_⟩
  have hbdesc : b.hom ≫ biproduct.desc (fun j : J ↦ ι j) = τ.app a := by
    have h : b.inv ≫ τ.app a = biproduct.desc (fun j : J ↦ ι j) := by
      apply biproduct.hom_ext'
      intro j
      simpa only [Category.assoc, biproduct.ι_desc] using hb j
    rw [← h, ← Category.assoc, b.hom_inv_id, Category.id_comp]
  change (H.map (biproduct.desc (fun j : J ↦ ι j))).hom ((H.map b.hom).hom w) = x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← H.map_comp, hbdesc]
  exact hw

end AlgebraicGeometry.Scheme
